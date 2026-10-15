-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3814
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:45:34.730649+00:00
-- url     : https://prove2.me/submissions/2089a760-1c78-40d0-b95f-5eb57f227bda

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 685791366 ≤ n < 685971223 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 685792616 1250 685791366 685791371
    0xc0303160c061d0705030703080306040c05040911091c050a0204020f090a0b03040302070803130306110702040c03090b010b070b0a0902030708030d09050106060318060507051605010f050f06100e0d0f06 88
    0x229514103040001c1c4c4050300c03040e030080ca0102d086880e050f9107070200070300941c03080742c85501c0844490301c148151001440292014018401600c4404140d40c0080304110b01a08000340c403420543d0109074010320458002026007542c11651302404040c0d4042c44801d150f1420805c610015a26220700003401021000c403070780c1d104c0c102032070003c0c10589507030310244141d403043c0300043c403d41c04070081104031390340003000103051240c07a1950382d214083c030365010394450300d001e001c10802601034100080030780c07043ca5010040ea807146000103050041c0c0c040030309101081c40028440048692014508500003011540e0507540d51050610b1580030b0911102001d440322403803010002c0901522020b00001e050174810a6813030301d542c0401115074000900140e44840200710900e010b0000c0700c618440d00303140c084440c006410b029001c0c2900300c4105c04082c2c500340c001100c5080c2a0f40042c0174900046c04040840e080000440703041c40b90058095120101d91880c8000805075002161942d04c9144007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 685793866 1250 685792616 685792661
    0xa0206061002150c030717010e041505070c030305060604030b13110f090601031e0c0203040609140109120309050301020304111924030e030a091a0c0303160c06 70
    0x6001680111048607429980b082c00340d40c0c0116003010031954024800c00302561030b503403810002c403041500f07000d0868040248400101d440a50001c103a8030641c090840340c1d941d06004216542100c0c005c50340c003030014003403031031401c0001e03c2908480e40148004042d241015141d49076045001c9060710001100c0d1543d510001c01c01041524924903513000300c1314005030103110808100205030090030b9604060381c404030310040c40080f9200e00700b0801008400c100e07418010700041d58079413040c0255004141030707000c0002d041d2040e8171100c0f03c0440607912440800d1030801c05034032000300d0306011001d1028012000c90307162400d00c061341c0b180b400355111680114020080c010900c3c110031aa41d202100b0110a10004160012f030070b01c541c0c8085548181000e0103107088004052102d403036038250200050200066902c110124140c44602e0b00400041c0808619008907119910b08001075401c184001003183d446000c00f0004441c60303061103603565120341d40e0402100c5606008800700b02c2d0301c012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 685795116 1250 685793866 685793869
    0x202e031401060f120908070602160b011e09020f0403081c09061401080a050a0224030c0301030b0c04140d031b060905060916050409081b03180f100e150a020606 70
    0x1596109460300744080085c1801e41d102c0701c18034402c0300000307840315030006140741e594034070010440e82c402e4106070800c4003947c50b100310a025840280d44810f08808031000480c90810501c01c4510709044440180d28144c510303640d0302903d420400c44076201007005504801e90f407125010b00e0450038441c1c0d40026041030360f246004500001a0000c00007580900844070002d03500007105c50f0960b80485100868005940201c452403e1100311242010b60210074445030801c101d0166040e284030310140701495a906d80c940304240524403810031840315450f10082c5a00300176041c0854540280303048418030018050704001c5c28030750041114203666804542d802e10005001003500444003c01401c00000d03940503411109029004545c8507a95074542401040250400c0300d18080038800c1c03d814110a9987d003580701d03040700d10302c2001700c06500c00c001c80c0ca1400030300d40c0d1070401000700040034400c00385508075409402001c0c0c0030342100350340b14207030f45141d121005810302000590040402e454042e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 685796366 1250 685795116 685795127
    0xf08070c0b1e030412200714030f01050610030c1803110103051b0d020c010f050f0a0b01170a0b011202181801030507060f0507020409202e031401060f 66
    0x25107030b40c40c12100f403062000084401007460342c014590b2500702128000c4e00704c00700c10f040c01568003007030b203100312400054030910780c1a14035800c00c001c07425103480c0ea203044500303402d03a4012100d060f0310100c003d610b4150140aa8000c444908051411402280442418940003aa103820039156120040400c0101c5d40e8140603040d404841c0d1f07102c0100d01503510108445a004502c3c611210940118030341c4c04c0c4480035404103182400d426800e03c085d0800e07000c82040c100b400e9485520300c0c1c1c00c00c2e0504d00b1650140d07049070907600509075404441d43e101c0490070010140c49006a0410140f5900c044000090703001801a080a441001c207508240000f00408215100001d07400340e030100c3e0041010510100f6802c04443c03460825042c04008207508072010311500c04001c0d8010300c1c000f9400207100001d103481c1401000c200740001000851010801c110a09038032486085c00c00310352031000040c850300b03090300303000840c00c02148008089180180245090304402c00003281400000c2c191503000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 685797616 1250 685796366 685796407
    0xf1b030f05061b0a050f16030804051002090918150117071e030605090a150b1005120403201c0201060609030309050918010924180f08070c0b 62
    0x2103030018128507242d0144545409120a1902445000700d1480701d0a00404216180070000404d43c0c01c002500e440c01608609c81603905a4440c4642c1c0c0e000035103003420b80b00301c07400758900030803500580d60341d130001c6a4840c1c8005240b250900503c0b507551038021040300480c0c082c041c50903c10500d0b9440b00101403500100782c0c0000303204200c09541c03d01c10403070084034606481e000040031442d5607917405042d1030040c0c032100c020114038540ca42002225103a51004411446c11a40302240c3c44003007404031018010092501480d0264001180010f80286420340501c00900814510010710b040510705186900c000700501c0065440004180c03982842008040d00d500c0c1451428a800d64030b000b0724503030300c502070607020310300f041c001c500091041c555420310320311701030001e101c0b4203c145440c08074030f01d00f182103030303060000c19045144030203440c00381310700c2030910000c0c0c0300c044815502c418041c0c0c010080241c3d5106410041d002c0820002c1d00b804018028803031f522a82c1e05e0310f880500c0d01c0c074040c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 685798866 1250 685797616 685797631
    0xb04050a02010e0114040b0d06180f0515010509040507031e050a0c110a060203091207050c0306010506190827070305071d18010f0e010b0a0b03040305070f1b030f0506 73
    0x74440038001d14100580303007618215541d0580754903403250380b032004000f1504203040102401c0704090088100b40c00501d4010780c803110500330b030340322a04500700074003000c020240868000c1c840c00495003041e0744960782c011640e01c0d000c17404401c5c880d040e00c00d488844042102e620386460401040704164001c0280340391280c50712900f6000000502d546842c10403000418040c5c0000100d43d03004420013a54141d0908017050f80e0341d80300e02c2e24240b80e44070303c694105e500a000d0320000003400c0c5001400d945900b44095030f2420160660041190f1503d4000e01220104c0d00b610b51190000d08449817040200300344000425115045061041c81d000d01c0307038411140d488049640d580d1062542034100e41240047c00c2481a150701000c0c220f01500300140b0b140c0d5a149440c50708146424150010406a0740945550440c1900c8a0800145200444001d40170820130464032001524040700d0400c0f01d0b01a140c6544450035114000000141580c070580d030568000e1580700600009000d55600a1031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 685800116 1250 685798866 685798877
    0xb04061818050307080304030c05061602010b0307030312020f160b0403110a030203161e151a06041e0b12190b0f100c1e050c030312011802070b04050a02010e01 70
    0x51a65070280e807840ba904c00240b0080e00800440c1c20907008201141c11258408241d40b028602000030400c000d4506035000c1c015820f080d802d11135400d010981a041c1e1fa00741e030300c40f091204010341d080060341c014200000301240800150014644800c40440c3c454812a0700076400d0a0a003401001d4006018030013003e0780101d001c4000280c0c0010440d00d4910002030100b000300014200303070000500d5030300340e9510030304a000d1040030001500d12502d81000c9855040114032402e006180c10402900c01481e04030104000038005000f1352041e01528056950509450944030b80756610344d42c020402e04000001000c041c80010700243e610701034000b0110714100002598000002d692000c0b0308065405401545441150035204070716203046150000b0304445903002c615090940510704080a07180c40c058150058034901d00402203542005003082064401d9082a2000303c451401034003181d501c5500300302c9040001d0085800b00e20039400754018003400607850001410001d82c203c1010304022 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 685801366 1250 685800116 685800161
    0x706060305060c040e0417040504050703051b0c1e01020906040608070f050c0d0f0318032601030b0f37050609010515071b0308030106030c08010f06120b040618 70
    0x300d412521766001c0e400070507002042d812071182082070300c120b40009802c141001c042001141e0184c002c030380616000c075420f80365001b056a01c0c4035280203100102c1d110b41c000911540d000d15288440341e420f060b01200040c40c20081c4d90002d1980d0380a0740c45400441c0c2036404010440c0c2e003049000c4803100083c20201c1c90103010000e100c0d107408900c40900f0a00c0441080c8403100d0b8402d501069134408804104507401809050161034600d07940b100744000380c0ca9001c03900340700c1032800115040326800001401c81d600c1e007035403064200300014003c5042c0b08099030341202d03094900e1a071000603140c252480740b100ca401d00581007a81e00043c02d2500512001004000c1d0362900b48010f00c181c2d20190207035413901402c1c5040b0004c46012111170355000740040c40801440302c0880114126085a1030400002207060b0042d12003000910032100c41e8075455400b008140d010f140070000710f00e03540c86c0010b0744240790800a404c40300243c0214244207001c02032140841a54410b0440f0321890510303400e00d24 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 685802616 1250 685801366 685801379
    0x10e0d0f020445021309030c0c08030d0f1404031d060a090602010e0c060a03090c090c080105090f01050d0b07120e031b0303090c120a080a033303080a140706060305060c04 75
    0x117052100c841044183c1e02c2622805052041900c90000340e032200f00360703c00b540e0300d4101c40d03a00e0304008038903000382d03250a40d8800f42d50104e200341d0942e83e812030440ca00700d54032500c003920301c440056204c0301e0746002880782d8542a5102001030130030324460f0301c1d00c1070b1950070480000d003142c5403132803060096030090f601400c03203503503400980d80140042c0c6404100d06410703140441d024078140d406a4004c5007040f06003030131160003200d018103841c4150713203e040e980e0303480c5d01d20281d000080c030440c0d41116100041da0041904000c0541d4042c2c15400c000c80340c181a40f0044003250200342005100c2c1d0004102054140c52003030b034681c0802a508011421400c200b560070740c448482c500301c0e034407540241c056101181014042c003032186410407005070b1030716107210001c5e000c1d00000725090011010032100c070000c098028503030b840d512814014801c039281541e581e103150364040328840f014401e16a6901c08450010300042400c0380c401d503004601c4a10b54903109c3d181c8203014082d1007816030240402d1108 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 685803866 1250 685802616 685802629
    0x17072907020a080d0b0d080a082211010e1009080708070803031602240106030501230405180f03190201110f0f07061118010e0d0f02044502 61
    0x1242c1c100f200705585003121010b400040200c0e9180304d80049540040c102401841000f030b181500058071000565500c1442444c1284d10202000c41d412010325503800c0840d50242100c5480c1c5010704084c1c046680040001b114200e04007848000110340181c02d014482c000d00c9000001c081410040c1105803c0000c25520303400010110444501c121303c580010510030001700d40c2c4080d289100b601c410b116100c0d00d20342d0240074002d59012a0400700002202040790000a1440d01584443d10700007006000300005018081c04058080b000d2103644c2079030130300901c0903445210800340296502c07418611119a50068024164256490900903414848062049841c05983c003131a059a0f0304544428801c10b0144601c0035010a180c2103446085000c60402040135106141c80592030001307507401151707084204124540c001c006c040352400000e88d04000d01406074030042022a0b5440640c00c009119059800400317145404003c5920410101c080041910386200040b4004004980c000c1620b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 685805116 1250 685803866 685803883
    0x50a14070c06150308270a0e01030b07090333020909010b16060203072a080d1104030f05030a120501080c0915090109200412060203041707290702 64
    0x300a4443e500c011001040a0401001e035500401103915a220030000c1c1210103440156851308034600031031010186030010302d41044481e00c0c020442c45030700b550399000708100c000e4218800d11120701c0c2c01000065042d10410007001040d40f000030301703180d0096404904052039640445d1207204011504207516001d00e418151002104102c1c2d4071003000c1900d0442911034140900b0491000c018080c3c070aa121000c01c1030b144c0b40503441c03c0c246420800c1c44074518070149000305030410810a031204181e0540200d080242c403088110308159076910740700358201e40d40f141280d0903040098404000707500a14142d242c843c00071000c000c15030400c2d222981d20024403403842d00c80c42a9400141344440414080f10711044c0280c010b03112940d64100c141c0261801e080c0401115008940720341340942403030290342c225100e1100724000d200c0c680d00c2c1c5200961000c0c000307690b0903032032038808241c4107942d400170a03401e4800c1145041045491161081000c491800440d100210005011400b03078000b400c1407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 685806366 1250 685805116 685805123
    0x60f0e07030e1207050c10050c1e01060302122d030d05040602091002150106030e06010519050a030c14010504080c0108100f090f1b020d05070501020702040f050a14070c 74
    0x7524003600d038040d4580f40c01e440074441607030800281c6030100500401e010120b030340d0648440c4c00c0ca8200d80e80c04d80d0240102c4a9203c0c140c1d124403800104100c9100501d5020b4040400010780700380c880e004900c10103a880f0200304140c0c4410340c41c0c454140d0080c2c0309040c1c262106a40203a20540041041d2030344140c1c0c1c20041480c0d2124007290a018183c0c1c100d540001c00144050304041c45020043d4407402641e40c0d8103c105070b072000000c0c03071034000d000350281b18110350082c01c1d950303081c2030422002d6074900c9051030352141d01c84004106a00d642c180000a54054222070007641c1c0740c260f800454549641c400d90400800784000c12050000040701c410b040070900703103c148c0799118400082c054103194840701b285103880400190040c0254000c000c180b51076a000d0004164990f40002070b00e0150949070300590011895000051080c00a496a07c1c406e0f40003501d0001d044c4c0002d026105500c040701c013000d580d00148503444001c0d2081f0201d20b110754510451a25148802800ca5105c006016 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 685807616 1250 685806366 685806371
    0x528030b060406050d060c0f030513020919020301170c010e0a21021c150b0a06050315040507090501020c03010c12110906160c08030f030103110102010e0d12060f0e0703 74
    0xa203003a9a2500300c240035000c0900102c200340c5c0c03070382400b00181440b030112002161828510103d064441d0142038072824002100b00c01e881001e60030300c01d0003074009140b403040d460310b20384400c110205d030700042d8020510106009540d80c460722802d4101080412100c0c1404403123039a08945448103501c0c4002c50348891812040904004810440881c50341002036100060350000705141c40c502044001480c00b031082c21720503200784a40b004c120382200e45d8079a0300c516081e000300000c5104d90000c5920003120010441c0e407403600782c0800c040c0c1e1070540d180000720380011341c2400296030400440078001000c038000c0c8400031b20350380701a00c400c0880060001450b100c440c072001004020003210032001014080c20b96038800c00c40c10600041c010138045561400890300000d48401c00026a05c101000c40b010920310703461903840c83d00d00004882454103554850400e4146035405120640720244103840d00d1040c40200e80104044070000c1d040b90182c3e0101c924148001c02034008525070065003401c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 685808866 1250 685807616 685807621
    0xc01020c0d020706080f0a181713050402070b1302010c06090506040212150a02131a0d050606030106020d261e090f15070512091b2d1302070c0528030b 66
    0x910396984071201500320704a0a400350400327904c0760014600e0082c44103601d4522502c40040000fa442110b501030a600c1c1c04001203907072610b00348000c28540d40305040030b00302034015a880b8401d8a0180030161450303003002c0200002d50800c400781c041440c01c2100075150b03006030021440c0a920f030103841c8074111940404c00309012800e100f1001d000d0108180e078402c60040100d0080c1195010341c083c8403006041c0710129070f02e420300b1420307070b41660792a4000d0400300070321040031039051942c205016000b0715500e0400119003103060200d401410580049941c0d0800030503000b0300264007501d00340042d404501c9056000e0707404100c4260b1011f47d0b1901441780e1320b51103008c503018002c0035241d0301d41e00001d10600440c0040002c2d0043c1d0345240741e46031050003103207800300045a0350460720040704944a114000050788840901c000781c42c1c004007404e80c1c00c224503030000c0403a00000070444903e0308202c42400315103404820101c1100c801d01100201051203d000d9050318000e100003001d1640d500c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 685810116 1250 685808866 685808891
    0x10509190f141f18110909040305030406050609100308030a0f0c021b060a090e100305030c010902090c1e030702010207080a03051f230102030c01020c0d020706080f0a 73
    0xc00c1491890707809104a404008100046031026140312a040c3c01407494036801d201814500c904031074011684044900328054054040c00702203840c0d1441c11800c004c454041c0e5518070b41c0e140510b00996605442c0d14141c9011421214003401c101e105100c000104044004100c07002025070342d000303240d0390322521045000409002001c0020302d8043c100403440c0d071420b40c0059034400d524107840b2412100f132098400d001041c466070070004002402803009100c0d55500403c013640088071640100c448954a86481c3d085411040d4031480e2030351610100410351820501840d008114880c0c801c2c50200e1807024000a01c116009040c1074100220000e80814001e40c155802c1a400050b803039a5007076041c05c010002d000031a40c1d0001718004a0418003110403003212501a107526480d25080104405500d54a548881d5a042d04520080180e24159002800608000300103030340102040064102c0190900750700750800d8041003190401c0090b81105c08410384c1d00901c2410340003540341d60201 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 685811366 1250 685810116 685810121
    0x609120705010207020d390b0906070f0308090d080105061602010c0506010e041202010b2409041515080702060f0c0702060a090612140f0705090901091a0901050919 72
    0x1101a5208003901254414040d1481c00d2000e40904008144194000b04551f0f000d01c0701c0d200300c2c400c1c0c00b02c1101d00600010034000010f103c0c1c004020f1015041800030b50b5200c2c0c9000004208a001036125424081d0b080020000c001110070301e0300b4290b42c95070604020807494041e210b4400e0011794a4803016055902884c1782c00c0640d6082010f40d038035980c450441c120b0f840e000383c40031996402c5601d200e0460702e1044c45080845400105204104034902d003054082c4002c00c1c100a07981d150812000c0500e41e5280702c1c1c11144060301c2085001140362000940203000303000d11990503c02c2c04010000c0c1141c2c085403055000300c1c600d04020320307510703821000e814500510358025081032000070b40c04030389600017050900311045a038400000881c0d40441e41c0030b0340c07040d06894a0780b001c00790201d5000400001c4142d480a141c0c60404c2c101b1903081c0c0000d407901800e91012103015500d031501c0091001031003070340407049000d490505695140c00b0100711b140c2401800c0c01030030440d80090000c2480c2c1d98 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 685812616 1250 685811366 685811377
    0xd1d0307050a0507050f01021c11031b01050906010f09020304111005090907091802222c0606040320060c0115150e01080c0c0d08061206091207050102 66
    0x100469840d4a0145001036940c41028030548242c03040000010f014074000300200d590200682c098180c4d18540104850128252070910050004043c1d059500000401c080d249c0d0a52440032200341806501c4400d08641001d00110300c15004040103010179000c881405089501e181c0d001a902d60396400c11281c1c1151171014180e01601e0030341e4031200d543e4030a01504900d0000c0399560820f8031680e03802e6481039440d1050441c0088a8a9103205280e02c507405440050107a0341e1550040a010b1b0803035a00242581144012225800c6620b408400304851651158444800401130741001400120a8052840001c100381c55000d030700b02c2c60a01403400480241740240619444044c100e440701c0c003a1102012915070f081d802000006c5280800c00d14412455880d220421408a200011101550010010030580c08104144240f402c41000306501c080340c2a034900115040c54030400c0341007051100341c02440d501c803006103d6100c2c0d01054020b8201c1d000c4050030b5a0f80311038900036019025a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 685813866 1250 685812616 685812671
    0x60204030609210201050f060d0303150b031b0405310906050615070206090d0f0b090d031b0807030f0b090414010c0503091b1203030a0605031902060d 66
    0x402c0300007000c10800c285030201e8010001c81801d40210180400c90898800710b81581d09401e2120100d0414101601c080907118064500842d0140000e0300404103e03107644e00546204000004220ba43c6205401c0700c074400c82580341851900c0d19120001d002c03102c02071900d010203001402103101c01714031343e0403601c070848800c00d0501209141c0d050400040000702c8081d4081e20350018500020340a03c812103001c290b0041985061010820a112000c800350350200c0e05c402e015108840482d1283d94400d1150304020020000c0c044041002800d54010a82030003850780c0d01e00717001071682e070880f8950380e100c5100d1500290100c41095020050100c821b1000c0e040303030860050102780b000c1030035522181c0395200000c1c00301000025085840d41701c11519090203402040c02c0b9000080f103114a003c1040c00204081c01020002240b00e00316841620040c0740c05a55110420081c02c09000c1e403000441d18401038521460542c0102d1800c0c07144030100c051190f03441000404272410480c1440c200500c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 685815116 1250 685813866 685813871
    0x2030703020c1b03061b0d0b04090803180d05030108030d0e0705040e030c160302060a0e012105040c05030f1f0e030c1006090204050609060d06271a0303160602040306 73
    0x200c419503120303480c04441c1d4142c0640229800646c0e0000f04041c20317010f520b000044540f5100004052900402d00b050b01c0c1e56129459080000c00708000c403000d140600d440d00030590903800c0304d00460385011203030000102440f105000400c03896102106071803d40300300388804150306241c00400c50408440360441030380300c0c6c0b400010540c0340c000040030304506079481c0e08840c140c0c800c1100394440558144802036100104110450700103216490407141a401810f0145d001e1a0741c440d12281c01030100080e590140c0e50b04104020700210180310301c002c100517006040d0b0321040e40d03405500c2c2e60301d600000f2011181c03042c04101002c42c81d8002291a0007407001c1d00c1d283c03c1000070042d240c6211307155952559041c0400407aa8a000d4401c03141100c10003000395190000d0390080c000503030480d503100303220643d503450001403141010300c0000c030700041d443e46441c0c00640c121001c000c42d070241d0001100c41942403004401620000200c40a00da075602c1410000b05091515601078810364000412050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 685816366 1250 685815116 685815133
    0x9092d021005120112020f1002070504050103080304061b0207090e1005090304060225030210030e07060e040e060f0103030c0f0c090b100e030a060b040b0a0b03060a06110d0302030703020c 82
    0x1035108001d0400c43c10340f80c20401c41640d80b41040d4a034801c5140340698803069080d0500814503003402d4000c1c2d0020a40184d904841d51140050101c071804d07030080d00d054500004201c100089803266440e8100407511510682840901c020740d40c1d00d844c0034400101d6030350b8201d0444100100302c1503200c103090340307014000c600c0c02585541d125007084c400c00001d4851980c0c249080d10013140c1505801008807030302107145107190204002c511080d8840404d156440f000440c544c0d40c00c0c88520043c040c1516448100c409040c1440308035503800719515115046407040c0101d810381443d205044075010320b00101e01075074506202e840b0b1040224024600c3c00990000a60f8400c01d40268003d404222450310301640d50b01000d0310000e01d0750003442c2d4560031180c1004005071159006090043d0050000600d00740d40d0004a601c400c0140c011f00c480136008000c200b0030780740c81c0281030050416481c0480c0203080001d00580d80d0724000420209060f0040002002c1d94800d03415510640c069100311200398 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 685817616 1250 685816366 685816399
    0x2040905031902061306021b010e0105150d050a0206070201170112030e011707030c050c0f0303041106040506070308090c04051e01090501080a030c1703040b01090609092d02 76
    0x358020301d802c0e86844900002c0580103400400c2d650300c244148010960700005c641d40d10350081d40706070340c030b800607a1400301c030102981c00921496242d1355014000240c136081001114014202201e031413846103e192116000240001c2000203216038140c0b03407280c42f05260310050fa04058141050400100c0700000000c0b900c0003445254500d600903101c031070b4000c0300710004650207018494954040c454160100d40e0079840780d07000b00320b14101482e00904100103804158241b00507018580c04036800802800f05002900ca0b074603050f0882215580c1c038140c03520f40402c03240d000300c0c0c40140900c0f503401c002411040044c018a004190300400820203490a0804128250b00301d4a2012104900c100082101125845101d061300c0040c001048014000d540c2101c2c2d4007941d0501720341e00a0805011410280c29001440c003440c450945c502e01c0750b04001d608402c54001e80c1c0080e21450816814402040d40d42014000b0040741000c00300c45101928000c2d84801580b4030001d4004040030b0552014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 685818866 1250 685817616 685817623
    0x9060f1908070302090a1e03050102181f080402011b1b090b09010302030c060a0302190806240301120614190b0a0515031f06020a03090608100512070302040905 70
    0x80200c0e480e070050340e4890300c2040301240605264280c128010f05428440c00050500e043e444031691088951141d072039644d000d00366000342d072071200c0c1e02882c11106451841c0c1800c03544580032030103860b9030ba0f615079001d0050086070003a1003c1e041c400103403010140d05003650010444140c000c1c0c00070310340040310010390311122182e05c11841e807146000c1804e80303d40f138003210b814102c9400034028080210760300c0400030f5035130041c510b500a0542c200000e080d201340c0d01c070100c044500c0c03e84800c941480c1c04820302220403103240201c018240c40d0108000c010941c030060f01c1c1503c0c1c07441d020380015007482c503008004044100c280c925042c0c008082220200050310b40070444d4103d404180500d10070141480400a064010301c0e41c8206c1303020768403900001c0f0801450340607841481a0340300d80503000d6041c00d01806070f040100142c101c1d070350701c1060540110204004018a191690441c9040305e18035182e03000714055030303200300c600700345000d130b0441c041101001441d00148108200f041c2450704566 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 685820116 1250 685818866 685818907
    0x6060806150c0a052b03021624050114011403010303210605090a050103031b02030a020d08090a0b041a1216090506040e160c08030703230103050619020a0e010509060f 73
    0x440817018007020056101c0e00a84400c951440500080041c0559501222400c0c0b19840ca24003292001c1c20b409494040c050b8600908000d0812401010048001049810034800e505100c4608100401c0003039031110041000b00031a41d2040040f558485180c00500032982c80954130803185810700480104690009049902c00d031551701c0500180b25100c60450b900d41c4008c0d500d030300003c410781c003d402d1030a4070000320751042000034500441403000540d0040f4540200000704800b040c02e00000f4110100d1020440031552154107200390810207400000c0c0051500303059016000751880180d0183c0c0c0b81d00054070005042d2034840c0e071101881d44205a0403104d120034034440440c400103260240c40086400c1e50800096032565035100c1c82500a44000c01c4465100706074010070801101c244032000f4040d511a80c050415804c0070380300c40000c107050031120000c2a104011000700c82d40c010366030804018081c00c00e90f442d40000000035185000c0d044c01e05041d120300041012503105c58030403249 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 685821366 1250 685820116 685820173
    0x50907120c020706270512030304030305101406070201020a05120a0306090608060601110a0605130b16121508060408040e010b031b1602120f0106060806150c0a05 71
    0x70400d6441e8204aa548105204240210306914550907a802e9081c1c402203589022541409580b96920045440c20170442071100c170030707000402403100f0140e040c0607480d004288842c4920b032507800c01c103148a08052480c0e00c03a200d600001900000c590003401805c004c0c03a0000141e03854081c800040410991100b14014002480d100c2e000c5925001c40c801d84050322944001003000740d440e00010343d03044141c428106102e105980c0482c0000f012070050501c101a110b0100441005510742041405000740c0790b18101c8181c2924030107920341c01541203107860f600110119070440f1040001c0308026039030304221441d024060400c02488030040081049501d00c0c1d01400f11070fa80d07a020000280410365103001e034094014a4411110030845c040c02e034980250005210940e000d40c0000c2c824150007503511102d41240c1008801d8007001c0c89500014445820708140c80d05e0941c0c009030b8203404000701c52034040004120440300003410000118200d6001303084614810b81c050140314400150184c14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 685822616 1250 685821366 685821371
    0x30c0a170f071508190e03090a05060a1403130c150810150e040209030102161e0503120a1b03020c1002160f020427050f0307050a1b05090712 62
    0x202000c1c60005420782150100703859803000300b0014404540421010340b000b00728540c030f41200084c1c20054800d50003201e51910007142d658400ba818084040d5155111a12a45061103d44142600300d0116485d041e01d020f24603039203560742c10300c03c01002e88140c809000c14a4080003c1649080e100390201d800881d511505810b42d01d2044200345001c8a00400d1080903606075003089044c05000b0003800784000800140c100410f2402290890300611420385c1a0540d01d007150092140c08414401c0d03210401c0031410400d0300700d4032082c6d52032003076061003007800680c400040c003901225805525146520410200e28140030f0300020040d4001c08040c0456000328060b08501c00842c0c4221003055000c81109e030807011071a2070700059003000583c00d9070000d40f92440d40d41d80364080c01c0c9281524000d000c2c40006c1044908159180034500b444030000e6603c1080b00401040740001c9040c0e2450b4045101d0110500b200611a011507842d80480d4000d901801404076050300004607800710f9100310b408 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 685823866 1250 685822616 685822633
    0x30403050f030a140903070b0a03050402040f0e070302011214010e0a05010f030218040302150c040e060a03020f090a0902220b0d020901061b1e020108010905010311010e030c0a17 78
    0x1c090712445109070310300102c4c86078100c11412600400291840030002015140010b5845403c40955030101d240c002c0080d0b590b004100840c03505120390520544071010800004440030862030761038016000180c14856844a03001c01c8509a801c100311451030f08415813000e5a49030f2920490b25020369403464600e0400d40046001580000f0640480360003c05d081c2c0039186442c3d00455101c0043d0003582140035100d003081c0d03180e902c42c00c094010340d0303010202c076642d40c80c040c680e00d22140d02501030303441228043c1d000c0015958a600c1000950400c03610000c10f49c41e01034039207000f008007003402504412030f0420f1086125080704074402d03a000004007800344100c000c041201000182100940c00302c03903500180003181c400c0582d51002540942080101005910349501c074132a0111080d0032101c03251104411540d0290a290041000704400e214550541e6074061130460020b0b50941002029003d60010b55010407100981c000068040761a0645942032810205041d006003130061090550 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 685825116 1250 685823866 685823893
    0x50d0807140c0c040b120d0906020f070503100213120b0406050105040b0d060e1608030703030e03030103080f0d090204140702061311100c05060a0b010914130b0a090204060203040305 80
    0x44940340e01c02d980103010b480b0303034600c10400108000c0080c80d4004103164103500340400200716040300756885454030040b052405000a1030200c004403076005d1600708420410003500c000410007444078041030050f0319198200800600b41100754001e1042c86400010392040c40000880c0b18001c502424040c0f000384e888034180015a16510200c6800010744422000410142d5200c400e90815150030b65082c0507480808403c1c0791300c541c006604540000400350304050b003503c141c188140759800070b58255031440e141e100081c001c3c4007070310581040000c0c05080041c01a44a82d002e5a8002c1c000c116602003582c0e0050301030f10481d500c0c4094030404010501c51440688000501e5a00c00b401c2e02c44c00302d8a40a000c003881082643e1010b001040010742300203441440744500c1130001950010f000050a000101004419880b107215040e80c1c400d004001d0710703600403500b1003000b444008540342d101040451404802d641c001c500841c40440d020518035408070081049a000c1e004680507002c0544 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 685826366 1250 685825116 685825157
    0x904060e09030a1d030a061a09010806010e04082701020610260106240e0114040308031302040c0e0f06040803091e0405042103060b090d0f050d0807 65
    0x1241408030303500034400070480c1c07842031900c99112008029504101c1d048200441d04c0c2078201171b4111080c82d1615056a84030008243c0c814030303000300b11880001c0b54505500c03107803585818050700c568010b241d40058184001002216000c0c01420b42d0b5442c120409000c0308942244e02c44258018000d19000c207083c11030021009003659a0310041c0090a03105404084038a484280c284429541300c20002031340e9001c6c5845403401d40e800d0340d10035050440d4820001c0c0344141e454542c2c0c0c1071000400000e50103030840000d4400f62640b00300000c1d030325100d61a210883e41400c2c80d009500c0f0341880a01811340d640100c0b140c0c2904000d95107610f4280c84030301041194040c03400350702c0340c2e41c0c4144001542c9180c6882c022004004440010605600c898003003025130b2000ca6095038041c14a101c4002061003c100c0070740701281601c0c0c10481b8509102c0c01885500c1030a9a5912a8810b610075500348070b4069511400340350f000c012150f103142d042d400a48110421510a408640c0640722048850840e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 685827616 1250 685826366 685826371
    0x806090718060c0303150f0e0906010e04061a1216140f060a0c061b08010b030601120b01020c0405041a01051c030c0f0501020c0f100903080114061e0904060e 69
    0x40149034a01c5040c000102c0c1c0d4180904810340405440301600303100705a503488510080d1050286404400e4184408500381c0e140181115420f03611182c010802e01d101001c0154010364400300214034035405c201d104503100a18140039600048179008010601c1e070004004520189a40e118441e03980c4e10310385680e0380c031102c40840360458400b200340e5103246864402020688507905003004120340d00d0f15040110b403c00c1c080384000e952040c00d104260781c6c008084600409110740d032a4514506500001c1c03a00c0c94155034008081d4a51045650581c0207104031014040050402c00003440e141c00d00c1c8058922500c3c4400002a980c80041340700d090006008840d51840500c0911001d150b5504403252525080f080d034000282d880b0b0b40000a00a0000300b043c01ca10307100a12200c000d01c80070a0828082e252100e01079440d011014000940013443c250440d40011016200308c0b070b90401250b02440384548500d02e01e604074070000074606916014280107141510b007040042c1d1525640c19810323000303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 685828866 1250 685827616 685827647
    0xc0f030b0303220b1606050c0901170a0204080a0f0c0b0708190309020a03051f0e0a03120e06010e040b0105040501030c0b130308040807090524012d08060907 69
    0x4100d280424480f40044085454124600107800b82c0d031400b00303698540001d000034142070742c000152070602950f030041541004903001d03030524008220002921070380d000091102d01036160700c000341d44081d1985c160350090421400f0390345c0642c0c89150001c4e84601d041c5003228614004100801c000e003852080c2c45000798009841440c000d00061002c00c0181e900c200c1c10201921407003244010780701ca0a49200841c42840104074900008018102c02c20070251420305c0c1c50729002c02e1402c0400c002603141c0d0001d8143c100201d01c5441e144402c03018007821030024445105e840000200011001c80080c8668000d0088045598030780080000303860b400c0c40082d00a68071841c090040e080300313100411805100205140580782c0da0713a903440b07181e0032a520003450340d00004000c01c880d20745405102d07800340c050b4800b500c0210403140301c69040701408940b0b9040095421080c1c6500c1d4403050500040742007120068215030300980d005007400c0044ac1c01c28000e10580b0041a1954040d1400c0748980c60b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 685830116 1250 685828866 685828873
    0xc0204061d07110705060412060b031c0c02030c090f0603060c0a051b15070905040e0703050d031107050105090d0f0c05060103030f120612110105120720010c02010c0f030b03 76
    0x4440004503000c405070000c0c210b45029130741000030540c1d02c00c00140014501110030b000c0094044c2001c030200c402d8450494026040b042c81061411002c0d08102917450715400c1929580142d400820f16062000c0d01e644c2c2c000c03000c841844030000a610b582c1e48289011012039129aa40c0f1514401c24010844044003080c4240842001d0041040621864207608402c55603010514503481d10581015140301c0d002c20a01d9005116a083c107001701080101a20f00500400d45981e881036510612640500c0c109540c0d50320b40080e07000d01c0300440d292180c01c41c000b03201c0c40c104040d4850325000150100b0020540a03546044890301850050000940010260055a10359101a900c100703d0581020400004442c1821503039024420303800500300c80d281d1699428140d29002c130003003d1140c02c031418044240041c52a000705e440030740d0303440300c5c1601e0550406038201840304c84c0c4040074405400711b94202034030581c4482d415840444160703141c1d07480c24110192120144c04a8009542d015003642 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 685831366 1250 685830116 685830121
    0x20c1f050115210e010504060506010e01020a08030109050601050903071d01050a0b0d050403050f0a0806270106141309020901030f05090d200d020601031b06080402040f15060c0204061d 81
    0x1c3e05003050481c2c0d55103281021440300840c900312400c5842c110340071624150307a00c051084d25640302041501070350003800100101c0c0000d8913490310741c0c04140704102e121a106c50000d6a03a0b4803a000340c03420000c014044580403519050b507100040d11032005604c980c44190300000f054500300c54440c0031103028044040c40c02159800f0003000d01002002901482000c02104260209007401000ba0501c1691521003d0034072004012401c001c80c8101b00350002450305440703941900c1c0036041c0c1101c0250070807c0048202e09074910b61401200080d030290f0707c0c2c48030005020f1020b1f400a0000a500741c0e0104041d00d92102c041003241c0c810350f25500c10b50301010000345000d0084100308004603451b03007008650042c0b01d2025291950180009005800210041080000c0c864502e84032241e07804017412050f043c100010074001000380040d103d141c5900c0400c07020201c5034403200e0010a410803000907143c45000161204241402c00c03805030f482e00c00001004843c00218003080c03610f4041c07086558 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 685832616 1250 685831366 685831397
    0x80c040b060708031e0c0405090c070209061e130203150111060c220f1a0301082e05010608100b071502071a01030b0412020606030a02040c03020c1f050115 68
    0x84c1c0000300300c41c080205000051130406240300710355100301c48400842e503846007008103001c0c081c030015008942408081c00008016502c00860a80c080c4042e0b03002c0e03040c21407818001c2502040460450b40100d07011101003008106a00118400c051440311089800310f84401110f10084285c40c0d440103401400206203078103040c00041c030700aa00141400d001103030b0018488050703034240c1d0001d50000c07002007040040341680044580000481071342c560556140c1140643c4803465400c0c042100700e105801020300c0c1c6119040d036104818a07141c100041c1d070312400c02500c0348400380c80c00c01075011880310009409070000304865544d03901c00101030500703884860100294002c0181100d1005e11070300c00841c0c4070183c041e628002c4d4000c1d00c102e00f242c20541051485420b8244207502190011010070185031800224030032000d41c10303900007418041e00c100c01c60013409040380941c0c4a005e1981c0c10403070000700041e8032842d014061820032099036501401034015900da141b802c00f09a200d00c0c5800708 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 685833866 1250 685832616 685832633
    0x30b01210c030b060c15010f1d0403120212010f050d0c090b18160e0402030402060304141603152d020f0d060303051908060303250f050601080c040b0607 67
    0x2400c10782c103011442a00385000500c0942080c3c00484035079201c00f02600d5041c104c9021540148901c507080402281850260422100e0103842d02240c0e464a001141c01c1510901162416a10300d8004540701c0408a5041500600c00e02c5400c0110083e034401080b1407074200d03454042590700450b0034840b0b6140c10740c128050844000c8080d0310405041c0442114028006401d1207440030b002a00800b9504440c06032003180b00e00c1450b80100d00c14800c110040c1c60700d808490300b164124090000c880c01660f0305c989000c1d814002907015043d9001d00100700204c400c1040000c040c00c11007480a204020102101e00d62400c4941c2c200c030100420810300100254000c0800401201d1020320701758130308809030150347d400d50045000030000114601e0302a0702021b0001c00313000b54601001c0905100c0006030b075a006d00d100c55101c140501719444581544404080000d60303114001182529450600c41c1d00ca02c000d2007428500d00503c07010b1800c03880c091180c040411002480c403400d003105a12201c82 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 685835116 1250 685833866 685833881
    0x7060c0203131a07020a0b0c01060b070f0f020f0411040501021e0705120106090c0c1245081606030c050301090905010b0d1511030606070204050c1c05040201030b0121 73
    0x200c190f0304100070380258803603a02000242c621070100650354661a41401d086600b1a0301059801000744030702e030f001507403044550320007682110800014000e01d00000e550b940010000c03d502a15104107059103240d400007410880310240c007500d824010803c06501c40c09600c036400e02c80c0f42c100d4241030005d803a00c200000580340c03102000044035a1a405d40320100ca5240c4031440201d24548468000c1000e40300c04503d10a9881c41c044c00310385000c480000030a0340c4541c4901c160003208141c6100206405810310072080601045c1085036035404c0e015403620002c400381010b424860038042400390003401030302d0008140c2e50340c8624580c40c0000150007411241d404907035070354a881c1e00201d1641c0d1000c2092025008034404100409803482e550700300c40041089042a080c18020015581e40780001e0700c00454040d6004951941e4000461103e80310310035000f150f0f40300a04400c00d8060440e03000d14480d130b100f038030200070100301c01c4010b48114001195950080d0322481c2c0c2840c0624045d00001b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 685836366 1250 685835116 685835159
    0xd05100e0a08070302011a01050a1d030c03030310210503040b160b18010e0d08061e0303040b0319051501180f030b040506010b03012313050103050307060c020313 71
    0x81e0206441d42d6402d220b544449030a800507911541040300e95040b40841c500800000d00740070b4603114030440d0113001042c080300c80c035546803404440014240c8080c011210301120040980b503980c41c080e1951100749150703000b06035070701060400c090000c0701040c0144000641000c01503042625014140302c0f02c0d444080b114140c020201d44660001e018801d0f002c1c00342c0c03854640350f00c50010000ba003500315100020b5030340341130f0700800b140b00d4020b400c4900d05400c10402d440b07503003140c10041c4049035150981140c00d6094880024001465000c980155000e42c02e803a490b030b031011201d018400180c607800c0d90002c6004034880903103030041d07008040316422f40090035401c2030101d54550041950001c182d1003500e0b000c0c20700c0100000c01c001886001c0c0502003060005003594140500f02788014032900030a83c209950123a510074655a28519034082e10315524180441d40c1c4074038246442e44c00c0000308031219401d000c01c81058500200641d85603188502c0a81502440c003150802c4618070311140e50f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 685837616 1250 685836366 685836373
    0x1030c140a1701060804062f030604091e1e0314071103031b250506031008070f0302190513090c240f0f0c03050307020313230d05100e 59
    0x200b441c0300c000b000681c000c1c0401e8840f58080e1400317083c40300a981510851072050b120092140e0108010545116000c40661402d16102e90f10840490001d08603890050005807452030301951200118100c0036180e4407074940185980c050031030708642a03d5080e4020003042c1c0f0b011604610340090700282c28a24095029034240510307900200b0305590050078250708d00302c028607042040710000c200da0040c0d22140780c1d00c10081d910040b0242491585801003a105110020214140820910111010b42520801d40c2c0303c550f03a0b042c002032985e101b071004034024122140d00d121420000d20a40c3c01310391000e0152101002060000310052010b10340407030b88045507a03804580071410394000c200301640c100490180301c15422020b020320301942400030400c0300b00000c058445501c0100c03c00789981c90300b80a502d03074807002030503400c600038182d03040c14952900078009101d0140d00010307904000c0329824005008145400d002171000c2404000d0400c0d8400400100049416800541c5009448094 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 685838866 1250 685837616 685837637
    0x1506030c07060603260403021509030f010501060915020d0206280207060f0b030703050c011805220617030f2101090605040506010e030d030e071512050601030c140a 72
    0x85030304842c2903070130540d03500e0798042407002401081000010103070004064641000d103558002000c0045151100b000300d41c1c081105261a20108803004176607554030000c0c0320961710382d0f400424540003482421307080448030603689511070012840e602005200c0d03015080d1640c483c0144405940400320360500e6099071602c1d00351b04200c6102400f0a00d10a84000c0380c40040b0042e20710a8074500d0286501c83d0302f21550810004d480001c850012140278200481031382030022020300300c4007595225a4001c1c41a008500750000c01400303041c08404d44203070400c1001c1e218402c4031130410448403200e4566100700030200a40d0790381c2c0e0280007540302400040071b10b000120154004a0307001c2e40050f81580c0c8540040c0844d181c1801002d910501c2880c0103400b880b03003080020f58900151007a00189984d078200c2e011160010300c8403901030200600c40280340e80d0028001400d02c1070035008555210320740300204200b036209006416155200307544d06c8003500300c15082682d1507440b0004040901015004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 685840116 1250 685838866 685838873
    0xe0907090803121801050601021009050705040504050a052104030323041805071404050d020d120e15030f04080307030e0a0807051b030607051809010e040201020d0203031506030c07 79
    0x20001d8543c98540b680c4541419040802c413446039000c03801850741080100422a41e002600300400f0b003640e640840d030355440e404d045081540395044960030a081104100500c8000500148001c0c0704100700c0e25072a0510026400b0402406003255803840100130400102e4829a80e403201000c40072179128401c02d4001c14800d066000343c0c000b29074160340c0040d00c4101c1005114165014845050142c003500609407403180600c201e0050070300c1051054104400e40d01c074610000c90280e800328580c00c13000c0c0c204201070010503012403d00e125140c51104000c41003424800c2d42d0040d65072030100c0110703451b1075582c2c0c03070b81d900000d18410070540d4a001d0510548410001440c0050007142900e54901141c00c0a5041c03070700c0500d0306203444824003144035091b1070010b00154060724500d450303925011108508420082d50350764075603003d009480082608582040c0441c000c41c0700342c0886006000e039040c1a40c80b030104942410304c4200c42e0418000a0170010020765125040c80041840c3c65030541d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 685841366 1250 685840116 685840123
    0x90304061214010f03050f060613020c0f1005090c01020a0f0206162a0b03060d06052a030115080c0421050615010206090a0503041a040b0d0c02010c030b010e09070908 73
    0x2132101107a8042e4180c10010702800340030300c07e003686043c009041c0a2403d40b011480c000c900c1d60708941116400148501c15820600c442403c0d08d85c08826101d45211007e504c0e0042d03c0c0591701d02c060b6025640d0b41e2492580001046400c082d4407444150f00d01040f41c007007100f160007603090560610341480711500041c6807001d4100d840010403140010f4600b40952103030301c03110740340c2080240e10130420610100e9915004000f0b240c50b0304c86c5020900f685e560501108052019003c008083c1c948156020b0008028001e075060b0760303120001c42c0075140f1840d01114010b406a50404a4440c200001d003e079141603002014040424895036115650a55500d031500301d0890f510f0187c0c1c85442040601981e050000783c0d00000d802e00200b009003000e456a544078402c42c0300b200440d800e000407c40082c10a07400b80c0700208000310300940c44045105c5107070041c1c58440d185000652a0112401e01503000344034510041e041a550002c5840c43c18040c0151240060089000c0c041680000900014100f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 685842616 1250 685841366 685841369
    0x618030f0f06071b02100302090303280e060d0e0705180702010e1c1209050d02030d1811010e0102011b02010c122007030504030f11090f09030406121401 67
    0xc000078810100050714030390801d200641400104005240e02c58900b4039088104200c8580444501503001d610b080194000d200b00c054454040c003000c200700c41ca020864141100d04c00b58070400c01074845885004460401907000e800754482400c3c0025840382d07001744d00013103140f0b001c43c086503e8192220001800402d135422000b80d51040702080101c16942801024103480700500100710b10040c031038260038a80400783c9a001004410405840e9010360742e004200c900307030010282c2d1607620100d50025203e42c0031a81e00a952401c11100d00003034008440c0041986401c4241034180107a01001110100c030b90b24407850445d9211140c4509006400180c1101c04000750000110003100404c00781060205c45e02c2c0e007000c503250950120703540b943c54400c950b04031210b8100540e64152464141c44038056508050208500103006100b0003121840c04c54054804652048007903980000300102d07001c04031080181030f0003e20003041407601800800c0c1e1000040400070861105510041501007002d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 685843866 1250 685842616 685842643
    0x2030c0306040e07140103020c15130308090a080a05090d0204050a1e0509100b1201050a0518010b0a0e0604090609150b0a0e06090a1b030603031803020f061803 70
    0x91005614141c8614070100d83e000001d003030590724225400c20760300d002c902d445051540000e54400b80c0d01040c0900c1c1d810400c00681c034000c60030700b01e0820221004d90b2004030045040080800c0d003014001840181c8150300402c2145803142e01442160580c0201e40c00da904507400c1d4491100696850143c0d0340308850120b4005461701c5010314044541545c8105036800a261a05020b44900e01182c0841c9503001030703101040055131030740402d1910501541c0304074030754a0801401001045074010901414148445480c49041c10420608a620fa41110355100d03c1610b8100041040341c03640341d40c000300c0181300150500031b50b00c0d0341d000e41d80c0c0034408542c410010300d0750078000202846221301410342a9881c1c5142030805a250152400160071144141c0c003902c00074600c0b4803c0c0d0000034034100600521071750a03940d900c003e000303410305000480210f50904802c184440004192200700c980040c011403001450000744401d030b40c84003420782c42410710010200c060340c80030000300e40740604 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 685845116 1250 685843866 685843891
    0xa0e0a02070809031c03110a0504090b0609031f2007030e030f030f1210080a24090302060402030f01020322020a030f0515090d08070e0a0509070e091b07080f0d0203 72
    0x2070018010f08035100542510071203882070000e4008c09901c001036a0a0b107960040000e5000c0f2030100103141c60090013041079040c4290440360303c07003501120a28040441200f0103103e6290340500c1820925450307600d2440c02001032140f100030030701c0703001992a540344c050140c4441c1c0c3e441d003180300d04603032190740c4441000a00203124900c103448a9103240d80807054109848449080615598885d030444102818050804100603403104506248014158290000b04244820b40c030b4080c1d115001100c0c281d101c1c2c0036031080100001410f000f203d00c20300e91074220101010585d600382600c680441026600000c41140100024001300340d07a01c1e900307000300700030607a150911500004d241c900130a110200c1d0880159071601a03004480c0036040380043c240541d0501034480410120500d42d030011f03920810705401e010040c1d03002100000b002c2c030207441c13401d803599035036102502c2d100e40400b400300660300804c8a4000715042e44043c1400742c0182d11024a0060709010307441c242c0c3c00c00d1300c5500c903918 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 685846366 1250 685845116 685845163
    0x6060619140a0c031b03020c0d03090506043b1f050a0b030f1003050a060908120c03090c01080f06010c0201140f030a0f0e0d0e060706020c1005060a0e0a0207080903 72
    0x64001c002c00604440b44684036104088546d0001e4581140340340a6010340ca03514884c10405002d4125817001d000c3c00b800c281d850302e03902d804402007445020800f10760340ca0810000d41c2d1300c010040301203503080188102d034499516046050142c4280c000707a0055040700c1c0500206840c2e4480e05800014440340440588034244400c0b4103c1d802d50190802e4242030360313200100006a0007260f10110980c111800007441c1c1d81600b080340c0d9501c03400d01c1c40107040318014104150450f441d0043e500405c00c1c50201c0308480707200001510000306c2903441a581d000c1110010710250307c5418208031113881071414100303010580104002d43e4000030429049040048200440c542040c45109011400d81d00d007840000796483c1d1180d11210a018188200301a81d2180c0840d40c880901310b80000b07038071070401c56403002c13403807507864942e615400302603c041c2c1044045001490408481c10944007801e00014450b10740400030002980000001c503034000b000c0c801c42015950501440e64128003d247e0301c00900e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 685847616 1250 685846366 685846373
    0x170304090506010f020d03020d2327060412180f0819031d01110f0a0204060504020a05040905060a0e07170a02160206090a1a0d0c0206060619140a0c 65
    0x4401c02400b0340d0400c4103e0350072640c01980050085c0800360141001030b941c000307600c030309409045e00c030700c402400310011080040080501000030303201f81f8a0b407440d0250120520300c0f044000b04114008003095001c1d101060118040c01d180440414042c00e05015860039507810f80134420150384014448120214200013003002072024420b43c84044510080c0c0310400d90300500390543d07851081081180c400c29217800c0b0790180c2c0d074404505011008a403024121a440659503401081c2c080307002d00c1c1004000603545c11301c0d00035500c4500d45500c540382009c1c10024040010840200019441561130341300064001700b9201490050039641e507503284241d2100c12100840201809084005204000e600c001c80e1890980c01d5040e0390494009580c4c40c0303c3e40004a03c0f80700c070303002907401103040005401807850880080100c1e011410081c804d521000d001079031121390032690380ba08840100106040582d0b415001d0b007081110341804640304082c00d002e038005030018440c403008242d00038401c1c001e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 685848866 1250 685847616 685847621
    0xb07023304060e010e011e02070b0d0c1e0504030206030a020f03040b041109100b0702060d0e01060501021605130b1c031d030a080415140a0c02010e06070f170417030409 74
    0x203607070080c2030100170b028050000802d00d00005000c1b1117103030745001805e17895500c2031120380024040d0301c3c0c27890b4980300380340c074142d00411740d40c2041c0003ca800070081550341118520720710a0444181c40d0641464959020310410358401030400071166402c004203104102b9074009180128054032080c07071180f400f0300e00000700000d1039203250f205603000810002003580000c8098282c13105407020b02e485003207901c04503140d030045429904c2084d050800b4040d480005520207821604e00b64212280031040c0d0a20f03902e1180e060161541020815442451503909600030403004a070140c5400500c50340a05881010204a04101d0000343c48030160914a0200d1b129044400400c030090180d20703a403503486a003148118030a4181d8489a03410070010107020341c3c44803110076080c10f0159504c86080d40002c0004a03040c00880c04181a80f100d68650305141c0161100c55a004400700d00c5940c01e13480300c52801080c1d500c3d44008260410001c106c542c6204800101c0b071091800454a417400c2003407000a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 685850116 1250 685848866 685848887
    0xf1b07120e09090604120311030a0b0a0f061e1e08060909071d07030b0d0c2306091909021605190209040b04030c0b04080d05010f0b0702330406 63
    0x10504890040c400d0703a940200713000303800c20342c494481c848504030280107502401406184104000c004010814a41e0441e00b0503610300408541030f0100d580c9621119500c5541400341500086031007a521080061003900140b0b002094104004401d00013501142c41501042d40300d00061a070b1818040320f8141003180c0343c0c10500680240c0b111a041c01c801c541078580c40e045200d40841c101012942c01806a4018a9480380c090070b01c0054100c1c43c100310001317031494403c85c951030120034262140c10307070b850030a0b00344110b008220500d003ea0b40010803280c0c0000703801c038039154051910002000d8003e84010001d00f00e007112000c201000300c4c1481c50902400028210351003003c0440304005a584000c1250f01c00ea201890700c00340c0d01c80d41022650051800c030014042c81841051006100520018101112604005000d43c0c3e0702c0700400e11120300c0070310801803210000d010150040ca04500034680203070003c0c84000d1a8901e80000b002500310f01c02d104203050700001414071209502200e01c40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 685851366 1250 685850116 685850119
    0x21201090e0309010804020a03020d2d11091f091d010209150d0609020d050603061b0d0e0f0313051305040209040f030c06050f100e06090f1b07120e 65
    0xa00c00440d440e142c2c89104003012a4100103841000600710755036441040040e40d006000f026060226240100364110640c1c001c40301507501002074102480290b003c0f640d2154003d0700e900c00301241740306211803d600070704a400851142e210030083c00c000a41540d008014402010445200f00009107400c511100c0d20a0216401000405002c1e00c600c0e800e600c42c152903c01e07240d580c0700c0703d25200004140940100380002d00008080e00e40d01019003156000e0482101560b8103901c0c0c410540d0300c0f01106078851400d01c03e05000c0c901401e940c075800b803a119004241030300c11040002d110350b42950b008040c02014080d4040c001d00403401e0010320100303c48103282003002503003440d0700003500004000744001c0c0300d14400000788081620801b00c0d180c1c000e40c420403e0045080107c003281841c0400c071501c1c1100d10300103000180e648081000d0900450015000c41020b403100e04140c00c040d01c0c000c095403030f10014425550011078a800c01000c41d14051030b43c0000c030f101c0e22440148906000e0910b035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 685852616 1250 685851366 685851371
    0xe0a120f11030a0507030210020a05120a020a022505220509030307140a090b030a0e120915091f1101060f0312121d0303010806090a030f0c030c0204090602120109 71
    0x70a8094000103d038100e4030702d42085900e0390040d01d012032a02d801005e1441b603032800421058a0f0540100250035102e5200e5a03c8035280d66041450003240920140b07040160701200150382c00c1c2031201072401211001d030cd03000c0b09640e1901c2c01b00c0c1d81c2242c0c1c160a8215082c07402d01991500090f07201d2a83c021001101451850810b14802440c105945a440c94504000203421a6a0b80110a03200041c2a084281030f1a890298503043c000d00010001244a0040e4503807040c803100643c044807141c040041420610310f10340000c0c0c180302d4110034000780d0840c034895448032091030f65054419080d401a81c520005c0d220b68000c6900f510480d521940041c108014240001001c90105801070011031524910400c54082010b0142800c2d966904190483e44104c418818000c0021810383d01d10100300c4a03280c5900c216250380300755646002d800180a4048085498420403811010030b010f480c050010101e50340010b81118a11041110b44035400a40d825807529008102c82c010024010704 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 685853866 1250 685852616 685852637
    0x2090a1d070206040b0f0601030f0e0f011d1504020d080304080c0715050a0315051c02120d0e060c030d050c0315010e01050d0b030f0709060602100b220e0a120f 70
    0x1440e15660010780446e0010030710a00003a8680d03c29840a500c111504409000354290001d805848d01c514400082c803e5081c119541d1201d200742c44030020a0303410f48d00500c0401c001608081070004094800ca074480350f400c4400c804111102e01941c007848c06010b2403692981180742c3c00e494140960310101c1d03070702900c64414201e00e8014094032000703600ba0802080c1d40000070070b00d410310b40715500442d900404412010140c01d00c1d8083d240c0700035100740c0740958100002c0d96055a00e00c84110703080009900005040e43e80d0034000090542001ca1100300d030b0822002e41103031825210700b02c0d40d100b01c528020040008a041071001840e1041081c01c2c41406c1c0c40907030000806612412010303124180c0c580d048280701ea2002c00800540b0000903080e600d181d911014003002070101849040010320410140c0d0352904601c0c810782c2e40d030500040c400345400850b00107001102c0c0000701c81004281d90742190b0a0011030510408813a9841030010b202c480d41280f001500741c0040642d80c50410a01a20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 685855116 1250 685853866 685853873
    0x20912011505010c02031924050c04060c031701090209090f071416021201020a08090d09060333050108070e010219170f0904231902090a1d07020604 65
    0x1400080e81c10a180c40b1004504d00d00100c1c2c58991040081c100c41c8041d840d20005206605202458005020b0301140105401450322001d0354426140400d04403410042000301038001d01d940141d452003070a01d001590a1010308000c818026801060300b5500000d66451500c5c1205913143d010456441c10102410540402007047e00300714034074858514005000c003619080718800c08a00ca600a00d410740350b819400300e05010b13400c01070400c0082098600455020600424015455801651010b0000d481c00e0012400b901070a00b4042048418100080c17160b80e0100381400f0f18418100c0c1c00660031b240000041228100510b0700781001b030f400040000e213aa01144c0d82c64805c800340b5800b03e000304581803000f4070342070940411442d1400056054602c80585019082500f0100c9080240800121050240408603e086224030102600050035103980c4811040c0440c1d10480050400c1540e5000c2500320380650407070105041d81103011040e4040ca4400c403644035003684040c0641e4141a41d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 685856366 1250 685855116 685855151
    0xf050108010b1206060d0e0c10080115140d050109020a020c090712051b0304120207080c0a0303030e01150609080606040216080a0e060304030807200601050409032102091201 76
    0x41c070009200c080104d0003941da171005444441d911503200700322002e0002440b039590a045c00119010700b20a0300120f101900404495049611002a1090030a0b50902c01c80e9002000b05c50001c0804050200c071940c0d11072031190b00e0280c0014100180c1c1c41c40342e140302030714100c1c4242c0038920484040e4104010240d0003062148143c004950105d010744440b000d5002d001d0300c2034820114404080104818014481200b10964503a5002c7d9091141c4840c80c0301d0703c4d0020700d03004541001c0001030030030009205c1c1d44102c4800075054000a10500914030480c0040711a51191001130000d10701406810000d2003c2c0307401c0082250f0440c9072560100b42034400c441500c5010309244008100b641e10b060254034000c180c1100100f03003a580349400e203800f8000c4007040c0c55000005034030324413401903220504142200403034000020001030b860641040041d2088040403801c112601c2801c0190568841c61814110143c5001588600c0759400344000c1d06081003800003a07a0421008a10468092 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 685857616 1250 685856366 685856377
    0x510060912060b091f0b030903070210030b09070807020f210f0d02160311060601091707090515030115061202160b09070513060e221b0f050108010b 65
    0x74400500c07003141800c200e0001d107841148207400103100710810850300e400c001000216241c4018103c000b6865501074902c50000715100489540108280300c05403501419401c2c25543c64600403960f1601140890382201c0f06603008800301c0d01200034400f130350750103000c40d00500529800402d07601890748600c0f11a030380d1010351403c2c1c9107000640403e08904c1e400484184200e1803000395030303407031a000200310704002e0002c0a500140f5182e0001300c2608000c142d02d409488160358001e8558240145624a001c000d100003d2900c00c2c01400584450715020745446054440d0410308025070403014142558042e40110801491084c0140039590300075600d28090080490300584841c0c00f4050404150000030018040421440420040d1030000138408141d90050794a01107202e1f0303c3d12004165001030003549071006030f41001408202c0807944000b0000408420351051012540714000070505c1241101001c00350502d09100c4a021000804000c001c00e182140903980341c00351140301c0d070080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 685858866 1250 685857616 685857629
    0xd020d08030901021e070201140403030503181905100b01020703050706142b0b190501050304060b120715020304031a06030a0b07021e1203061c1b0905100609 69
    0x710100e84803240035419912411040510010b50405d00f204a000680012104900080d003501c1103a4590024506507411640d140d22828190740b10600a003484840e040500300192154803901c0c1502030078001c8110b5114090000707440e087d5490080e000c10380311103007200780c15544101410400500001807074400c482c0c3c20b252000c0741350340481f4144490720480c1c4405a00c59000b6a1034449141c240301350042e10500e1820030403a03640803106000740303081014030704004200704460410255000b00001c1d03505c03600c102c00000d01c0294480c001204c0800d084075200f4a6448858140080011149240c1c1c5280c103600065003464516608d80c0010385070002400e03041314445001c075850351010000e191609a10001810080c0380540d0000e554003a0305414001480080d031003c040b00101007601000180031000c160300d1917031080c00340520621a00c0e404001018201c02c0400070401e42c454820f40f1980705140700701024a000711401c1503a8003c4d03d01018408400c100304101a000403241003150724 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 685860116 1250 685858866 685858883
    0x80309030c060c01141009050601020f070603110702060c06012102060412030536011404150c0b01030c030b090c010c020918100203180a03050d1e090302010b0f0d020d 73
    0x110080800d015041200400072502c4000042c8101b1401d8004100241d07403680c2c0081200e0350f0344900482c1c2e20400300b9000c00c803a803c1b0381010b0110074480e8004000c10801c08002d186803254940c04222983e02010340d120303e5030000401401242092147d4100b0300b100840c40204801c010b1300002d0092085120312074240c21030040c0c2c102014050f0301640c6000f501280040d20350034150b4081c145203084508511110582d036002c00010f90f01030403e6901114400d0451810503091031407101000249421200910058580300300006844588042c040d45c8500d419081892551030001c05600c00940018016003114a2803580e076603010030140c00c3e060301215108541e4a8048044850452a0312a07042d00d0044501c4c41a4800d51900218002d6440341c1159044020380f4204546440151000030000745040088045000080d0040c0d03401205200030729407a050f10103103c8080f10404201100540d4441d01480420f20307010301c1340740e12140c05843d5407000d20303d10380c0004c203d4080454010103482 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 685861366 1250 685860116 685860127
    0x90b13031e03090f03020a020f06040e010e060d080a030c0219021c0212010c11102a031d010504020411090303220801180c0906060e0d0201020f010f020d06080309030c06 74
    0x10302c240c002c44100d640040401e0310400403424025243d5200b5441a402544c445035004400c1c1031007011142102c000245458450342440810000820040c040c13503400390300340269a000c151400010000c104590b2000121194015806030405200c0d40c0c0300e0045443d146814405a104c1c5082c40320f5060308060681180171591001031020320840000300c6140d0300e4980c1d0103144540160b1442c042a05030030440d0702003010039100c9002d40d4035000388485003c824484011400030b00a45e004400012410081032288824500d010480c244010b079488680d100c4051105605142c455041c1d080c0d4015000761078a0f442001284d603a208101002c001c24170307404c4804510980d85462035028040180080c0715604111007110b01040810600f5200c1d0340b8040800220003526115801c211161038031200c00d0000b12908010501803095800e03410b5004002c00780e1398240e820310441013001e80600c001a2100d4400c0e504104071041500408104d52040000340000d90b800a207201b0102c1d004c990840d61003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 685862616 1250 685861366 685861427
    0x10b0d02070218090c03070b0304260d0f1a030a080306011d03030a080412050c070b09061c0203071101140c131208180d0b1f080709090b1303 62
    0x20880c10f0707160921a0b000a0040882c400701d504400550102d0441c0d0320070742c503000724502d188019100206041111800002c543c0c9000c0c0e00415442c032086040e90400408000c44815661040b5040d80c044e40c1d5100c2d01b44112150000040d1040ba080d0002d00f007060150b56480f02c41d100241a446c10310101d1075205043c6ca00749240b02402031030140c140c2e6129242981c01070080c150980b011140c19910218144540344900c0542e5500c9000074003d1403120310b00b0170003041c103500001c3c142d43c01c80340403c5040d0140068a542c0340701c1440e16139006030341c2c0c6401c2030300903c0b0340c0d003e1414024507410000b0030844514002c00c02e03074011b510300d0080c90b943c01080780085001500b41d0301400ca081c1d111441d072010f010344580a0150345c00050b1550030084509800c1041014503210000c040c0e2500e48080781400c000a2540304ca030039030005401003407a854101e92880d020b41076000410b40784e190401da0b020000e0282d001e5030080c1c1c0b00ca4894181c410030b031340d0103031038098034164840c01260384074040c5119 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 685863866 1250 685862616 685862629
    0xd050304121b03200132100605093601080313090c030b13090204050a23070509031e1c05030c2101091505030c06070609110603070504080d020303010b0d020702 70
    0x1300003a20001c1205500c0840c0140c1c81d01d4500c1094403081d00280c14090400c810426800e101d1034540c0101118036052603420f40d406c0d00200916900100c0104058058808043d69003a90b403a14000d00e440c1c419400d02c80c4030103040e0581103211107810500c841140c0104582000066039034842c400320b504443c0841c200d0003031281160b1a43d110100c0e020707011140780c3e903511002d9268000e840a000d50380c1d40c800d010044d03805001c4002074090f0110088400c0c081010485500a80a45002031420742044000b80c50016890103604038120700c0145c401030440e041140681c0c5030701c0c841c9040280d82400d10702034070b14003004007100080b22001036400d00ea50094020748400c01141d00c0345005075610f480b0004001d00001400c02d40c1c01100d400041554500003404115824005200300d1030482241c1e1000c002d061645412140026070b00b4540072155500000342d4400c4045545031910780b03180038140c034680300c542540700d015500300700014820600ca4200b110b18040e004407025a842c0840d1000c41e54 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 685865116 1250 685863866 685863917
    0x6060d0f0b0c090618550b030907060219020d0c0f0b041e0e040b0a140a050702010f0603020a0512010905030703020313060905030303060d0312090303020a090f0f05120f0d050304121b03 81
    0xb6a41b45540c0801c801d603260018500594015044031803683c2c642d43c007070740d8501c0304194403039020110080150044c0350140211502d01d03c0703030a0740c1d152a40d90721941810101640c1100f41c102d2800300741442155180290f0f280c0840c07a8001d100807041c0b82110200c0399510180020300302000c2d01c0e00040c0d2028190b0420070100c40350b141c011030300c0d25040d5401c03001048140d40140041d400c0105055528800380994000d481d001040c2010039894401001014043c50384242a00d549074241d69011a0742403018114060003030300075507907030005200d0b4010160302a42100d41889001c101c10300c61503d00000b925400030059a50802890184c10291000303108403c81c0d040507070802e0003d404050b40f40d009407d110350a40c5078001401d07142c0f4840221107055001e078150400310030f0801c101d00d14020348a03900c607448803015101001c600c003103034070f04210911500380041100042070204002c09000c068002c10702620344007a90008a201918241070030940c0a010401803035540c400056803620502d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 685866366 1250 685865116 685865269
    0xc0105073801030c0e0703050403090b0c070f0801051503060f0106050307030b1c06051e04020f040204050d0605190e060619170f06060d0f0b0c090618 66
    0x401d981d480c601600f0b6511580031301505d0108000114000303a000b0b0060314040c80d030544880e60500e05054800303040d17801011006031540301e020030000e07040240d000b440018000b094004501494880100a070101d425003a0501a502c01000c1041107440854220705450303651802c1581d0b07890348034044015110780b99203035030f2120440104070904890700391220f500038810300e42440035580c0c1800c0e4060340081c50288019002c2500c002500505c0c20031450109600c00401c01402e258494012843c10261460708031602c81d910010300085002030b10006031803080100061103840400d03ea071a80316034000d00886d010300d8605000502d40007a40c11002d02601541401907070f003c1103040680e40d901044405014180204400714026080501c80415010b4002406008400075a0303581e6080860081007821024800e0000c4e950030b660342c400420030307544076814148800e60b580f0200b141101d00726444442e00d06040c035038808868103a0203031151345041c1401080c801580d81104940040c601c90220 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 685867616 1250 685866366 685866473
    0x20303041a0426010b0126060402070b0c0403140607050a0509040e011e0b040e070510050c011802040b0d020a1707080a060204153009140705030c010507 67
    0xd030040983d400300396200f4030904001d0290480c0b590040d05e0b01c5404a03160484402035101d00f903d83d604d01d03605c140e042a00940b00621f072102d40c0e21010b151050641e250003c50310001400c100340031013140b0132b10301440700c800603024505001743d001d05203210701c0b07450314103122001c64a0407042d03403694007a41e07641096074000c2c0031100403082050108080c100345050b482d4507048100805003454810405d4103129440140764031070030141084808090b0600030020400c080001c2a21000c0a0141c005900d0030540700040da8600d0788100016604420740203401003401261410140e6900030850046400c03928502d850141c21181d1039091a089410403400351203841c13588000c0050711783c010021100b030b9801c1580940e10181d07080b0f070480400d51401c00756860b04400070900b19406502101c101e01e0300708000465401a9490800d015099104103429402c400c80400035414244001e549841092801c80e181070482c1d83c407402c441d41941c0c041c1a12781b000c020f01c10210390581940c641070241d0403044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 685868866 1250 685867616 685867649
    0x609040c05042603030708130501090c0608070816050c030706020f09030610031a15030a0606061e02150a09020607060c030f0c020a0f020f040c02060a1107020303041a04 74
    0x141440d4010303c01c62410310004860340412241c0c1c02c804458140840700518038545412030100c80700700c2d000e440d003040101303a407081f0360000d4004d20a001e40a8454001c51301c5e800c0c51f201c80507240702030040c491002e02200c1400c0269505018000031407524807400c1c180d44231607120704007901e14054a900181280c0c40000c030220895801c001810b80c101c42241124115560140c40d5100e4103644e100042461141c043c0d0072a480c054030365007a42c403400c400016590644e05200080c44c20401d05402c1d60320990b500014441c25601a9034040c44048001d4440b01c81c20b40508000d44d40d800c0b0f10000300c5142c807400c002c156407268030f811002c801900104115115403540c2854002807000d8560384000c289880c2800040010b9800b51048620031030f0042d18040b41644c54000305c03034002c1c210403030307004502100d0483e10350f03168460b040001408d603000300010b01e8107003000011984454800903940605009100043e03400108031401e4480c404050101580f0002620507039010342e80180e02d540c4080c1e0700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 685870116 1250 685868866 685868891
    0x30f0806010219231606110d0804050c060d020a080f0601050d0e15070f110d08010e042409050c15190903021011250b0702060c0d030c1707021506060904 67
    0x902900d520180000000425a95041503070a008982e0221f02960460340c0705505803401249500c1d4454041c9080c1e8030441926000501c480d40f00c522004410350b8045080ca0726280d00401c1c1c203a014000f0076160303180b0b052140000c0c01900410000503003060300c9030f0b000d40303980c1418005000c26456602c03003440303541842c1c1405040d04bea00c410810004c2c0c11481d041020000014807401e400780c0caa100c2c14590f9003004600101c11000401c02d540849003d107905903410070420841545800c1c10700c00140c450210324005003040751200c0c03003a1041960b80601100200d0304070440e000300b40d501c1046003909203241d030185e410a6540c1e1001e9405910450300c2c0f4485a005407102d030700c6900ca074080c0c800c107504d960110001f1507460b2951000c8003545c0c12051050001c110000e0030a0f5000500032030800c200113031014030b091300c1030714a600041c5c3c5039600111702c2904820110805c04101032810454a8211070003982c40d00d0030403041a949030550301142c2191254004c817044000f015005025419a1a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 685871366 1250 685870116 685870123
    0x4053a050405030d1812050102070b0c1804020403020907080603150103080a080f13030e060409050c070506010e070503040209040c080a0c08070605070206030103022713030f080601021923 82
    0x110b41c500901940ca010340c8101d109544005a45691a0000c0101410201e481d100001008012240d941d402c100400204400c0c0d408203200b0008148119030300c51094681c04054920301d401c550013140180424401a990707010701542c081c00a24000006a850b00006440c044200c119910074110801c004414003c01034010103a86109440362405c0d912517202a00c0d4a03d022680ba041c41c0c07072445280320009228825255100344010640d504042d2111b80740030032a1415070707402204c401d000030b000b403c004040c0041030041c406114542024505404007071302c90b10004000a10900706030000030104150304000c603001c0c0030317a9001c9500c00e0100380b40c180441c20a40c000d40c1e425119190000400303510031412030303003181d6000d001c040c01e507441c540c05d0140d9280100b1885001100352030310540243d1049501034400e990b0000742c52054211418081e0200c0b10b0200c00c441007140150070481942d0700040c0c00710b4a4883e8209903514000141450103000340492001c9480c07840e1440740600920000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 685872616 1250 685871366 685871369
    0xb07082a030d05070921211d030d05040b09130e030901020f06060a0605090310022101090603020a0e130503190809011505060c071d0a050a0504053a0504 67
    0x102d07000c10480d2610501603580b2426481076000c40d10031030000702c040b90720050f80401c540d48500c00505000e003403900c2491b100c0b40441d08920004034003903000c10302d2000ca6219901e54507015400742078200350191000304030f44a240190350034070000184d03e280b00e0b10741c50001e07412100c0c142420880380c140c001c0c1098036517111002d2680144141401c41d030224401046072806044000c143c1c0082c10b1510b48141e0f241c0d00f001541903814040d80c61303c50159001800101901202d04c0e600200c0a803051034104281c01c4103812100c5903078507041c800e0005032925114101070310504079000845650f010364100c148a49900020403a020200344403100954040e081203c4002d07986511409541d00b204c603a0885141002840356444d81000c20016801c3c0003008124888012040d5a2040e031103a942c1c50b6920749900c14802c80d002e030340e420031060b45024400c2d10780007504c8903000d0100b07003019240c996075410844440b10440e0b00c181c40c4090a0800820524070803108260b1030714030200c48520261503500207 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 685873866 1250 685872616 685872637
    0xd080906310509160903080a0809060c0708040b0f071b05040b12031207050d05040b01060e01021c141e1b0d1403072007090609060b07082a03 62
    0x7000001410199603091900c280c940161500d01c95640d60025803903200c4078030444000780102110040086000071000344985141d81c0c81d94180e5082c040005031600c00014103802403180103000d120b0004034010121011140e81c04038194039040701124450b1a482407140052044400c02e100861000d084440319045400071501003141c1041c107410b000d02d210700c403048444240c00c00c020802d22917540d440700d0354100d8036900d0041e08118034001038200300d450583d0140e0b01214141d0040065640c4203161041309207080c8003074441e001210a03a400b020762401c44110501402d020400c43c0710141c1d0064505225a405c5500640d007020341c0050140e5009003035030002440b880c901141021030002d07000e10407000b0b541c0c80381201c400c07100c80f00d4500d81000d080001044000b01c440b038000d8810408810300b01009801825207549041944004c40d00560300c2020160300b03004041082d8160181603605550b04040b080d5940d5070301805141000c5054041b00c040203412000c4140c10900000182400c0a103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 685875116 1250 685873866 685873927
    0x5070303111902012306040c0504030b0405030d150324020d060e1501050304121b02040f0b09010608221407080601170102030c071b0e130326060d080906 67
    0x42c8030031409a02080a200c011400045d002041c41420b01d9440a180e699107450b2103400d00c2c0d100da03164118100161015500ea900108110214201c0c40c802d540b0240b200d948610340813490356a40850940d240402031a50004401c41050703c1a0203404407100084a9502040b5661703c6d52031880118000342c6400461808220b03414410354080c20460740030b02e07002105103960889101044800a00c0c83c40504036404408009200607101d500920401da040c01c04046022101141480700e2060141d1101c02000658003d000c90b004d8524441d44102e100100341c00c0a01600742170101c0030407192920f000c403600c1207250000f5410310214185c0c6c103031035450104412440c0000001c6007030b03000580ea0620701c034408000d001d00094965600990303807003400c11a03410483e80c5440385160030400302c400c031f640f001c40344815404065004d0124051210082003000c841406107401c0440900700400c103a0041c40040c1c1c046083c40118001d0302ea0804c0000d01603a9196200b0141c4e0824600e1811907071342000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 685876366 1250 685875116 685875131
    0x1407030308060a0311090415060308030115210e03040f0e07090909031202031905040c080c091303050a092d0b07030e09060406050a0305030919060206070507030311190201 75
    0x2810003101c83c2100d4110b8503074540a81ca1600300501240080c1c004c50341d20004a189442c114100d000300e100843c01075001c10380300d624204444800f030850301c44c02ea0400c600400345140d10030807042d03c00303111110f8420000d40d035804640940c0c42c51250303070491001c15100d06000a1b41200c6402c0e520300c102c1e0306980d507090321a503c0794050103481d1101d42c01030100d00004402010445188e000d50b511240501390900049100030006040760003d03a002e458200c82502d0178403124000b00302c00000c9007419900104940b8000640c03038040a000f220003420003e00040b1225450302c6425010040d0030045a0101d2184440524048280206c5844a684e80f0741d28000240d40d103001c0c045d180f4664058407000c244808403010440d002c0c0000300b825900a544840104a50b114801000040c6101d035004640e5a80e01504011240318100600e2041000c000010700030b0560210728940c001415090864503a60749141c10b401510241c11003c3c550900071840195074228024407400c0340c400340e0000c00144 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 685877616 1250 685876366 685876369
    0x213031b0e0c090402040302060d150b161401020f0d0b090c0f03060d0c35060106020a0605060102070509040503130f06200a021c0c0902091503060a03140703030806 72
    0x14642031150240c0c8a901d0400511120410300040c241000000e00041c81c05449034000354071500000e952102c01903440240c1d6040c5403001d84c0480250612900c44e9041090b003100b00e00320a130b42101c00800710000040104100a802d405844001200480d0161280e180d115024010445010000c1c45102c0c090045004004041c0c02c070b5103241840c40443c0c0c5580d8843d0709000000414903401c507040700072000001f403040c428116400c4406601041401c0c00440850507402c0340803404510a069004900100803850300000c2c0032800300e43c4a0004903070741c2d4038500180c0c01d240040c3e10040e004040c6030108400c00501100030100264808580640030b5181c02014280c4003050044401180c500301994941d0000440c0c60b44005540c0d40841d5442d12403903001ca480d41c00d5400521000860140c4043c080100f00b03010749001d4542600c04508040041001843c071002144111a200c4000408a00300d13495504002e0b010313541103044030248410000046907103020070b02c0700303500091142c07001c02e0b00b6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 685878866 1250 685877616 685877663
    0x3030918071b03050301050904050c0406080f0c0a0803030f1e041202010f0923010e01060e0412020c090612150103320c01030c02033106020c1f0201020706021303 71
    0x4150583d80381405c681c2001c06101090341c0142c0283e80511462203410601e03926801898041e00094014040c6948640f0442e450090490304d8103100e200d001406000600c000001d495111242141000341911000e501d5002d401c8901c41594046040c03400b0041440800442c650340100c9941c001c016590068882c0b608039904100010201c00200221481c1810780e800500501d41c040390001641c0011036040a003140c1d00d84d07001c00f050031040c604000511200500030707041148a030000c0c0ca4a802010001011008001c0ac240c1c410f41e00c81c3d12264000b4070420260081046e6a1030b04c003400e58590501c580c00c500f070b010358040c058411580721880d6000000b00b4003106403080c03004200c41552080107602803c8858501d8045100a00ca40c00c5528079402c410150309906540030708500883c80001d0105031030030b800950555008032548556501c509640c0201d2000c81c02009401d2114098124068481c00c00050295800801e81400c071b03404500046045a201d4115500d480380c02940d809103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 685880116 1250 685878866 685878917
    0x913090b010524040e0105100f090e13050d0903060e07030201050412020316030819110318060c0d05040e1008190204060f0825140409020303091807 65
    0x4114400042109050007920f240f810030300b100344940c2c181c0000c0c00400c05070b0400e0b4400401c100c9801c00400c858204401075a039804910303c0c00e01d807018030202d0301070322a41c800d100e18154210200006501031a40148043d00c10303a02c40151058a030781e200c00240700d115070380400d558051407c48410b29500e000200c1300116035040e1169801e080c41e10760416230462043c1e1042e03805001d01083d20003045083c02e02c56000d548141340c01d0b525403248603414500540d503090080c2c1070050409005851080000550341d02840c0c4c81d10054880420074081180e501139520040d070700d44124240c013545160084080d00650350540c0c000011030f540d41c400100814524494445150080c0071500c043c1440f40c500e00c1042ca001420115019644031615001003038564001801504500c0301402e16480c00c0d101e842c40c2400e0304004651075800d100584041c41e00083c800d40c4520341d0303100c0c060110b440600c04d803130030040002c061000d42041c50300c000300c024000316150000030b91540800004042c1c004030089 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 685881366 1250 685880116 685880123
    0x50318070f090f1407021011040e0c0715052d07170c040305060f0a0b0f031207030210090602070210081b0f0c1e12040e04110d060908091309 62
    0x41d80b40c025110020100c2d0300400000a0300d5405149980000025043c041e0b0030550090030080f4110b8104011074800101070341c0404820401049440c030300240b4140c00100000c0070a5403045140350207403e2540100c0400040f509000401001045a100d80100b030440802c00c00c89107420700b2143c84055008540c01004178002544d424200071020011903800802072810600c0c00b81c031390b1505480e06500311070340288005503404120807010380d4003483e10b201d00d0a03078040c421a90000d0000351960020031307000d0b034000000b280280515208005240c1074040d500010415000e44d03041c004040c3d80910801d9016403c0d40b141019018858840c141c41100c0c0001d4410a1034104001c449056101600b84008100c05000c0040007410600006008225801d011000005010004c0d402c041c0444038000403400244010418a941e010308181d00c168001a125000312410b0001240ca01c401d84015251a00c1e203841c5800304400d036001070241400407100c405010300008805429201c0580c8000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 685882616 1250 685881366 685881389
    0x51e090303070305040f0b010801061a09010c030f02010b12060a060b04060e0d0305070203030310140a03050c060a0c14280f060e0c1309060b040c02210706020a05031807 74
    0x600c00c0c81c400c4e400740384c0103071090030390503402140b41c0c071084140301c2d00780c000115a954500d8100b01e015400001c44410460802c110f0f070400501c0c000280075505184005000e000202000d4200c0074402c0d80440a0010024190450211440900e03503a804088809104c003078074280c004241082240191801c89110381c1e9803030158051032080c4034400c2e944980072028010144020001a9000e00180d44540104031100d1011850302c1075960305600300c0200c0d180100704084042c404500045070840c06810141d50f0141d440680242c00c507801c00d03d0303940282c0110095030726840480004601d001e0b592070f0506c40700955001a5000c80342d0100604401081607051041550006180e50464214981d4034012307103081011450100341c5100042c041c01d140385548080e0281040441d104030b003480072040d582000b0303d44015402944c1c900c1204075030a020174103500700c0010310006904603244660700c0a0f0664694600e440c019003503400548085401c031907441c40310b400001001865500325171404012 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 685883866 1250 685882616 685882621
    0x302190306170f06071b1a1005100f050f1908040c0509070e011d1c03080a0203010b0301030f05071d340e040615050705070609031203020901050715051e090303 70
    0x5948070840c10006200a4190061b16401b058074941c000c140b650384414903082e20301c3c0c641000f1320300503000d41007203105610b002c07032908007958410800440104103040465480440117180c102c0c60148003800c40d43d0b0b8140301002480030364042d0a003030160b13108122000080b52502c013000280300d8111851b2000490140400065611070000079200c14000804043da03a5591000321704400104824182406481e5401900b010342c042076943c1c2c08580ca060441c155414001d00c080ca600c010311010700440358040e01c10043c40b40900c40c180040400c02035108101e2011018606d002c20101c2e1078045403000f05150701684003a51350b0000d4050f48000303802d41d030200b101200340d803440c00740070002d600b0aa50324404500d00b50300001080001c5000e031540c43d2102c0080c40c1c5249003511a030880410441580010030000d001c0c00041d1510101e241005038580a2078070040303030745010b201070250106401820b6890340d001c06501c10341c05500f040c18140148107500d80c0003401d404040d5440d062a5104100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 685885116 1250 685883866 685883881
    0x2d18030507020409020901080715020c100311040e04150f020910260a0609110c100c2607020d2f070506120609010501030e0c040c0302190306170f06 65
    0x20071030720303200900c002520041034000c42c140707a034240c100c0b07c141d902640d02804050100c61011a102c0140d00c010849075030060007244000851000d41c5d402d00d0744803c09070410096490907900a0210390348859103903c0d050810501841609000d4072000d845c3c003401e1070780c511050007150405000034001202003040b40f08102c60b004484102002d0308940040c0c500c500c2d5980744a03050082412250128949040c030500c1170803a095203c003c80c0303107202003200302180c450114800301c40c907200b04800076140522250959001c92103032110380d0800e01d4000c40075282c00c50040f05a0003030006a0171283c50418100003507403262490300c10088500c0700d0303003024803411030301003000218041d5420581c0c0c156903690021410310781048510700c1110120200300400c5040c030004d4a4010030003441c09114880200110544542030707400e01030300807a04d030491a0500b0303010b5011611321110428002d80300501000004004000e02d0203415540550300105075211100002d42803042507070803015040d0b503181d020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 685886366 1250 685885116 685885127
    0x10905010c020603130809030706080a0c0c030207170c0d060e06091207110d05030a170906060105071e1b181b1101150e010e1303020c041802042d1803 66
    0x1c004541c45c0c3c1b010002a481a06c0a100250060a164484240b1820040812800d545140c21140100181030328041c02103a4001420b030110780507880d020f15411080b0004c6410032003807a008a4200342642603890130420580d0241040b18141420307169280c41e2444c54603122480b68802049056090103a0000f150b14030f010074246030001021206129002e68800d801d40d003110440001142c2c9101a950300c05101110447e48160303890043c1c4038516006001814902543d8006070942941c0511450410040c100c207920780c1d0381003207480181540c1e6403c40d81c42d00c1e81d28011404081d1007500b480304140b0013801400840146000d450841602091048540c0740007a800340d542503496003003141c0f041c80b6030318080d005492180b0a819140d0304000c0d03030400114002d4110380c0c0180f003881c82e00004c69404186550ba940c000c50700850740003100301014078a00b21001000c0d6120745885165940d0001c42c0d800044003440c03201900b41c5043c42d8011030401c4400060560301454071590501e400244143e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 685887616 1250 685886366 685886401
    0x150614150d0501030f210c0b040201180b04061706062506020f07211e0e041406010201050c1305010e150307020606151e0d060e15010905010c020603 65
    0x4440007824501c500c1030000a4440a03401603138822400a26507041c4039180c44402101c24184c60b1610f659400044c00600081c41070101800501c45240807c046a104403010a00344494004417204280c4900c04442554003a100e10404620149a40e0340c00f08800040e80307100e0240245110304004580a0716201c600d401000b41d403003699040c2100002860038406040340341e00401c040d58581c2c0080c07070700d0000308000c94292070024200f491500903965100041c0b25440e0315012940302c500002d0441502c0801020180075401410902c840701c44210001c81640b01d003401364000e00c2980c0f01c1400441030b074803170a8110012071f4903240c010300241d401104021030005024010112684824491480c903030070a80e82040103030802c0e010700640f4036040c008880c140450b00d4034103140c211101604007812500c0c040c943c46000700800d18401052081e03001c48004c040c0400b0f082142e140283e0b0a00d84d1502c6840c0d0317070380403507c4c610303000c00c60794424900000820750144c0b1881c80c5480b60401c0300c80b0035405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 685888866 1250 685887616 685887649
    0xb120a060b0d1506090506030402040b041b0203070c0b07033908031509010f030204201b1203010e1311030d03060e090c060a110c0d03080103150614 65
    0xc9900c0050016041c100422010411400000d041c1c0404002c440034814240d010100700121160180308565410048039007069044500142040101c1e0208010780421700081200c900405403024403160040002c2c128244240a5000000d844885200c03090203a4080640002c0c040c403414443c0340c80d82e12042002e0350b24041040001140f8401c2c5403013081800e0812241c1810200520400e00014000e426882e0021a12410258103045400d909910304d44000b0384a0703912016030b1503000030121104080c4001d00e4100b079545012540510b080501080b03222030542c4281d1131010300c0c0700300881c1500d060340c0308411861707074030307114260301080e00c4ea00d9403000d96112810001c060007559040190600401498401017802483d200c4100010200103041603202e80000c444c0388280e54401046031003100e2281440b076400904118250f04c1c018071883c940ba00400084a0181451740000c0b030a4101c030720601c414184500042401ca054640f035101c1c05803407038403160318840b007440c1413080071700c03100c24 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 685890116 1250 685888866 685888871
    0x80403110a151406010e030c190308121e040b070c0203100c0801090e01020c07060c0c12050102070b060d020d0222060e061f0e0411040b070b100503070b120a 69
    0x440d40c8078a8001c0180108202c42c0720707520402100c900141c4020f103030b0b001200b400c003961140d450b100403d85880c04200716500c901d0003003a042d8140600c0c60500f1000e9500107099603100c4444603042d151090003520a02a825011882800c0d441800081c4500c52588000c4102003500c44001c240c0d06201a0700080381d02d4001d03085141d9940a144c844d14004418644d100551540f51039a880200c9d540000e42d140d2990041000b0141000c00140503c105c850500d0462400344580c200a0310705841074000303056050010b0400428050150003a25074140280c01c61407507a01e400c42084001c6040303900080d000083ca40040d0054500741030b00d07004c160a024864060380200120300400c071102a003015010492002c148038645c1005080103007410550060241d0503511544054a086503048001c2d00c2203880300000e01024468900340c1700146001c4088071b40b0b0724080d00d80944405400c03600201d8001914000048910300090b0310b1044401080a203807500343e982442803802c0000420b84010b864 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 685891366 1250 685890116 685890133
    0x4031704031b050108090d090b0904020f0d0b27071d03070303081008030f1210090e0105040b09010c0516080909101d010e281e050606070308040311 65
    0x1c40410059444101944084030240d040c0000900810000303000c80032140e011f5025a54981e8002c0405001c0d16004004903848901140002e400380c031880c1381d40c804402c0045045000b402d1160001c200740b02040380e040c6a03c1d1a40c0c0175100702880c1d81c07807080540d0860000452001c4e402000341800c0c0031880c40c0c101c0d5074400345801180c5459030315441100001c404c00c00b00403070380f00341d99400d101619403070000d14580b0020a1441d913207402650b1045400c10101408034203074a024451080c020074100001707015040c00c40c6030701402868219025600c40c10880c0004a5410041c4199585844a601c90030704240160300070101e14220310504071000351080102500302e0341c0b851022441500d081081105150505111955100c0140b41c3c0d030305102442401448203018486906a1041c015032001350509401172044218207054922520502e1170001800d200c83c0f01c0e84041150b082240105100680313600b0203000162040342d1003d00000c1140010400182c4500103146080c0500000c848884c1d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 685892616 1250 685891366 685891373
    0x181b050307020a02060f040f120206070b0c0408060c03060916140d020405132403020102060f06370b0c060c07021201020a20010b0d03030f02040e041103010b150403170403 75
    0x1b907105048250400742d003c05c04002c1f0103e140c00034400b0700484d5190000d4104964003142c0c0038015004010a5074980c100002d00e85e45100c01a90005e168450486407982060451041c440e442551b216000d4079000d400201021107030300541c2e1206000350b0300c424007640032103003030505c0c2d400130510307400b06507020070000845555a120b500c0f00004142000900c0340d8403000c4010341c1e505021894480c003406142c003007025030b0700070038011f5001900f41c0004040d07648410026003c400300c2001c0c0407042514030f03102c5540c00348000c8020064071200c0350071a21541c0303070100c0c0d00182c0505400032405520410020741c180b0560000303032024a1004d040350b0301150941e1201404ea17000b10f4032000000c1c01da0f480c20a4441800080d0800e1141e4440007000442080c8011510400014402a040c1603da004e225504001c50781150010442060b00b144203080514000410800d5001014802c0d802d1420700c4000e80313405040031506241d005801d0b498039142da51042c00c20428101081d020503130620000010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 685893866 1250 685892616 685892629
    0x913060b250b070f2f06060411160302030c0601030305030f0a020301060f0e060c0115050415050307061d060318060c03131e1704181b050307020a02 65
    0x1901480c1110307034440140c0082419000030003003554074200512010580801c0456040c0798100300a0b107411084154005000c0c4e83e10468045a54001112004031404003600e100104412040000507a006a26001c080109480b807092000050400401000501515449509400501c0b900649080c6100c83d80c0060801c8000d90059007c620000308001c0ca1100c000e0b480759000c60495021808d550403c00d00402040042ccc1c024820301010300140907541c0c0d9031409403110b18034905c00070300149440400300038400030f26102c3e0768002e9007410b0b0225101d0028101c41801d4400c058020f09405250210441d0140c40b088040202c0003004924144241c8900c0000c5206042400c04200320b040000207a528103e0300424001d0516130034070520580711143d01e00b02e0b0020303411031000481c0b4503564410b00419125054010101c00d6801d15800d4004142805042102c5402800c4042e0300c03100750101d025190f81d80f181d802c0442c07859400000c02400392001e90303000300a51049643d4a0195804503d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 685895116 1250 685893866 685893869
    0x61320041503050903190804240e0f01090f080a0306080d0302031f06020705150c0f010b0910030c031203020c010e03040f08011116140a06291005091306 67
    0x1200710260401e00c1015094022281c10032002070040d440c02800003c55031100d41c048480c00200030740c590100d428018101c50566101001840c00c0c0484c403126210709008181c40c0140b040d00d40036070840c1066844c012710401e036003181c00601004040c0c200b669489080c0c5d020350520010b16550714400b060414080000603250034084c3c80042e96400d02400304141e07080000659503010b078609106112417031b4041500e508559041d60070a051045070040c40d202030151540c0000103106100e61508200d405410016905030260741011040c1c4850249256860881c04081d03c055812407040000030245042000e8032062442d00500301045440290b094070000118402181c0c1301181c244205020f8241c52030007015900c000300465032020ba480300300c5010b820380041e03074032088003801002d02030903e0062980c0b41508080d180b981e03107503242000061400b114492031030480e1900e02c102481e550b14085d00d0a00e001002200c0045d000c0f502180d15520011415400580040300301e1100c07807580c06402c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 685896366 1250 685895116 685895129
    0x18060d1208061f021507050c011b03060b0a14030c090306040b010905070207051309030203040e0109050109050a05010501020303160908030d02030417072001090b03010312020d02030306132004 84
    0x12080c00c00d0410800300b03d1800591640c000d0444008521041d00081d965031200681044000141c0d201c3d1425160360083d15241d030001d508000780d0020315000c09107040034800c001e482c1040ba46440b104049034038008c83e244500481c0c0003e02025805034000c026581c0b001e00364101c0c03072400e80300d1000320b0300380501528104c81c070040d410300502401d140d074000c4a510112501c02020f1581c5410700046100540900415035942d4800c41d04041c544207208030b4001e0115188002002d580d10780d0201c1c01003000744a924010752904000c038402484600800b8100c0d10164011360440c0c070b60140c054642c203801001e1901780442030a0000fa1250140b000d841040003404005860b072404d818107400380281300781442130000c0d081180c3e07000100f0500d00d0004003010002031115204115005807020700c0300d6009400c041001000000402440980b031212400b01c03542610800a101001a6660700060b140c66078005840b1000c1034000c08140d1103009800d510030203101c3e80e625441000c04080d400b94002c176 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 685897616 1250 685896366 685896377
    0x50d0b0a051c0308060103021e0304050a0606080f0c0a060903060f060f060c0212070f0b0c030d090609060b0f150d020702062d03090d0e130c030b010e060918060d12 72
    0xe2083c190440b01d01540210282400d510b001070146403001c2810000c4240074841d54040003240500808214098519900180801466850f64603281c2c1d44d18640301484080e201c1c0d41d00c0c0180a040108201080710500e8952007161420350f0f6941c0040d00341e4482d200c1e0b011355180000594601000b19080003480a034850002c0d800407401848100ca245501000d141e604c444004c0040e0094804858219170610700c0f1141c903411180300d0741d070440c4542507800f000c031390a0580c08410b02c00d9640c802d004991080004010072a07404052001454103d094281d20096426090350b0000c0c50700024000300d0a03422006180c031665a0000701c141c0c0185009440105500002c0c03110a030401c140c4100f0039042c46209815132078101c0c201d99955214981c0c59080103014191400141c036074040c000c802c0c4140790018014034907010b40c000c00605c03c000c01180022034006001c642030601c0740465504107005000240d103080001141b00f81504041e140700c1c2c005c20380d034440c440403032032982c0c42400420503907698 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 685898866 1250 685897616 685897669
    0x50403120e030f0301090e0a0c03030801060f1e050c0a06090f0b070903050c0f0f03151506040302030c0d051f05060306010e0c07020d0311101508010606050d0b0a05 72
    0x1003004580300404496801e07030081060001403000003090764110762811901003054a2408021420724601c02001404104885404020141c2044007207060300c0541c0d0b5045030340c03c20340000300d441c038418840c0c1140d00c040814900d00c80c00d10800c002d00302e03030740c5c940220ba5001c191541c400c01101d4a40005803500220000002d0410036400c0c0c1039134000e1450b19042480324107548442d80c07204030000c0424030603560035010840d1629030700d07000400104000e00382c46c000a201c40c181e5081035800c0303030340c00c16040050500f5101c1d4503020b0241d40580703070041d00406881e0b2101050104414600e10242c802d0311a080300e82100d201c0c002050010010682d80100d40c070304208080c0351a003d81030304110030411981007000310030413450307041c0e40c0b07102d40454a00006021078101500c0240000c4c903044081c0c0240702090103001c95580110205001450313090788425030342d400103822a40e0501902c40014810403074018000d545401c004640c10005001d5080d00740c1d60302c0014080e2840844070300c81032000f4900c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 685900116 1250 685898866 685898897
    0xf03030e1f0c03050615071a0a050a06090c270909050304181e02090112050c04050109120803190b100c03020118150f090218010e07300f050403 63
    0x14140b41e14589003014030690800800150782001d07413418242045501184040a201a440c040c1d200341581c504850b1080c1000030815001c2c010842e40c0d0401e46040080014000344e0320702c0780380c100400580d610020410f034105503c40404ca10254031101d0078040c0300208172000c0d14858440c0c2548103100840c1e031549840d04502401c21241d2a401a2500e040c1c02c0003c03d1101801c0c40c520844036880c016960424080180c4442c104c2c0040c0c0c401d11458a0b00300b01d10800084003c01c1590700980301d0091141d0703900d19030fa4003050340c104010a120360034400b292518020001411111002400c04503000d030802020550342d800f48001d140025900d400d11a0a00d40c080c0305842c01c11650b2411500d0940c090740f2810685198103880549460b030f40d0918405080090740a4045242e000b00711140c4291740749103180443c17100380607294121607000c020902050080300c2201320b62a00100749a83c3e1040c2c10340d18500b14980d00f142075034250f114421490905101d01c5a240b02c1c602c03a4644141c2c2030b00914 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 685901366 1250 685900116 685900121
    0x11223070806010f060507060b12150915060d02060c190303050115020a03090308031e010b040611150708060a05040207050f10090b06060703140a02060106030f09030c0f03030e1f 78
    0x303020700904e034100d0390203000742c1307900004407034810b5040000803451f00220b00202e84801113400c0515024040e0480c902800346041a006024824110481300c0381007030201c00c4180028142c4009074032804000c81e1a0060400b00050000313841e01c14103603210700c0045c94131104070501c40c02d0124002542c5000500070480c00b0300c1000c10180b0f0501c000c20b5480b005607005480034090703010140c441240403001a404010095218480e425500341070001c0d540c0d0703801c080040350440d000d500301107458102501c284490000b5001a940c40508410103580c552100580303503030f8000341500c0d400c003031444404030385c80e1154001090410702c158020038019000c0b400960505078002d0035298000d00303101d04000420304130102d80707400c00300c1100e9052f507825841c9029500101c61100e00040241701056080b12150017060301812200f01d524284030070900016204226070b007819005011031040006807000c1030548000c0c5030103511034240087c800480740070107890003c80c80f0002c01c0d000d992640b2803d1418a60 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 685902616 1250 685901366 685901369
    0x5030915042316030507090f050709031106120718060206070507080d2309070509011d0703141f0e0f06011209020901141c030801122307080601 63
    0x60042501c0c10107079209074020040007080d2020140b040b5108603208018442c4400304240300581c0341285940340380050f00c989140c070900c03012500d4042c04180004581c044c00c2d00c210010781e2003405250540d9220300451400700e40d09a045041806003102520545c040c45002d0681038507248a102c08060608441c0080c640200c400c542000080c400015084000d42e0b081c5640900116142c20310984441c2c014a001c181d44508403000e08100002d066034007032550301400d4042e0503a044240c50b1420b1000c02e910a02c900314601511003043c0d08000301c640800c0740c108050380380229041804115803c80180700755084602c0d10581121000110104010b07070340100700640380e81c011403404a4244180d544001c0003581800400709030a0403070440f0303500603050254010811202035860710f42d03400c4d44600d01030b82d031402100303500b400b4000f1003400a0420303c0035503d035031144516802c1c4002c9c0c1250148204c0203d40c69196400101c1165111004038000d0944032001005010701d84020f0500e8114103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 685903866 1250 685902616 685902643
    0x10c030b100e2b0c06051e090a09020702060d1407030e1501211a1008030702030a02040b0d021302030402040b061315121407030e0115140a030210050309 67
    0xe803041c030071054031407119000541440c0c041842555064114070f80800207901001071018000480104000c0d8100018000104105005a00d81c0c0010b0802c0003540c842e03440459846025007500700440102c1da00100300f0b661000e044e150400d600600c000c5c060303800d085038034607440c030551003009100d6a042c4504200c1e10102d200800741210010707840b011a40060050301744501341c0d5809210b42c1440c020400001603480b041c070981480020231211040d800656440c60740d1088003800203580200002522800c58008001e412a1400d82e400c000084c100d5009064011070a422009d016a60340011405000d0010001603520b282a10400080724402c10465110384009d21201c1500030303011403014185c95603500119205440004e0075124020343d501c000681600f4400a400c407054038100c1540a40480c0d02d09002c24800c01035054269604060030786c1541501c49000c0010032088042e00a000b000548103001c41d60300d07070b0041049228152a04030110700000240010a1020801003441010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 685905116 1250 685903866 685903877
    0x60314010b011d030c1903030201180b180f0d080103230d05251b0531150f1404090b0103020d020307080d1701140d0f050f010c030b10 59
    0x507001030100d4a20001c0c0e5031101c0c0310160b03c020b258804200114811400510051040070f01c03413840080e00f07102c0e000440040d42000290403911070b542e40f40c1c00c01550300c44114a45a40d480c2c00c0380e200d41211145030041072007588524101c60300184414100c6a03100d994042496065040040c800c1d409041c5c21b403450b00381c604103815044000314000c0503100d514504103503510005200b05020001d882d09486080b0502c91b403071800c110f0020200c204001c008580303545416980c40c00c0020840002e0050801c8040415692450907100c552110034aa030b41c400c00202003500c0f48540980c080c0c181c011180c50407841100780b20b07203014900d0030007081e20200c07028002c1c46020b80d10080b0000d41840000d0155040c04041000c41d6421b000c4003001d003802c2c20880e0844559560020650a0340f100c80c8a03014041c1c0002250980306405c1d445000f600203000c0c07800c807903495030b0398400a0244041c00c1e1080d014002c0c00d03d649880c00c0c0580032081e0f90366500492501056002c020f807480701400801c05014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 685906366 1250 685905116 685905131
    0x90112030801141c0303200414030c0603071407050f0312010902041206050a020702130b011101231b0415030e1c0e03031c021b07080a24020d06031401 66
    0x59980c0c03060310400e03c5095001424600a01c0e058002d4008039154815000d02c04441c03000c00d80407d800f0f0b00c100d5a10f290380d081809a600c0c1403585a541640009800c80c0042001074401c0740540078a21610b003201102c5880c01130315456840c2071400c6003680715600e400c001000280390036034013800f0b030240c8802281145000e20b0902d000e2805141c5a000070602601e407070004004407d81d9064a02300c5401030325241c03c0c5403101103610001d00b003d40119010460759402c1d0030f8560b00510a0401007110b06042207180d01300b00030b450258040c01840c0c400209110360340156403081c0d10004e04005e009900d05584d03c03540c2000c0140540c2d18000394515590b105008411040391010b80e1004070303400c0f508003d8821000007012904601c550b618481941425500f02425241e03141c2c010464106000c90202412030b40000490b2201854071076107601307600c840f0703025003c111344440c00c821155500c18240100600d05641e403051f07800c8005405000303561078008009002c1078412000e80c4800c040b00810040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 685907616 1250 685906366 685906369
    0xa150b040e190e100b03010c050f070209060f030a0317011205100902152715040b03091018140721060e06011211010203030403120f06030209011203080114 68
    0x45001010702c1d203584405402c08100c000258014680c000c0d044054405080450380758401074198224a80c0c013170b40c6803c01c0d0320800d620410603902c0403085440040e01d040c010f03800700300c040c12024003019403084c502d14103480513a40402410800610a859440e68003446040502c0b0326074059100000c40040f1206041c0050b002064031144031051140026640109002181c1628100c1c080d2a10640001030840c22820b0640c0c0b44601529595120200150000c0c003405140080e6403c03000481000748402d001c20248031300919408001d990854502070348840341303030081d1010180c00121202840e00034000703202d03015002c000b1070b030f036904000c00141340350030015500031541030041404211a40c1410341044440d400680100900340226406961070b180083d0441081c40c0e001c03070b264045500503603103e50021040e244142e0701515144c00c4600310300f0a0300c0150810804080707003950380b414080016a0ac60b000503003c0c00c808000e072030701000240f0f0044c04104041e040307038080325542030341c111a5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 685908866 1250 685907616 685907639
    0x1008121306111006060306050a08160302100e1801090b04050f06100c050f031902070503060f190914071226040b0f1201050d2a0306050a150b04 63
    0x4941d0546020588160a10301141c201041e4400715003c00b4203100d00002c040343d040e00900305680c0c04a4420f07503045d0307a03140520f41e034803c02441c0e8903214103410010000361034064030151104245007001003002050300300085000702c1752582d0f000707030b41445401404240c07518071034403021040075034003041242054001411104030090031240b14120304100c1c80c4680c1d1183c0e5514032000d41c00000c450ba50b005c20031280c2e8803600408400038565600a19154900b880024003a040350005000b5000c0d0380c030380c10038200320b10800401320824002412014020300c041132088080032405040f185801c01e4440500303a0034062264449290084156441d6000c02c0310700c1000d004800e003111141088070f60100c0d401800c1d000c2c1e6800303e07500020200b20061a9401d035402450321403200c5411510703903a2241c0c20004c0805600d00080c080500d0f180c40c40101c10b160300424114078031143c90031502c042e42c07a900e10080c1e400031513280d05000e80b02d0400d03500400c1007803d1039015120403600d090405003008000c074803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 685910116 1250 685908866 685908869
    0x51608090618010e0f06010305060606040b0901030504020d201c050309040207030903021e010f09270b060424030504050a030315030b07030504050d08010605120a1410081213 76
    0x100024011407100b4a1000d40c0b00403020583d0409840b1902d03602076038152a044244800e5415010390400603400303141c50804c5505503101010694107100348940114020480200200e0b004441c5200141c04202c00d07003940c0700d860f61010104450b140480c3c0622105004001c1d0361000c501c41c40b940c02000900c088142d52100348207480041e03e56066040440b815821680702a41002260f000305a402050402d0b1406001c400e80342e0b80f031030311203045046424518a00c10b0b425840200084440494140340000e121001494008500002c100002429650096000f032515a9450407203c2140c0308e048031300017110503541810002c610341a1070b450380f14000c0703400040415540c0c0c08038101e81c0700051001c1c0051078000c01040071134541050094020701054405407100d110f01c20305220105e200761040760503100f4965a850603c0c541d0f8043d40c2c003101019000381011350301c1d0450318899146850055201d685407581c090402031510004038106034101c101c110784034104115010220314001c56020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 685911366 1250 685910116 685910131
    0x5070303020913090b0f0f04020f060c0a080f0a0306081c050c0f100c0305090109030e04020a031404051c020705180c0c1209040c09050d030f120f0516080906 69
    0x41e80c030b011550003e01c1c1400410301109a1910b840310390024014001c950620800c00540c000d031030368440030140f00003001c0445000b075000790020403940184c2007030360280100302402d1040f20030440c4140c2d5100d856400030140a4801000407660f08426581406000018040790001d000700d404080c5d12a401400070340c0c4040b00303020000810190540080100e440e448003004169665641039000c40d5000e02407020360b03c00040e003401c0c0803c4d20f040040c403c00d1092135040e00e9034442d0420100030f00c806500500040780c20b0540d1020340484402c40080918429407180002d40401d10308040741c3d1030b041040f00080000c540c0000814040c68890341c01b0707080d1408081d00307408030b01e03560711100c9062481041c40000c002e0150207a05500380c031020000d400c1d00c40041f9010f01c5148a068000c44038923000b03224450b409414101000302003405071005021030200792501205002d2040d42c01000c2c1c814128043c4501a61802082102c03240e004081070703401158035010846007050320a0390b43e01c18014040d42d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 685912616 1250 685911366 685911371
    0x9031d041e15080105070801050a140a090b0103150311150324040902041a120321060a051909050f0705070b1513060f051203190917060907060f05070303 67
    0x2460b6a400c0c2200000040ca5124000d0003141b0345104020300c000d10a1051a00910f040030006c01c2d1100e007140c00341c10040303021b026440303080d14001c2d101c40a010b808144605066450503041c50000400100c44095405100440308007180310041c082c0115080d100c1140382c41c828024001c1c00f8141c003101412000355283d684024540f07160000b0000c1c080364030000c3d84075180440b12589140c00c00394042240808554804152b518907101d141c5a104150010740c00900f4000801080142e41d22181e400c100080c0c841d40380031b41c0300c0b40030807040070642c51030107888044003000f008015a1801340ca03a11030311100d0414500e041080000d0064042e03020300502c0950603c0c0012004268190b07840a44200103040308003001f0824141d60080c200c40c014450360103010200800d00c2d0501c560940d0528039054001e5103000b120454480361013625890b044200320407000d0000d02411015842c0c1d0440001902800680c140705080a00d8226107511020074400d03490002e102c050341010a450009806d030601 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 685913866 1250 685912616 685912631
    0xc030c0d0f17130e251209081b0307051011030609041a07031d0304030f0206031302040f1416081503071502072309010501050f070609031d041e 63
    0x7000101d00810040031280c900d29000025020340f41034100780150381c0a035103071180941903010403401c000003001c05070201d1200300c0d0b01d1b0504110b40d8044002e040c00f42e20110704080840781e4034403030090001c5482c1c1c1c441d0b0001ca40e000a0090501218100a490350350070040c0ba1448501c42c1014080105030030704c611030510026040c4007440c3c84502c1a624660191a8140303410803010b0000d01102411143d402041007010000794030000403207003a02e4119052074160030345942040002c1c0c5c402450021299032003445100142c40d20b000380c03481c1190030140403c802140086c48844e41d6801801c60490020170700065a010b50800300454000b02140483e0b501d451882d40824600242c55018071004e02800300c1c0f80402c15400307e080790642e00b40b42c040708041c4d801c5a48100f01004a00c03000c5c3c0e4054415001004258000c0c4010180e102c405a07401d41031070710a40700c040c101c8010f10f0060b008101e510241e6a45106419100540c9000032281041040d165800505c00603808088000300030341e59400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 685915116 1250 685913866 685913903
    0x9030e010e01030921090812180a120305030f06091308030603010e030415020613030e01050d0b121507020d020c0f0d02060a091401090308030703110910020c030c0d0f 73
    0x116840882d0005c030b00e1103050282c0c0422000701c9800254010004215010220700c0b45004034180084440030054203003094101101ea25051a40c8000359610410305000000e807602c5031050011054082e8407050f441e86000d03082c01082c0c404c01003099129400c1103040003c0280803006050016030003107083c584135568000800d004116014010005100204000818503040560344031080e4203613090f200142c5500c2c01e4408a0f030000c0d040100822102c9030044c0c02d551107280500b6000d00000c40c040351410381107000c01c400c11040c00c18070929410a081001040d030000c50310a81003c81403004041c65420351800075240e09a92800314460300300c003041207901c0d0340d85540354101c89030010907a40d03440e2500140a4881e94062240b440441a1466482d00c0c03580074a01b1501203030382180c07000c2c2c80c0d6901c200044006004007101c82000410510003581103407100c006000d158585600204003100003141010b29050301d120080b441030b030542c43c0410008600200052580d44c2c03100e50501d00010544 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 685916366 1250 685915116 685915121
    0xf0d0509071a0306030d14040e090106171005100f0e040f0209190e070605071103120c07030317010b0406050a1b030e0108071404050607020604090c0309021309030e010e0103 76
    0x384081802e4919514150415044200550040c0e10850499403c0340c04141c09a4a0094400c0e501048030f10a102c104200e41025180682c0405010000510240c49040d20103100d28440b14581c142e505c010300783c0702d20041c01e01ca040e030001035440c0600c0341c035440c107500624103454a0141030a040c19032404201004604814040c3c490390080807100710740b0300020860011440c00e040c00d8401d0742401d0116a240c400824010306850b025542d0500d45445038480d0208824030510359034151141104002c1110b1040000d0b04c1000040c1001d070000b1441c6044c01815103203020412100700f0b820000402c05050400122000c44d5514101192102c2c42c0c00002d80e081d003003100c218050302d61098248020958002d02500e04a03109885800380b03a2500d540407124412012480d6040c81000c00040c07050f45007100207071440c54030081080c0c0c60b05071110101015200301c0040b03000801c4d202c210010862810241d003002112a40c001003240c640552001004a583c147d62b003410700ca5070100381e115a07403198 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 685917616 1250 685916366 685916369
    0x60e0c0c0a020607030e18010308090d030e030a05010f0f0501050a051002031b060f0901050603062a0c0f071703040317070f152301180e160603110f0d050907 69
    0x6000c42c2d1144040e00340600b000d11446d078a1403080313140503000040000017802e240e060b41e40000780d20741004503000500a414410007019024043c00c221101025542040980007a92042001181c4140d041d0380803000d8a4001e04000a21030a107001070040707844120341801203c004640c04a8121f0b150181a4214841c040444561036042c2c2d8455076200f1000076681e006040f4022000859075605006d00c0c00ca403400d0340d680e075158001c0c50204900fa9010203405c0c3e0002140d103400040703240c1c0108210301c245e000000450071900010b50628110383c003444408014482006403030001d03a4101d00043c1c5a100d00c4c04000c2a0340003071030003170010f00d6401050328151540305501055480f410f0410008500c0340b010044280c40c01c10840d88662641074010204402841310705030780690038040110f0341e1161020900f854603a44d6494034507004000c00908048a0b2440460078116003042cbc40207050b50b50700c2c03401d65400e80e41005001d8010000070201c0e0881920803500203680d48070002e8443c00c083d0907 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 685918866 1250 685917616 685917619
    0xd0f0b0d031110020403150e030c010c0306031e0206070b0a020f0f070506010605090d060f091a011e0308030c03100f080c0405010f030218070302070c0b04050112060e0c0c0a02 77
    0x14036030108109500702085021440003902220b0038101d00390748080591095010043c09191501e8407400001000e070440c09030340382c6500991742424405500a400c4a105c0c440000c0025200c1d04c042003400341141011548101c010141e403014040f640200345c541c480c080d0020b03e0541101c0c0000c0343c20070640d044d5001d031000c08c12050f54512521000441c19000040299401d0040da03000058040c0214204e0b460304501409010084541d0b0722084014613003010110002c0c2e0322600c030040000e04200340901480c0e583d051005240d410905a03400030040b03602d0355092280c84003810b0010031588001d880c1d00140400301c0b42d6880e91014241075140a850b07008031003048491101180503400480c20300e9016009a0f01049141e9841441c0c000751501480003940041002c2c900d24103855019007540d40c0040682801761800703038540d480f5590200d90317a00c032882d059004601484030350781c00b090100d207501000e18203108090600e4450301c50850081c0c031034851503030006440400e00200b4051000c01580 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 685920116 1250 685918866 685918879
    0x901060b120108100b030c0f0109090204030605010602070e04020d1103031b03270d0609080c070303020a02010e0d17090d06060801020417070605090f1c11040e0c060d0f0b 75
    0xc2501d141070044800303000d0264107014a84c4c00d0b0803a20068440d89840b100d004004100807011401030001d400c46900081d410040e80140c04030b505505400140021807288000084a40c50001c000703090407260342100c40c444a6000600001d81c1e50508150b45103900031903500391801d09140002c4c99072003030003008a071071001020001e10103140400502050075400c10fa02c030340b00186414039a01302c00751103046540141085038280110b40c00354810501c0d07511800046141064440301113141044a178001c6006920011400085591000c02001500010b0318201058031803a81c4640c0708503c140c001024404c40410b41c41d61550324100c280c02c105070088000c020317151701d5076860b502030340c094018800c55425102120b4880c020000b00d503001c584095481e141000030450802c500a002481190b500525041e0049106c210782d6000398003480c440d903c4619040005400e000075541c003130b00d801243e80c0150560b80d034540c44100884104840300d0301d0005851350b00880c02001403d03159031280e040b00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 685921366 1250 685920116 685920127
    0x509040302010e01060f050a0e1302030a0507140f03030a0c060b04060905040b01060206010e0106050705010605060a230f090f130c0f080a06050d0219080129040204060c0b0901060b 79
    0x540650040f0100007880009004d025140c1715040441040780c41800d4000d04070502c1040460782101d4441e030440d40070504071040c00c0d126000a131030300745000c0c4141c0c0c158018140410403084044e03c201e4000380c007a642c03610543e82d40c0000946078019555800300b80074043d05a4001c2004507400b0410388140208100109a281c40d810001040100d03001c580002c2590b0004c141203000044280c12107170b0010300940c07168207007003084401d5088550112b403990340300c29020959a039580c000e032002810300d030b4404154003500c0c03480c0191001c0d400c41d075030b0482c1800c001a6441004580480f002000c09960080c01c00198802088005a01e40044035a0501c3e0604508048e941f141c0300001d040420b5803441080d8881d0418402120543c0c421036501104007891a4010304101040e640c0c0f16801d00d110b5500c0c0c035500d01d121402d603440c008140041200c001402c5416200314002811900405c0d030741141043d09005024000340c9442401410001c0700c0300c00920541750075005600503016499040d078450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 685922616 1250 685921366 685921373
    0x919060f0303020c03151b04030602030114030c01030b090a110d0203010602011d0c090f0403020a140606100302070812280f060603090f03051e0f07060c092d050904 72
    0xa1481e0004800501810001054524000403114084aa0004041450346501c080701880000742404501324500a1000001045a03440510700074100055184030f81710510007010f040c40c0f207032400f482c14549890014845501d5142000368088643c04000990340020120a00d442c091151320440403070001002296031030b0306420040e00c81001410a24a0820a0a240f525010212241e9800500d1000040e10080c50103403410b401c54060f0050300c4045815460f01035017004031900c040d80030f910113070900c48141844a2400342140091904500380300b120360f20922584104403088209d4000d40d400b1440c1000c9907038100703003511034903059a4100c500c1c040130308014241c014907524000d4908080050388900901404424541c0001d0210703c01c00143e0f825030340b60300704600f071700c840c07002030035843c0c00c614610f03002002c042c0401c841c66038643c0407501d02542500e04614484c010421041410407400200d030044c040c4410640d8210030316403000c0c1c075811900035050760213075500401c50000e00050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 685923866 1250 685922616 685922639
    0x303050d020c0a060e070b0f0a0305062e022a1318060f06170d0804080417070312020c0306130305070804030f150b0609010c0203071203050a090501020a080405091906 73
    0xd10b6017030142c49542e50b030350b400d05069000d0119040e603d580e00300480032030580710f50b21495015400a00c2403031500036221452050441c1c8003d148a61080d5258060322650100220028400b600c0d180d1850850340003022400750055141150042e42f6011141e400e015003504840c143e59464131030508c0d0001e032418200080c1240d05031000c211807906102080301c4010328442d5803101c9818000b080d403070242540840f8041c000500075103900c01c00303100204005c01c0214408130703070402074002443e040e411b41c1443c0715100741c03203104023082d0751045400d0340058a000c03580b0790340031582034404a50114941000d0341c5911543c9002859804000303000300c10050b000130400c0a02d400b03002015522a40b081104089644200300c1c582d0020083c0440e002c00e40c46a11a0030740688090b0507280380c15681e040c03208111150100032004110040b5203503003040d60000ca200e0041c42c01344018145081d09444040b44e900c1580a014080c1c4010000500f51245901c1c0c0040c003645a90300410001d9074030311017001e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 685925116 1250 685923866 685923881
    0x203030c100b0a03032106090507111603051e0f16060e01080105011209050c1e0907030b0a181b022107152007030521040c0303050d020c0a06 62
    0xa8071440c10030848101d08000c030501c802c3c1c1e80c0c90385030003d02c5c0143e00c400c81c80c80100001e248044686884e4049001c0c00240102401048140c4501501c90700e401d030000c0c1041d07000e072100340c0d505110000400c080303640054528800106c0c100d000c0910072084881ea0b040241c04001400c19105444d4a41c040c014020801000c6442e10341e00c1c00b403102d20000045405490a205c0e1500040207038032102a900c0c82903102d450210f1140c012508280180404140c401035503000b004c020484074110200f46090072594260b2012040c42d08205002031200040c8001c1514003515001381c01d00c010034002100b03a94446400c00c100d240d00454090408140290745080e0424900740041b50740c0ea016816203118002c0e50304c402e84c0a0a03014524841600c202d0040c41e0b030200c0200178201130f0000441c00b800d900300400100c0c1c007070340e5010340d5802c0109492445845014050350144682400c00021803c94144001501da00d032505907503603c046045000a8050f0310503811841c010108ad031000c00006602240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 685926366 1250 685925116 685925143
    0x60c020c1002010c0806010e0f090a060302040e06040804061d090f1603062301030618090203060f0402030c090403091a1c022505010204030c140307090b060a08130203030c 75
    0x40000c03081d114201d003a1000070500700701086106002c11036039802182c00d4884110040c000c0b44640b84d0481c00141100305c181c800c0580302da9100401e1040d802e00d8014130702c0c050150f4006180c5070600b030342c41300110311403481100c04108518071108000428641030b01d562501c000d10340c1c002c60505201e01e0360360020a0361900c4000f0020200b80c950140030780500303001c46040303c442034244c101c3c101c10f1402168203111454100b590f03995000c55510030f06941c000303451031403440c0025029441d2044c90701e000c00140890302c281d800c9104100052b9000180841c085c1c105441d41d010b26259071030306480d0440e80c0e8024000044040d82d1402c1f1081214020380140c1000ca5101c0502c01d070540e038560100d1044a664842000814202c1e103c02d001000413007200710b1040000500d4650b490321031024401540c4c01045060850b80408013552504110750400f91604080070004161100d000521601c0744044041c203000f8140d0004201c0c0064030044100190003400f40d0b0780d6485603104070303900d518612a565 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 685927616 1250 685926366 685926379
    0x30c24050a0f0501050d02010c05010f0528021224030d020a051905071703121008012405040b01090503010e0a030215070804060f0f091b0e15060c0a060c020c 69
    0x10001c0c82c4280c080c80d4129030b400b07800c42c124042c8036001111100e086c8042520190349908200c00282d0b2540b09030f41c4a407440480d02c650014503a200740401180407440710b400345005115180c140302c7c0d08088a604112000b8041030030707140700c410f60a9145602400c9503410f0040c1008500c2958020981c030941c180300d28147d540b0070741d40342c00b840071403140201c000d8416408a2003d00180e81404090320500403080b048904064006122005580044480e901c020301d080e00304008030340c0b003401900c941c9010710300b0408400be4007039010525400c15201c8d441c811a201c400500050f40036001800c0075050240080c4001d120801c4020342d68074172400c08600510841105c148084032204200c1d0084185a403a1110703519a500c1d404c01412507108072201c01aa543c403500300101a910a11600d00d10500d104603081c0610201103a119045500140b201180300e0104440b41007402e00b00c10341088200c40071511074801d607026928180f91120010301c42854800101c070002d40010f030901300e101084456 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 685928866 1250 685927616 685927631
    0x30a110a050303040b060a0905150126150a09050a0225080f0a090b0a0c21021f0b060c010203160e030a020f01050f0a080a05070e0607030c24050a 64
    0x145645651400019141d600140040390001d00c50307103a1640c00200042501e4a515150b0000340211902942c0aa111000300314040e109540c01011028a2003010350f4500c00c82c22144454680091008041082d02c0f1248a1500300f141d41e007004560150409440030002840d00311041c0e1700035840880110b01810707102d08281c0d40b07001981c80450200b0303030044016003440f228684d02115a04603a1102c4240902110302040c20503001014115902c215501e804514085042a902c40c2e02c101000402d160040069450380c41e800044248410100050003103031890780344440d000404079542400d41c002c40c001600c9941490540195008100d442045019524515010b0302c140d400c5c0ca03402e603010f400910300c100151501000c028100401030405a01c0d0083c1c0205803001507204030390f0b140100c0e00c13040034000b080700e0394490701e0381c4900e4034100240300b512443c002804900880c00c0060400c041d07006d802040205540482c0a803290034216003c42440c02e08684000e01412540101214a888007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 685930116 1250 685928866 685928897
    0x50406050616080711180a050a061409090705100c050c010f0e040b1503090a060b0d0f140a0c1706060a0b0a050a0203120406050105090a05010303050901030b010e12030a 74
    0x12140c1110120b20541c1800c400341e56200072a4101040c159400851039225440a844540c803c8041080142c1c0382007040c5450700781c10084aa01400303850b0901d02d030207070510140c03003407103003c0b82c0c8100102d0781b843c503e9071190a15850449144c2005800c10b980b90032803022160098400c0003524480c205590700302030707440f00460b49007a0b8030901c1c8001400c485080c489038240307540450a0808003818034400444d040b00c00e14003c1e4815036000c07105601c02d042e03e03402d100300c920452040907402c507140b8004500c241c07641d00d8050080d45001d81007564144001045000c00c0081c070300100d600c4580d00035010390ba10309a5440d03007003e118050342401040c000540c92715001d07949505031000791030114200503000804546517044400d90300c2c203520081003000040d090800c0d425129500c1210040ba0f03a40c1081c041c003560302070143c0403000050420b030060000030780046c01e58440d96070a00c0d0002301501020300407074907015244003440d0042184000c5051902d0040001d0112480603200c07041c0b4420000c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 685931366 1250 685930116 685930129
    0x30311060c0313030e040929010503030a03050702070806130b0106020f0718091e050114151e040507030b0102070f060903080f040f23090108150402061b010605040605 73
    0x4078020300c040c80400004000c00b14040c842140280a881d140390302d140c0c503001141c2110752103c4140d4013403035103a0b80380c2c4241c0710402d40041c2c0904410440c5002d94074020201e59280184410782041c141c403100010f50440c400c110840003411000301b1112076060600d402400c10100300c105072080c0d020741d0004a02140002028480540c0100050000928000c04010900d24448244104a0710344007901e021801e10b00482182c1c2001c0c0c90f61260010591031310a0844403180c0401c5040c18803001042900300d11004000889002540c0344001d0740c1a549803201050320950b201380e4014501810f001c5c10ba035260b40600040402a000c8841080d202e000031040b101007841250002410b608044c0000380c031003030207000500603003000a03041588440c0240c1d07a0b40782c42d4004440003a060a07a000410302c2d03404130400307400005d446081c60b950400b804180c64498225a00104d40c0d01d54000c80e04648905080b102c003c017900742c160380b5481180342c0160292096106480c46541402400325542c40c00303c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 685932616 1250 685931366 685931371
    0x31f05040b100f02072303150606030c0a02010914160602030301081b1906020f0c0a18051e010f051201020c030a0c11030709020d0e0c13020c210403031106 68
    0x41800e1024500c1440c102d40c00d0500030007074000c40c06070840000c5c10540e21000f4101b040120014102401d04600a052800442d004501c0c1aa14030809000c055202da41c1180d070402c50f41c04580e50f49041c90340c0241d014010009004204402c4075400200b804000700d00c81c00c85407a04c50114110540e91107003240e4900007806a000243c01000446226020b007480049000902601e06030032140d071001c540000512903030144000d40c00001e280b0380c1c0a40c0a0080040d01c450464408107402d0502002d10107170703e540340c40300460a40c5e410100d103880a100c400d081c2e112084015020866031039107101070007011035205607801030618400540c1144010300a44850401e41130086040c0b005516007201c0d100c6c003424041d05c5030b0281d0311426041d510140306450141a00c8440541d440000480010032a214602c055459800490950051744d80b54a40c0400780c800c244000350312000c10690751410071500940d8181d811587c0100d040f510031411300544200c074040d485040c9000c22000c01191a140304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 685933866 1250 685932616 685932619
    0x30204052d0f01030b1309032d0e03011e0b03010605180601080601110129010c170915031005030616080106120f1d0c0109080303060603041403031f05040b 68
    0x444108030400d042441e00c985210b0030500d000301c0c000764450007049900c42c2c4049203004071500c90305207000381600208401102141c94070520480c2c580359480c0301e07001e54542c607900b040000b08002051166000d4208007000003011040a11009070048078100505048042502a50802800041601d000c02d03180361001003d024286c8182d0301c0d01c2c01100c683d0300081c081414441c0405120810520910600c042401000780400c115143c3d40d0015642d804200e40540c1008000b110301c0000540180d0340c5055040752084294413020440c00042000c45c0c88210721055401c048100a01881400d5140c4103c400c29420303111140c07a8200742162500c0c00040c00c10100f500700004001503403040c2421010400d111000040f500b42d0307443d018094800e1600e8202c000340e42c00080e034070031000c144020100c00209083c070b1810b0074a03000c022912030100610117445088040006014000002036140e042d00045042e0781e43d03458552131801c822800c0c003600b810091044030001c40e81c0d04081c0b0520560280 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 685935116 1250 685933866 685933939
    0x1209010906050a09150c02030f0c0a17040321021032010b030112030203090604060c03090510170606070b04050d03050c031e041505010b070311030a1b061103040303020405 75
    0x1e802c9805d00183c0b03040d10038a01107220400240552401d035202a080748403501d4003a0a041204d030500c94100d072014a5044503c148c03c00003000001d0100406903004054507002d108450b40c8000e050742041a444200c0b40507508040c00c400202c80c101080c442203400c00529440d40e110b40305403008880b6000d00603407200000400051140300010b140c8140303480e201e803040702c1c40c000880c400310304660044d03403004000ca0b901070280020150041d40714009880b007600c0d480f214003802c28004210080700c0c40c85030cc2003102e00002c102e86496a40032030310f0107604104983c07440c1c2040d05c0c11550b00c050032046600000c1c50710022403205400e40b821a40a607004281c00715290340c4c0d03e4131214aa0002510407501c0a680a140c1f40101c1e509005103402032207810510750321a40203007005003c01200c180040b6658208000b18a105500010002815150803000c0b44030f8a505103000c030000d1811801a401e402404401c100405070715030010000d90300c3c00d40f160384181c0e44480041442e9076001c0c4250000e00d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 685936366 1250 685935116 685935143
    0x30207150905070605030a200403060506100912030e0303120117030405150901212004030209130309080f07030204063c1a030708013003051209010906050a09 69
    0xc0c811006540c1180d150800050208800302c401084d08d00014015a0350003400305003041409100d01c55994481e00070780d881e00b18001503a40045c064182405940d52441d040031100c420705d4880c002d9602540340c0641120340e40d5400c20b040000315036007480340d0b01440401610210804802000780c80031501c016080c50f541c0360080c2c00c20501500070a40c114100b12208040c08055260240043c0da188184680024100c5c0b5003840c000350411040382c0907800404c100410001030320f4241003075511480c401d6072814440303140d00e000c030b0f104611540006018130a0141c24024113401242130030449100725000c2013025034840c0b40404010400e10f0403190300c0f105030071a1161208a1441e2201c00b03c10794180722500b80c580d00d240e450454890032507a40c1c00004410410125041410103026100b404400201c142c18007546155221348401c2204003000700903000c900300f41c010015a038211403804c007664072501c0d11034540c034020000d0340f50549515043c54081007013149a4800d4401070b541081810a1b0031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 685937616 1250 685936366 685936379
    0x100b0f07020901123c060b0a0b130b070201200f0c0907050901030b030708010207150b04021c111201170111030907061d09040c08070504331503020715090507 69
    0x1c400852100c0345443d05c841c808800c1160f422500d5006840340c800000c203079445600b80b04c920b00e40f640040b01007003020090f0b035025401903e4441e04460f41c54420991341d007807030b00c01210f04005400d1168640802580035102d40700d00814110022070500e011620b0580c508810030121040590340c0c1c0c00400c04c100014829544680c11044c600b40f009822500441c0e80c030074059003260300c40e40c425500b4031459003070304180000b14040c006001c0b800b1181582002050498019019005600c04280580c1c07107840055040440c4166a213803e0500c641040c00d695481c48c6080510101004110652134014051040030308201a00d02a0000d40010200760307007000c0056414914070204410340c0b110026800c031507030f030b151090b861246210300080226145009445490440c0c00d422041c410390801c860302c065000e400f40ca0714040c100c0c4030041400c131400c5030400d600d4515582c000380e41041d040c565074981160103030010075000380301c0d1710800795074882c030384101080300c59090000300103400c00c403020800d2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 685938866 1250 685937616 685937663
    0x60f05070308271f1b08071808010203180607080405060601140403120c03090609081f020d2c0106260304081b04060914040209100b0f0702090112 64
    0xc0c440e0494032000b043c0c0c4510180c2d00d80f4081180d1103d00302e81c404880054029203004540d00c5200034a1100c1141d84010005444079000030001c030200040b0701500206403100c003158400a11080307000b19564103100c100a00740f90440c09a4007180d2181c403010595203071048410b28800d503044030103003455440303c1e0700440e491200510400e007075002c1400040040303610040480b2182c4182d864850036140c3c1440c02500f070800c039502800600c80e844000300310f02384021031150707a040c0d0f5402c213a66202e404035246071b009003c0d8105201e17100d07145c100740400c075801c00d1041c03100081c0141c2c4843c501c04214480c0305c2c00d031903150144800698807100541e10b08400510003000d0140b00100f968106a01c0e4420780740b4014140300100c901c40b02045040c4a0750400341300b00d4020740200d40e82032090b016444040d0350a0217003e80020b010300e1448001461b241c0c03c0d01e1404001c2c06a814596039586441008055680c11441003030744654141c500009600001900711008584c0c000610b2909450a0480450 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 685940116 1250 685938866 685938901
    0x1005090f120f1c0801060f1707090803070b0f0c1309090c030215130b030601020606190f0303030b04050a0e0a1b0b07050f070603020915070503040509010b04060f05070308 75
    0x1054070a0301c40a40c0245420300c14110500078143c031550164149850092090700c0c10391000050004000c25946110390119032800b01540001c410707920340c0c98886044481002c1c0d940a08410301000c60b41004005001c112240070303800901244003251641c803c1407166200750400b8444545040c1310402812210350440c98a40b406010102e501d1582c039004074000340c01d102c280903ea1400044c0710003410118985900c041c01d4108103860552400c180040e5442c88041c1c149803052001c000c111010b00e40722454a00500504211000b002e07a980c80c024001e010703110b816034800d509042c00181075100364400e01107903009410003042c0c070000c030342c40c1d003450b00c20304103e00c01d003249500c00d000c24503a030407a00400b240c62242c0018402c1041025005051101c5504010100b6004002c403241e15603620040c0044c078282d10006a41c0d9007074519040b03107948070355482a900300120000000d60074108002070301c2200d8940c0c4504c00024031080041752a88a401e10060100d44054049034240b00050780118 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 685941366 1250 685940116 685940149
    0x30b040f0206030103082701090519090608012007050a03081509010b07030206060306070504090c05040503070b0c2e1e0f0204051908030406050c1603030c021005090f 73
    0x403046040c0d030300440d1032540309800541c0d0007000080c5407d005d000110a002003c500510314505010361500000c0c8503101b00d101f110320990840b810202d000c40070702d00c2c2200074009500100907544c0e4a00c05140070f03100240440c04464802d17941412202521401c079000702c0e41c0701e0041c01550030195010303280d45130b001d807181d022203812140c04d110689581c1b007101e010340400c940e0107890769440d04d40240f4102c40103082c14041e40001c001e114003150418280d40544003084004144134040440494581c062680074070790600c10f928001413000c0324080180064550f42044d2aa2a146030f03e8580e8800d0b1804070b028001c280d9441014400131a5911010449070a088611a80080c00c03040c0010b81e10f0780e090208900b40c5c006400c2200d40b41102c60807040400081c00b41c10414030307040e10700d40c5034041c611540c8180040042d0380081d0780014440c214510800022142009449045c01055070421500403402040c13a03040c0c10200c00d002e01c0030b0b600c031458010141c0b00400b04140921000c4003600c62800c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 685942616 1250 685941366 685941383
    0x1151707030501050c03040b09241905010b09120d0203030a0c2717071202040509070e0703021306050301180e1204080c0a05010e01050a0c030513140406081204030b04 73
    0x40700150080c003589004690004029841c0c0c02d080c1014014200c01038881d010951008132130740400721a180c40200b0340c1c9045400c90b565030b92996441801c038244001c01600c07040c501000410304a500784090309000700140c882e010340000030b0003040d54680000c0d0404004d03a0050002030400130068010a60031882482e00f14145032074100c0030307c080502056641d00410700d0b03450a010758811441c500244030143c200a0101921301180740a44490a8801a01882d00d0b40000f40c2800401c1040388020040441d134101e0b00c0ca000c1314010001d4203d8135800140c420081000121544243c0c00d80307068031100c503403019040d01408040c3c402482c15083e5918140542c039006800e400340100544010314a441c05002010307075010030441c03012500e810941c1404840b440d08030030341c2d034448180d803694075260405c010f8071080b4bc142a80e0501a025002401440310440032030441c00d290441c2100141c29281404000e4036a886180c0f82d0f44804541c141d03040e001e01003000850400059140c1141c0140400e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 685943866 1250 685942616 685942619
    0x90e0c0f040f0603050a0e0106050a06050c16061808070b0a050a0905040e01090b01051008010b07060e030d0e0d080f0705090d02040f090b010603020c0c0904060b0a08010c0e010201151707 82
    0x200c2e02c1521260f40200c001c259910104200c80310640218944400c0100080200ea424180010035a075814060f22040007001300c0c0182c0c16120411036002540924007581c0d8500da903aa5000b01100100e0044501c03541c102e22000520441c00110b160540c0d40c00d0810900300401c641040302d42d60040031148082010070440001c19403124861424000302000020503606064200313101c1c805411380c480e40c0280c038280615142c050307000e0005419100310503006a9544107600340360025007803404925a084c000000c01e01d01c401466440628485a51400d684041d04c250005a46a840032074884070003511000c00140101c0c07059004140c0c0082c02090490610056000705045510150045c80b550b80d840031101c092050444a460040c0104d00d001e40ca400d21880200d81c59003401142540a290703040045410480389070010445050050b20a03400540e58103a4107010307240b07201443c404641e200345003c44652041c0140c904015600714000c1c01c01d45410381a42c1a0451081d600d00d05005080c1c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 685945116 1250 685943866 685943879
    0x1509051003320607021b090106030b0109090f060f050904020f010f0201110f04090e0f0c040507120e10050c070308060f03031303050c0f061810051b1507090e0c0f04 72
    0x440c1c480125500248124505030202031b1802140c203d101d100000c5140f40d1070302560307a01107128190343c0f10745004188982900016a800103481c0c0003000304908103518070141103902d42c07200040b03445626140149981d00c0c0188091802c0984019400840c00345041c82c7d294001c601c1e03100c542c41c40f8400024642140701c10741d8000e402040c14115510400241080038007981d000d0001110340d442c010381110351154110307542e14410001d50724050340e204d00024400c28010540a003640100c0c140c1403080495805655895003440103400701500e26000200362509024403d0300c25041c1c1c1a1500c103660784900041003403420b080c99007154175100811001d41c07a001003200040003980701e100188103106540d4100030301ea5034450850750048000703000d50a4805250080101c09441c207a0f180681403000343d074202c6403441651768094419110b030001e201c28181c0000c851205181c402201a4582c65600382240c40070420f20401d5600401c1034046807002c1401401400140d25100702d051030719544c3c44 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 685946366 1250 685945116 685945193
    0x2d0a0504060602032a07090509100507050d050a1a130e0a210c0f0602090f03030a1214090d11012301080f0604050726060a1509051003 59
    0x100820b0058201003002d0015803140d01441a000c8031140300d920860580c4101150f880e4003a11612400e903899101066180b0814004c40b80c041e0440390060025260400000d445a800740000e00b00309031070702000034200c100c603200c0d00e07461007100c01024102103e2a0b0401032005281803039000260750300d040c2210100000c0100e51490b42c0706a00c4d14905441e0a01da51840b070b08040e0000c014045060340f2040043d00e40c00540200d154082401030b00c960380200404d11611030594880c0d050321002071401c13402900046400c1d00001040b0b030501c2290301d900c01c03542905001356140801a03204a501d03200f86801000e142025614030000041d004400903601c251001203018586d03034251440005104608081c8010004c03000b04000400031414541c3d15650b40d0881071061800c503882b085040d4280440b0a0701048000b10003004545950928481c05001091a0402030380140700307004000600c0c519a0241c5407150109103100742c08145035844100300c03416000300b5910301d0001c1c016624000200903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 685947616 1250 685946366 685946369
    0x1120515070309050f07120f1b0f09110c0307022403041209120c0509060d020d060203090c12061f23030f0c0901141809010506010e2d0a050406 63
    0x81d0342c08a4480120f05219050081c1490400c840b0303000540305200b0062030798600c8a18071340c899006070400e00c1c5410079019030002541d245040301019000003030003450305d118070015101410000c0004c2c520554100c2018030400c80102c442d0b4106002140140c600840d1035001401e40c00c01d404560028101d03210350681c001c841c21141e584440d05015407055021203081e0262030b01004005102c81d030740e180d00b200340743d1901c2054481c00b014800603050303407100382549100c5903001c3c00c698000039041ca0708401039001114205160712406940305414a401184007103a101e00c1005040c02c1d4551305651900328960441b10030b04454051000901c0c020070f0304000c1d50440c407006002040075400310426040441550a49990382e0000300c02d100c8076511294600c0c1110b05c080900000e45072500041a602c40f035040e03041400500c00300400004000640109224003026a18684000a0b80041214080c0414042d510144100341a010300c40000c4040582c4a00024081d05800b507a84c0c0016081c0d0307109 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 685948866 1250 685947616 685947631
    0x7020a0b06090703140a021926040201110d08011409061815100c02150c1b040e0d021e0d0801120303110a03060611060105010c08030c090a140108090d02030301120515 73
    0x3c1d0a018120700300048d1000d014061034032920308074401d0044200c0c1a41402240d4a402450000c541160700815a200070004008290f40580c00c40074800351040009100d0310f6040043d002e042c8100e45442d0042c1c074800c203001000095065401c11040d00d50150080035106551140c02c0280072640e54003a05d06003111403603440f800211490f106101c00110500019a0500780611a01041580124000702c4598241c1c0d9019185074041c80050701518110400010502807503c8172000141d0102d080d8001401c0042d00d48011404040101d603500702b400c0300316000403e08001440301034100c41e2041c9480380245070104424020b000030805a0f8484240300d0040f1740e0300c00e410840603411048600b403a1002202030212980f41400280c00f00072500d0004012034000000990400d0001e81651400c0d540602600c46039615102035481d514421161039000c14070007000910b0031000010108802032940d406181103901c1c18902c445101c5c10620115075900a000074100140c1e51610303801c1c0b00302007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 685950116 1250 685948866 685948871
    0xb1215100f3e0106080309040f0213080106060207060507021f050903070803090109061b03030216080403050307060b12120d020408010f06090e0607051c0603080d09050607020a0b06090703140a 84
    0x581e02c101c003142e0b6608414000c440d0341420002c000c4603d000c0140c03100000700b55008550f88118090b0240240306a580903100c2104041340851140380541c00f0000b82e07603d80e000c0719441e54658600355214010100c0081d4008034a29100307103050081e50300388108241ca4200a070504071b00c2c4c0e00081c00d1040035088450750741d01c042800d004540e070020301c1d203004088a050401080d440100c14040300c215425000d001e140c2c0004400f41300103d00d0051309400360308a22695100e0740c40c0c1c907006880b58005003042d140c0c68103000d400d188038540080086829507c8200400c0f000003003001c04001074103e04540f00d1016801c1c440000c898000f0700812200711410b4100081c074a090003045412981e488024a01c160702a400300486560001c0c11101c850001c1060075035034070078000301c01000d000c05820040260070b02003500b595107885600424040352042090318110340e01c0c1c3c41c0c2260368242c0300c00e010300035110307000205a00f410040003a507000010b520300402c00d0011100c0b01c800040040d03401080303555 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 685951366 1250 685950116 685950197
    0x40903020607090501052706071208091011072012070e0c0a1709010f0e0a02010801080d1403090106080d0c0c06050301060504090e0106050a0b1215100f 67
    0x9030301843e004003801d82401d040703041c6103021000c0c1000b2100c21194400001400300f01c030016a076402c080e1031100740d128004418403242c2c42070007002c540b002e44011455120300050b001d15202c440c00740400d440301d03d126150070000c1d030340c40b13a0328400694010584110507940d1006950307124603d10b0350500106100908000c0d113405080040c0c01001441c49030310707090900c140c02029511404c0000544810481401c0548032101d4181c01881007407150f034000d51174a840e50f25241d001164610349a03000362600320050ba600c0c844030b5298069042d07400005915011000d2780030001c00c001c0c50700020401d000254250700d42106c1c07881e05c0729800740103002c11030f01108101008044800000171b882e99243c154115494014054403074040c50240c03030b0105803541202030072410258002001030600402400103d5035682e186041036024180303044443c1c01c00c200080001e00140014899100045d001c8c4460b040145000c40d0010343c01b08a441c10400e14540035808408851070b210611101010b030583c049 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 685952616 1250 685951366 685951381
    0x706022a0d060e01020a1d0f090709080a12020c010e03030a0302070606261c020604080d020c0d091503020403020a03030810090203040b1e0603150705130f03020a08030f090409020f0409030206 84
    0x30710744101101282d100c7c2c1c0207072a06455034800070312151010341da1104142ca40710025158101e40d83c200074800e210f00c185141c20300c0724041030050401441d40030b84040d65140c5004441103841403000c150554800c002c65440300e03119500401440d40100300c00520244c6600010400c100074140b90244240401e498480440c41800404d6803000541c0000f2922101208081e40380c000040c00a007040c0c10200b007880038a0f040750103e81c09100315009440340c05480d80c0018200f02028041c4503800c04503200d01ca21064082d00c02c40c1d081d43d8006080701d24251031550100c40941000b003041d01e4000804c00009440c0c40380307002441c0102d1040d040300c10240b422004103540407600c0480458211504424800c3c107403001319012005100b07070070252040707541703600b0140c5040c4511101215445000c04000860001c0c07440c1c00c1040e00c1c0708607400e00c0000d40d078101250707590040c01c540801c0712074100a071214a00d81540005401d40c1301810300d400741c080d5400000c1c00c6074042c40c01074001d43c11130002c11401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 685953866 1250 685952616 685952627
    0x315030312010501080c12060d022205041401110d020a140301090504110402031e07180806040219060f180e0f06090603010c14070203071a07050706022a0d060e01020a 73
    0x30071b1010f0011705103400f510100b000c050000d042180074900151469055443e240c1c5409246400000c40058820814404900610085406644108002e210380d140700e04180184030142c0c040240c01400c1061040075040213500c07941a080c01d00c0f50304336600722600d110300040c500074880d01d640000da17442c1a04100d1007002c2d40b030203114070a03407042007004400b0001d04002101050714000007003290740c0c2c1440c1541c01d00c850300300c8400e0104003c10002148400000e10620641c030940d00700000c02d0001d044001c00d44124000d1a021440b01c0e04401e000601c2190b4400c11030000783d6001c00c156555501c401416102602e441402d000b20108010a0307042158035660001c03003d030000c2042648034880103040070356003502d5021480340000c0c0b0740c00f995801c00c21000504403240951280449c0c5810380c9001b58405401103034a80541480001c8050011a01811030b410040305041180000c5421149500c0080c1689500040000820001c00c0d2544038501d2242044400160b85050f0000083d10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 685955116 1250 685953866 685953871
    0x140702010e0a0b0705030a1e0c030e010213051009090c05030a0c14040b2a010903090f030b07082e0807080105040f021005071b050a0b09030d05031503031201050108 72
    0x10668402c00c8282d0005010306069603018000d483d0040c0c0b02d0b103840f121140549500303c0c542c5c18181e1409860090405107501105090100e0303102007220000200da66400d0f40100401d992412150407070410080c10030410340400d036141ca2900300d001c0c9449503007200454070152a0300002130310200810600c3c48840c801d2490b560902c0c01d00c00ca8440d01c1e5024960079220f41d0081116030140403525030b40c903c40308614034544a6404040003854034003a4055802400700c08003d42c0040d110a10003c2d28202c1e000c02001035981101c0c00074074565075114151000b110140004150b0032403071300e5489500300f804a1007001030b1030440840350894580f10f541c0d40341200b250030034030099140c90b05000020b9896100c404100b50305545c030f48420f40340c0c018251098040c90750040c1c00314140007840c004140480c6100d42c161001210019511910368071010002c1c001c082401c0d4240d40f00e240820403250103003014551040002d200109d2083c02780021070308582005451031884680c5100500066070850286079 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 685956366 1250 685955116 685955141
    0x33220503030f150402120106030c05161a01170601030206180316090c030204061d0103110a03090c06080402012f071805010b07020a060c1b0e0a1103090a030e0d0614070201 75
    0x18149404a140d0724991b41e010f2081d802456610030030160624028800c0d0b80030001d03540386141024a081c1020070340c0628410b1a0b00d490710540e80082081c1084074000c100f480480401400540c2c02c50382807194035030001441220003800242c0d2501c180c0d8040142c200400350107804420300d1440c06840805441e1014148824540144410710129612500c4160b01c400c0404005148401c25001a001070050001c41e0000003000038402404ca90190050400c09104860310140b007680c500c41206d0001d800d450003030001e0352421210040c80c044c0c4489c50380349024050820030940030508128948480c2d984811500404600d03541084415407040e44e0060200100e0300d0b02d0f00d0083da001841c281c41c40d020760f90500c081251a4002e00c03890013003001401d004030404400082e142c103500645860101d4ec2411a5424841d94403045409103081c1d03800341e07560318001c0c00e0407110751b603060355070304101e180294100c5460000040820b125014401c07010581c3c11140d00d05040c00300c8002d0940710100d400a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 685957616 1250 685956366 685956371
    0x40c030207050d111b0a030c0608100e040c170c03030301060c0b0109091a071106040f05100c051b03090301232d09010b030f33220503030f1504 63
    0x803c0760380000f01d41401170b40000c1e070518510702e400000040800c1903680018001d1090100c0120390b10750011151401110320300d40881a295072010715841c1f52500b2030b002800c0c442558810420001000324aa4100e074950040d1805200002c0210346140c01c01d902c5900011040300c0020b040c04980301555000d480c3c0040c1c20301051843d0385449001d00ca000401a1110140c840050381d0703144601d242c0242c520501007507030410b04250070410801405103400b65000c0c024080c1c1070310484481c0c49041150002c9848280c1880b840d504007000c60401008216600c4c0420042c0c07400541d020b20072a828402c10070062046c0760f2400350441e1030078000030070180039000074140f111184209808016200701e59803240400e941d84800b070840c0500000359081d034052180707525442c032034040401d030015a40d01051800c0800d00c040124403401d605107901c48461100f54402140500200c04e020080c9045018034941d507064051360784034610741c0100c902c502a0b00318001806640d80c105050000701c02d900f00c03800e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 685958866 1250 685957616 685957637
    0x14160b011703041a160c03051f02030f0105060a050f04120b060a06050909060d0516081908070609020d0c030c03060c0c15200403112e0e0f040c030207050d 68
    0x36070b01100e01d0b10500e90901300865030240720b2903948494880654030040d0440140d50741d2600c40d030b03104180204002c686000090041a40300c0610a6922801d50581e240c1c40a9113414241701c01c40c0d111040c0d03034040190400c12a611001000002e00003003984000f0040011042d060003110b00c2c40c050320a40c0700b404409410000c555028041e690440b1003120101040c2d1140e40005041c84030801d4001c3c1640039644882041404403082c034001caa01100a40c0c403c450010703850380c0101400c805c0204120820300401c400701300140d00c007513030316480a0803881211029840703006011034540e000302c942d00e9003024240304004580c001c46444031082c0c1400e40c0742e02c03040c0c0e0324003001081c902d10360002c032680d44040d101d41c80180343c840703048840c0780e1b48569900e64807810580001da1080488600900c070083c102891204000350700c07042c0705095814001030030700b940400c40c1c0b031003c50030034540c1c0700c1d0030414004403e80e5039100f482584101a20010b07134420051030410b0070b000c00d0100f507805000440c0304 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 685960116 1250 685958866 685958879
    0xe0307140a0c0b0c0109060c0f0f020706270905041b0504020301180c0e130f0b0609091f050310090b1e06040f020706050a0902091006050a14160b01170304 68
    0x54103419107030b0545070f03103861304644445903004000741e0f20094209801d0008921513207400c200500b007801c015a940031201c40c4c0c100400d036a0b80c0e00d180b09290000707840c2200f042400700d203040e6200b1070300c0f02c0710320003124941c0e40c00d155007c1e078105031815580e406210f902d4005030341c03548030008010f10b4195000c0d03086d585420820b00340b607440c0c2100e103a400c075160303004800250b12411001d032580311700a21313040343c9000da66600002842007054810b1442e00e80f083e040c9242c50320a05850803103200a0406201342c1d110001c2d40814004240d042c5904800b2035400b1900d41d8043c0040d8018001d90345002806101301d0400910701d2401803c501c4590038841030141c42500700103030b82a4448025100400c0451030035000100038852001d000d0000307803402c0284405101c550304028840e9000320ac0030089600c81601d0321300d41d00014407a52000c01c0c0c080154460103402130160101e103c18506800707060500c7c081c800d14188141a8040700d80c10b001400600c5009092111901004000001541090709104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 685961366 1250 685960116 685960133
    0x803091c080c07060b03010617123c07150f0213150c151b080c031302120303040c0801150509190e0f030c100b01020a020d0507090e0307140a 62
    0x824a42e070078a4006a80030521145400c00d041e9241c001e402000441d5454146422040c80c3c80c03440100d600500241d080000300040988000a0b0a0a80900140001c440c2c0201106c4640d000e441240a04000d90745041c444002400745e103402260002e130110325240c1000111070306407040d042d5681c41800860030300f10b159009a004d48e4649001c0381a5a080c10038107403801c4d144000c00401e1080c80d4113075007961050310303000b080000741503080017003851100590585425904441d00300058a0600000b081e1415a04020040b40c2c00a0104c00741032440b41049815076004a90903290340e90362a070100041c40007407041c4034403480040002c20329130341803100190031140054200c211070010340c0038055011441d030303002d050441d03152000c51300111114803040b078503078000140585082c026480c108a005007180100007080340b059000c0c154800c8103070b0070045040754110301690a4810140301240c800380602c9004011450381d802152104403924050440040d44a0301d50103540020b50300e680040e904a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 685962616 1250 685961366 685961371
    0xf070b13050a140909010209040603060e070506070b0f040812090c01020f060c040621091a010e0f060907020f1009050c0d0816061b050901030e0718180606030803091c08 74
    0x101d449003505d858610000740a80107078010154003d2038110300104011040c1d0201e040342c0c8018064503052940c0303004000007401065406001d90020302c00040b110620b240c0110760040c49501d14604020300000002c0e070b145002c40c1c04540c00ea0181d58203403055a010803050070a0070f07074440280b105141213865034009016512443d420300c170b10341c1c0c0e40c000000d00c01111002c19480b00a81001021741c0790070803e00310203041515403140f000324030022803201c00d8909010320840c801700480c4001d48501c01446071744003001302484114010b0b0444480c0c00102804001d461004402c808602e1a03200c0c20941d0400040c4400284617400e4000054006614017050322002c20b80d0b116110300c10b921504214014000c480308107035a80600c40f90808080d40c00401910301c000302030341d0400150000d07044080e50b900c1240642701d1440c0420341c40e5108003065800401e5904002c41030f9110a8038170303990308010b0ba03816800465a0807008030800400143c2001120f1082291005602e03407046892000b40c020f0002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 685963866 1250 685962616 685962619
    0xe10020a030b090a050f0901020a02071208071401050a0b09040f0201030e071a030121050c060a0e03030f0d141003080a2609010b04020a020c040e0f070b13050a14 71
    0x1003868010107000790311040e64075402a0103100e0340d180c1032504000400d4116084141c0c40441e1000c00c04410b414400d6405108140c0c004264041c284129802c1070700c0c0421044418100401183c070008a0400b9200700d04008900041a142000c440c0e50f0f0a84001400d654082d821040400c404184003028002ca03183c0c080c03e00040d00218041c9040c14040c1c00e802c10105c03035441c0d510290600700184019412150410600211032200b05100040e030040c4200c0602a82d01124180e01c00e45803980040c20b5110450403c01518130280000c42d0039504000c018001603c80400c0c1089400c030140520915210f2060041c0894507101042280d01241c83c0000751110340003040654030390380510790b075140c0302a001d450300006055400400601c844101e440782c0895007011a0103010b0f042034000d071400004140c0182c089403071a0030511000301062546058940308141410612607070901203800640494030015507035600040030380307a2199103988100e0081a41850410486409503031050720883c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 685965116 1250 685963866 685963871
    0x90606050616060b01020a0519020108060a0501200304152c152104120f0f0203040608150603090a0b0f0417071b0b0702041401050a18090f030806040f0e10 68
    0x14004e004030b10317100b510fa4000741036220765420f0800a40b03070101c82c3c0e00e9440c03007607840c0021303640c0c2c0c40184070b0f541c3d0280c4101408600140a80101c0e01045503902a0600310720b402c0740d05080d03a5102d40c000c05201a102c40c0d02143c18420100c10a0010074400314902d603d41c02c0300341d034410740c900101d9405045030310baa080180000c80d403503030f241040403c80c2560505d03209088585007084e0400150104040d1f072401c0c0803d102d1803000704068020f0503000801081c0360003650a017807410380240d4415000405c0705000c04482c18005180e6518032020398004d040c0350005242c01d0240f072600c560317106000b41c030303809031a181034041000040720140740710410700c1d001d80420380751796503460a40002001210660307404c07080102e010070407542c01e10141401c1c0e0b001300c50a0200c80f41c2402515111042030040c203802294000c01403004a454280c3d03c1e81205003880000307070111040d2907040c450304078240c0c201c00084000d01030040754580350141e070151071144031382004520860f1510681e0741c1072180305405480c0c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 685966366 1250 685965116 685965131
    0x1403120909150d080d180206090d02060f0307030b270c0703030219020d030f0212040803090f0706021014090a110d060f021218060f0c1c09060605061606 67
    0x4142c100b90782042100074107014006140303440c0100050b04101d0190302510318004d507444207101403044460b0503503006860640307800c07454401d020300d41c254980103a800c801c00700a103d903060b01c03010040d4400c582e10342d4001500c08061040194000c02d140d00c00e05080000280910304c40a0031701a190404c1c110f02e15165524554941030b0003900440c900da00c66040310910325440107401190309000810241d03000c02c40404d038030010038124041c1d106250b0078400c2c105d0015002030320711030082d5000079070700c4200e030240c03040840d2052410280e03070031590040c2c01035501030b60103c0030703400b441c1d19003600304c100304801e803a00c0c2407525529104908080e00f81c1c14074049082090300c40160341d1940c00d401000600c41e81e4108809070001c0d6008180208a214250f800141c0c2d10041c801040c80c0e88034280c0140409464079280c04a207088003a1100c1e030000007c00c100c104082c40d4119107010011204008070301c08240c1d044c52000c481c1d0590050340240da0812046950b1050030213142e259030340c864000144903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 685967616 1250 685966366 685966381
    0x90816090c091203080108060a1118010e06030114011b080a031d0304060c1e021806031005040b06030601080c0f0427031d0649061403120909 62
    0x6030560b0b070014855046181440f000d055021400c3c030b040e80ca4000441d405511441c010134102e41040410b00c4140700700740f10f4201e904010150b503401d600d82c140b40044601602c5e00019071184e10a81c0244201040c10803050003550700a80c0004584004444407a5017210b06d40301c4028070f02c1821406002c05d90780701c00241d626203440e0040205480002d04984d12261500405000348005c25001d64103c5044c4160b11075640341805075030f824a40c0680013804082c0355109150304004050012a41401020ba060f201c4c0c00c0b41e4171506216500400c200281401c207202410b08101d8180c2042482d45c02200200c01240c43c0d403d0700c080c0540d819140014074032210309010550510f4400e4500090501c07844140030300d0f0b400121401c50b04000904500049802c3d4200302e050b128503036a0401c00790800502c4c0c0d503060200c11400b880444980c020030041d90720400120120407175500d90000c16075959506203c034a504802800034030f0002d80080113a1042e22100c00c4560281c60030071442400550b0028404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 685968866 1250 685967616 685967627
    0x90a09051609020a031514011b0515010611161403071815232b05030a12090203030708030414070308090906040504020a0506030703060305030d0b01090816090c 70
    0x4125041c1c41048020b884451070740180d03200b080c600700003074106000408060308040010003100c0460040c030360f4020400006481040e040104954951807104081000c1a8203101c00e107103080d03000140d44c06560500802501b0303003913051501d0540d80d200080c1c4580c038000d64624a03013034500110381c040031016410006854456541c00c64503524090081008200c8241d4000582d00d0b0941d912030203850b40c50700b200146d0002c8807100b0445005003502c550085052403000351401014450403c1d0f1040a07804c116440b440d480c0304110342c03070741c000151150714075480400e9240c20000400144940320b001e030002030b56800ba43c00302070102d110000106080051500018400e500034500341c403003040d0b0364144440d0300d0304850b03065802100c1d134000040040c90310744103803441280d006049981c4642088244580d03600010040014181c0d580c02c00b00100710b040000c0d0034011070440c00455400c848000051a08200383c1c4040d005a2200e010140110b02d03040c042d209649044100040c506004c0d03108455 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 685970116 1250 685968866 685968883
    0x110706120b03031305090f0702191e0f030e0609030c10020c1e030d093204090c050f18040803040f0c08061b0a090504020c0c04060f08100209090a0905 66
    0xb8184400503a8081e13510101c401071046071001c85442440355030741c20041103110001c41e508001031308038595403400b40360802e9030b085019009d030600f40b0701107000380c69501c1040740e140c000f83e41d03892415045c0000c15902112034541d160040d80d1250802ea91400820740e81c03e03540070ba09200e038070421002c5821602c208054061990300610b48581d5203140203c0920740408149440d0080c0526800c0481c00c50062005004840b090421140c034900c40e08102d6204644014180e5041d4410201030407165455004444145025007003140f20341e4070f454104440b080b1007500e01130050b086058100003c1d01e001c000703164059041013001340d6071f41e514030b490300724051011002040c100c41300c03d001c60031000028043e84103244003c2d044080c84407010103034910780180c45001c40040c0c0841e6052002e800d06030042c00640400034111864600a040082c050b528103030041103100c0d030b44400030440500c4c200440f042c9034203002d20840c5884480408125902001400201c0864813085807004000c0c040100b0b40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 685971223 1107 685970116 685970119
    0x309010b030303102121030609060302031f090503030a09120e1005071a28050c0403021c05010c020c010f090503060114060403171207110706120b 64
    0x117480301003820034440383c5110007500c490018a011080350001c1c3c03180302c0c01036005400b01c5001412280ea5901111a003814400c0400268401140080a406c1c60407445000d00c0c2904006101900f100400106603200000821070056042d0380300c0c41c034003849000d00001152890208581102106a031154007003048400340c14118002c000501078140308441c00001f100412842c1c80520741e0440d248000420308800c0c84000d00d03103c0090441551112404100c336050404425201b40281d0200a004251440f4032034034902400316075030103040c1d0000c0280242d40c402c68000b0340701c4011640310707804220324080414096000e40344040c2a10000740082450360710302404e82d03140611034041242c000800700300100115485981044444544030769195640c9286d404250f032401c0002c00540400240e81c0d505011340c200414142c041310058941804004982e240b424000c1004403c1036 = true := by decide +kernel

theorem cover : BRFrame.Cov 685791366 685971223 := by
  have h0 := BRFrame.cov_init 685791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 685791366 ≤ n) (h2 : n < 685971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
