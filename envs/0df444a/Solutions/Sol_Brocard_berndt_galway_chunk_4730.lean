-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4730
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:33:12.384125+00:00
-- url     : https://prove2.me/submissions/7eb451de-1a9d-4b40-b8bf-9564c843415f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 850539568 ≤ n < 850719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 850540818 1250 850539568 850539583
    0x3150112031d1215070806010c14070b0a0c0516050a0e04060204080a0506150307260a17070c0f0b16171b2e0f060305060c0301030b0901020901020a060905 68
    0x1403c1c0b400a110314840c5a613650700d6200d0083da41002c40c0d000300780f00e10301c00c0f2a080c4c060201691039028904480d01c1c0e2050001e04040718951a1044a030001004210340c00503210b040c01c00d440c2c0061086a50400c04d041031641031031a142111400828005035840b00f801030309031141d074550032a00342d03180d1600a00a12654220100c1442049010b1080000001e00c55104140c01400310a41481090034556164450700460b90b80300c102e4814054001d00c0044109900089081241c81130741c59500c40c00d513400d02100c40414815000513070308060145400328440208442d807802e00442e4540000c0d01040c8c050301c0d00000d04040c900e40214180251003240340c0c54604002ca655039106001000034400c4001c1c0d0040503030700c0c00380c2c82c1d20100c0509100e8410110340240e03688402304241c070148010080c0400b4259035241179941c04080040b40b010480e10344a01c0c00b0b030720340507501d5045007460383c01154000d00450060303004020030400c60740c1c040791003400264008004541c105203450a5400c1108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 850542068 1250 850540818 850540877
    0x12030c0f1202070c0e010f08071a0309012409110c150405150906060a0b091f11060c0c010608070f030f080d050a0603061a1f0519020a020315011203 65
    0x82451061700110702d0407510b02107001886c0507a6458407640750421032141d02008000c60040444d80b41c500401154850b1943d400020171144003049105c40d11249411240c107203404110500030b4940301d00c904502d9003c00d00d24141004580c001296880d040c1e40400b00c0780b50200400b18007006410400101d102410702c00e00e0705035140110000c0c2e42c0d005c0c111a01e45c42828891000204460700307004844840c070300a001080340354583d0540d100e81701e42d4120300804009448c542000c4600f018005036003d202d0390000c45580b0001d00c1116820740e1150b07004100c071600b09907010004061036481210440c0da1050350840000000c2c01e0101e514080c481d0754851640c100700400481c2c0b012548020280c03841081c0c10001b6900440da46001020844842a0820000368101204580c0c030302c1c409d68000840d2820524254405081e8003041034141c01d2800541d004485060031480c05008800320303003041c500c1c0f41207a50302d01035115085403120310000d018000500220001d0842403001051200e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 850543318 1250 850542068 850542083
    0xe0a02060d0b13020702010201140105011e0e04090c0e01080303130611091c0203060a02030c04030312090813060809030711040203042a05040e010e153112030c0f120207 74
    0x40803e0411406540021001c9005502c0c081e17411f2001d0510f20006030503108180d440c0c58103418501000c0440350740302c12402d8244104c2004003004e81c4d459014241400c1e1040406611052502d10342800c20081a0404075190b081801000001c0115504041f00d95802450219402408400c10b48180c46608041c1d07811070344408400d0007010800744107100c0103109a0031079040313649003882c040480c0404d4404444c841d02c01c0108102181c413441200314152000800020a501290307203020172540035410b6000d001d049c0550800c54940c00801081d0b1000561001e14500300303041e17440d4a08062000c1c0c01d2440345a0102c0810103000c0481c01c0031801081c0f40b1420121140c00709802d00c0b410403140300f50783c17203241000010340c0c01c42d2042c010302c0344048015004142000c80d8880303101c1c0c8594020020030200041d0b43d0200710740c580344900c02d40036010303c8523003443d00d90140c01c00040c180070402505050500f00003008a01580c0407071220100d100f81d00c0d240c2c00307030010b88071601d000e84034a40d000b80001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 850544568 1250 850543318 850543339
    0x7080a050d0e39030c060703050409060305060f180601091812050315030111030a0519020a0f14310b13081608070e0a0207050d120509010e0a02060d0b 66
    0x1c0c503400054000340650f040d00d86080840d040c00e091002010302c180e03050b8001042c25000c0b41098809405068424101113003815125009a021608141d20651342540080180701c2520020040c09810001411a503400c1510304194280d4400d03042c480c8904c42651a080c05071617614803001c09080725449005800e05040303121000f00aa001981c00039161114680c49203140e240c144510021001c403240303200c0c10b50b5118480c000c02010b000744510117000510b40c0351018001c103031008019440080d250340e2064110f41c54000d02d1050302440d0b11100110402040011040c42412005481071075040c501d074680010308089501c1c5502c6c0d1004e14030120100e0130b58800b4441624103419103014100301c0310f200303004064803692100588240cbc2e1094116003000d000d400d03642002154004451131000d40f9007241aa541131914031001030f2000015403800a002c00b44203d406806d07040285403000780040c210700c40c050b50f00c0c0c0d04080d0b030080c4209000584c3c0600c45901d034000b51202000280307080d081 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 850545818 1250 850544568 850544593
    0x31311040e150601050c06040b09160305160e010819031e081506121503011407080601030e1b010509030717060702010c051611010e041a0a0b07080a050d0e 68
    0x40b07103400202289080042400250300d940714000343e030703240c3d50f443c40240f08a0311142c039440f0b03070301d040030b4000c2006009100d0403245210b0a09601c0000718482e00040060341d14a000b60600610150001580803120320300401640e00001039600000c06102a211403481c0f4515080d40e8040c140440d07104190b04541c40107212640011031360307100b10714801c02c04240c482c1c0c44040026a124914524601c5807016000c20381d8800007200740c40c240706010f17000140348844105804244041220984009400801004465641741c0220710745003000d80005c12280407000c0140f00081000e0307500d0b9040150200e94040309580402130100140400f10a070b8014201c22401f10381c86e4031040711080003540c00d003112164460301c1074046074074280c20b920500ca503c043e01e44e40c8012640c0004140c90401200c1100c4501d60b5031944a9201034410030441200b90208a4040c884880607940c42006155070078800ea01c0400d000d01d003114605180c0c0d10b042607031b640641340c421008050300c0c1e0150701a4031400000154 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 850547068 1250 850545818 850545823
    0xb0901090f0f0807081204060f11011a040f0b0604051012020409050106170106021902120f0717010204151103040f03030206060a0e1005010f02210403170708031311040e 74
    0x107460b12902564041e0b174030780340105d94441460701171071141c075820402005500d03c1074400c0410000c451401c944403210f50900c490948024140303041d4180944c03444c100c00c62400e8890041c9070301c8095000d00081d809140000e08501440c4a0680190601c04000f04124425000b64804d4a403c110071910f0301c1d11400c0000041c0400d01442020804140d144d001d00c41c21404035074100d82d0203038010001a10380005e0752082002c0007d00f260441107141d0384094404040c4414071280c2019001090300c103141c0200c8401d50859403410ba50a03910401081c001060b180c420701d2171941039414040000481c02441c40c1c91403040354031490040c0480040032007090b9011540303900403081240c45903801038440000600b0f64000703546808088194240030003036540207a00e007490b2030405005440810720503900c0d0300c05030064080804a9202c00003414802c00c284040e0464004150004460401020390380d0900c4c144009004603400e418500c60700c004010000c000d1082c4140064828405800f042400c2035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 850548318 1250 850547068 850547099
    0xc020a0f1406120c0d1b0f020d090e06040c020c0613030b0c030105030c01180801110706061403030d0902040209041a040c051602040203061503130506011401090b0901090f 75
    0xc000098040c24403441c80d020058828480e1541c103e00d00b02e480d07410810903544d0100c94004072858581d54140c481454119844010084039284d1044101c001c039002800c001304c2c04011000e105548906100840341c1000c62940300c6070a4600017042245400246d2808011098181e88108002240b00006104100305c4044a214101d0140c0c0f58581d018081e0b82030000340250398140d80215210951b940c81401034010080d845642118000d0f20b990340309080d11b03820741940a1900300040c1c0007007049014441c200041c40b150081c0c0c54038100200000c0c3d1244111011b05215940301d51082c3e003550340d103504448104000800802401d102400003488030301002c084940b1841c5810721003200d4030700440c01c644a86a01c1091040c418215608106c0250405401e55411080320000400f6025032400114080c403148a5602c1702812285450351528105800c038900303d00f4000040015071741c1000e410400c2d141c0495040e621070400d01d00485401146da800720640c22103100001464418088015 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 850549568 1250 850548318 850548329
    0xb0f041b030507020705011422090c0810260f010c030504110306040302031606090b0c03090625201e190f12140d0506040e06090703120c020a0f 63
    0x18030003070fa00d001d0181c0e2100614420782d804101034020755840c000195004240c03010307240407440c1c2c0216201d0030f9404014005d42103020b049a49041034801c240c0c001c98400d500013020030141d02000c4c1000c80e00b09079041d400c0ca0703180050050400764000d0b00800d01407100d1091105008011900d100c040040140c0019034040e114000007040d144020300300030503082c0c89580c15400952074820031601030741e0740180301c0c1d01c10354510b03645000f5000010348981342139009604849009403641440341d11207003058005800240200952141e02107600105100c8005400107400c01c0341d2100540f4070060b40c91406209500c03485d01900344142001c41c101442120000c2400b800c6a2500ca80701004040341c81c2000300c0640b03001010642000000d0017448881e981d200c0510b01703d400c0031183c0700040d845801c82c41a070350400d9124820081d4a09007445a9950420100010040f6081c408030032912100d1501002d8a40022002d1460002c0d0180e02070900e040e46c017038901e44403241d0390079800c4171144050007074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 850550818 1250 850549568 850549571
    0x21f091104050708190905070e100e07020d03020f0c0115090507050901020c0d02010504080703030503090c1012050a1b080103140a080a05130302060c0a021f120b0f041b03 75
    0x50415074181481101d200c0c0712191990203094945040040a41d03034000107001c0d480c1c1d10f80080800003031703060101c0e1000f0003d5102c8003446013440c0b0840058860b45401403141e00e5041d4040094040e13001811588a100038100180e0751741d605006d00b0094412210b000d4111340c20814170480803841d840c91613045900f02e8404000c55281c1c0441114075202e030440c050b0041e13000171100c2c41940350008880c059903205040c01403500d40d41c0c82d030b07585c28440558000e5002c56030110420111940510101402c01011144113160980244018100d421116039480c02c0315a29030000b0380d40c50142d8451944801048103003802e08100340002004085e0901040340c610000100011a4820000f04440c01c01d5005a40720b092207943c0c1800c48480e04000810420100250b40000150300c032000103001001004014080c8010140144442c1103523a017038403804004507001442c90710703a00ca403070078081c22003842d8041011184117000907003483c940c2d11f40c05c0c0e100b0f10301781c40c2c0e022070920600100039018a5440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 850552068 1250 850550818 850550843
    0xa0b030402100e0d1104060e16020d0905010f050c0f06010b0a1b03020a080c070f150e0d0209011e051302250b0a2c010e0c06030903040603090201021f09 67
    0x60840d0480c0f0381d1100c2e550840c2d844078610002030700d01d85000e49100c030b010b003002400942d100c0d0200c80d40b4006851007070040c1c2150300050b0f4255418444603c084030300d4280300c40c84614210000f010b40c0b000c500960304005003c290f40b02001c4040c00004400000c000071100c1a5860f455020402d41c042c030800000709040c1032542088035001806051110b400d5009070211072021f4949441c1640003142e06411402003000c0407038002098108403028140f01103410610b0110f002015040c0d051018101e80b081055070140801a44d4000000d8103550019924803140442c2030300080d10700c0f80c0da40240d903000b2505c0740740f0b00300d41c42598060320404e0f0350707450000348604e4000c2c0c41c03210b5032409000160110744482c0c0090083d1406030486031055411400903e038100d1000f00d004840041c4030041c05903a510381e0000b508000c0304100c143d00d28241100c030241755060810f0072a6591041d44290800d054440e071500381036a00030310245005100401903a0302604044401000500b00d00900722a103020500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 850553318 1250 850552068 850552099
    0x1060302031305120a090504150b030403050c06071707020606031e070e01171204121b0b0a030e0c0102010b1f0201060308070b012907200409050f1b0108070c03030b0a0b030402 77
    0x10b2462407003100002209c52600304622000c1301d5100400a80901c0020070201103c5181000840c1c4200b0381d0f680d461955009072101d001902c2c8000d040c8000710762105040c4001079034045009190244814102094000e07004d8443d82010456441020100d1942c800050514101102010310401401c00e45000800404485060740105e00411510240c1001e01034005203045940f6800b0140d14529207004c141c0d10241130b4400c2e03114200003030009890702c868040d942030421041880c840c0900080c001c004c010030104070940100a40403940303d080803054816176000398082800ba58108641d180d42e6101b0b41400d8150400a1040c0c02550741403641b504410601440000300005582c0c0ca21850000181ca4040001c5c500c08510b410b8541c2140110903ea510740c45036031100d0f407081c0080c08500ba01d8074501c5041c1241c0c000b0070b140042c0802886070840ea40302041d141e100d48941010054643d16082c2100100858025150010081c1d4804034038000c0401c00ba621031032085405e010314103400d8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 850554568 1250 850553318 850553321
    0x602010501030b010b1821060a0b03031210051f0f140d0f0f050a0b0f0603270c061b0c0111060a0c0507020a0e040b0a02040e01060302031305120a090504 67
    0xd21001d010500c4000c010700125160740006c20365813245014403200b014040000610400010b41036003030003140811607803034415003031040391380c07109419908001120061000c03d8591289104442103d40c01600260b0442600d00c07514001d071101910340c041038469a40503004400c010520480413544240809507640d00c90500c815054018240541c01c0c00c0c80d50240c0000f8001900e58920a03e455591041c04a6610300c90346105011048006c03a0044000c0300740100d4400c0c21203020700451080041101c0c4e01e1541d003446e00744034200d14810130785205208105043c01000120190301410020703e4540000c1280440e02100c1e03107620071348542600c0c02e0015113113520441204807641c3c20800014443c0209075001c030031035918a0401c0707441c1c88a03590004114032090f030803030856490003170305010a01580414040d0306c00d906c048110718084c01d11542d0061710300e0500c07031030041540000004241814000040d10310036880070444044226103012081c00340c0001d8801e8000400e190800030f03491606 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 850555818 1250 850554568 850554571
    0x170a020f0403030c05010e30070803040206032205010204060f030b010207090c020309042a08071b0804030b0a05011403030403020108041205090901060302030109110901170403120e01090c06020105 86
    0x605800d40750500e5640c0a0718004280c000540d01556101d8180c850844144901d62503100f0740107401e00d82380000216024242c4410812004544050100d01e0008581c80c0440b50810780444155845ea41c40043d24401c0c06481c005000e92104820041070070008150080c0c01683e5080c1c4481c3c030303400c1c00d54208408851005c884140145d02c80f003410016032031a81d1120780c0e07061007841500d103003080c0e00d40800c003640c00d00707440c4c0698060544803650700803100e13040700740340140c4c01e14012540341401c000c010500403600030101141d00c03441c0d6001d010010044211001154460380c0c4202c245030000d900d0005040900c0b44580240342105001d00da0719020007243d094a505865a1201e5191034442c08182e500c2910500c00380002045105000e6480303400040c002c01d0991380c09640c039070404124200f92100c482540500b4141401400200e0380c00c402000903401e20210404e9007540c1d14101212501ea8207211006024039003084000d03c42e9064000c44042800703800c1700e000c0d603595408100d01302c460 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 850557068 1250 850555818 850555837
    0x50105040902090402011419090f15050717040909061d06190b1504121e0809042004080708070e15060a09030c06080109140c0a050a030e0a03170a02 65
    0x103c0e403000800540c0100c2240e91860303c4041e481c0c0c2003c503240741c1c2942110340001c0074804a14050340802c00e40d4a00441c0c503010300a0204130072402c443c2d400e0060040e000317141b401018007405e01d590f50b1050361a178003520028101008280510b140904060f00203002a03d40004624903809004218160000795a0700403068420340030207079910307a90544024003859072400d07070007a40e101082c04c03411034003070140c0081d00301444050348400203032030418032b0417500e5881c0c01020610880c052011800c039605480081000303403000b1803040b007103403808002c0080c00420b650340320030f000c100441d40d0f031800034030752099440a0b000c480d2000c1d211802000c50b041c08a60b01c40f400c201600c040a0036050080107001c0c41e00190806251858403581c4852003141650002400562540c004100d101d029010381d96040b0000b0480d9085400c20101500e0544120b2250400b03000700000c0310f2007520b100f5032140f4200c01500c415903c1ca00041c0c0390040070030382c004c848490080e100c8404140d4001c014400c0b40d42080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 850558318 1250 850557068 850557079
    0x150e150906010e03010b0d0302031306022802032b020c0136080a030e0406060f020d0f1b060204090c0f09050114041d010614040503060a050c0f0c060901050105040902 73
    0x541e410700468140340c0240782680c155490b1810000c1030b455090540a01ca4401d4001d551528601d1005100403901c0d40c0c044411903002854504002852440700010341400b60480b00660b0100c0c00841e1409204a0550701c3c400b054101c8450383c0d8800c2120501d885220354280c0d610b1883c00d000442d00c2101c40c000741081d50010255841040f00410301520b40e1000b0104140b582c1070351404154184026940180e01084e400b012450041c9440d110b03d0001e44001e0808a03030746080e1420083d569011416440c0901566800c0000302c039003d2242505000d100f0a03869544881c50324048019400c20b1080700c07a12414460740f182118020100762000001950349c040605e403030f100044410343e07100503d14443c29800c020102e60780401110350708002d60a0a10441d29514000c3e0041203012002e0038080c00c050240018030440d80c01240306a000042a13a01261036168030300c400f00305115420000b903051350001030344984202d003c40d075140300b0403115000700104d80c0c3e0b0304144001d40345036000c02540403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 850559568 1250 850558318 850558321
    0x26160f05010c020603011e05030a08030601170721110d020d0c0305010e04240e1e070b1e0d0504030810050409030804060515030f101b08071d04150e1509 67
    0x9010030b2141c2003c5550046200d0020741c3d48d4011070300308011004151080ea5000040003c81d503040503500300070b076003a0114030000d8a02040001e01843c0d020051051030150807014446c041e0444c2c00c1042e6103854800529a10303900302105074001e501401510f0700356400c081d5682040d40c041d2050360f04869400000e101c0301d98481d07807049603030b8488502c0d00800c0050201c1c40940f020191244050f10010b060081920042c1500030014407080d51600d0129030384944001e010904050702070b1a00710740e00324883c1184000c8030b00d070700041d40500c082c0405481d1400c010401415442200603006803210003081030040c0c2c0340d40c180002c0d10344020015010a05060120b0001510350b440b83d0360114605695a01c1c000c9480c0010f0f003001c00a91044010340c0c440f041c99a808041807150350850304d04a0410550074052a50160140d00e004142a00307001490042151902e41446500c0300440000d0003000780c218502103c9690810f94040c0c241038000560010300d95003d010510380b0390071001408044107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 850560818 1250 850559568 850559579
    0x5070611100504080d0b0906010e120a050f010b0120060103030507150504050d0e0603060d03050717030901051b09010801031506031a0403080601090f26160f05010c02060301 76
    0x2028404201036429110781c003401c500070446480b885000303a12900116030340f01144141c4809482e05910f50074400c0e8a14414000c003680c0240322003000f181d043c1c5030740500e040440303d00c50518260b01c2e00a80300340101940c4400010040d8840c064001003600d4111b0b15142ca010b803040058a4041a003541c0d0f4801d90050001c40c1c02400130300b04462084045014400500340b500080d100180c40032280e544c8200d0180c580c490304080c80498844068820904501e000400100c230295010800b4080c0000091404144050316221280c151640910700303649040c80c4a442e4001c1004650005580d40c038205541da8240212080b1146684141e440c03514690030760300c07080c01c1841c10058041986654a000000090b01e0b4115900a00e28418200d8418a03181c01d01812030f80004104504000c102002400210410001d0703c05642d494115071045801160310707201000303182e40307441d161342c458031a81003070180305042990140c40502e0364009900380c3d41c80040d00c445101840003940319606100501a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 850562068 1250 850560818 850560827
    0x311061303030218121f02070506060409050c121605011106070809030c070803090901330203040509040b040c140604090f0207080a0c0b060a240905060408030a0e0d050706 75
    0x6074200c000e00c1310710140d1038400051220700d8500d00004a6420038140d18103944184002c041c004890740c0400d529000f0596241c40d00c0d03180007881e0320f02c155942c005180502c00700300100390104401030215103c00c400070400907902e4841e0045401c500c00c9003007000c038195206141001c00000e202006050b20389031400c090f00c0d9840014244905071006000c003403648c40040124000401d68080910703510b441702410700c003445005070004500c0700c0e040c0a40d51840c1511600001e40261002011a20111184c6040f81940302d1980b1203540040c02e0f10500050100c4212114020362068411000c101d60319903003089125145400c3c1c95121038203000c104404455500b019005026200005107450f020356603001c4550462010540044e104450760400c10110b00380b0190054004c41d00c9541303252924004030381403e401244800c41355032110901c02c085000340b1242007e8032000b0315284d02c0d940c071000c4030b130341d0380d0801941c01c8002070032030715004030340e003020b0941031641c58119014004c1079050074015607 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 850563318 1250 850562068 850562077
    0x9010c080720010501090209090c190c08070b04030306050117280e0316051203060d0f02060c0607050a03140907050405041b0f030209091f0515120a03110613030302 72
    0x212095900c090306800b0100a105007406084d03840b000507140e0345010180f050390f0fa0024012021000c0803c8523112450070400385110f0300d1043d1801985001c42807900401344d002e0040000c04544c414014403040541540100c070585400780c0e258440302005290010b40d00c4019212450f050410344a0051018260000e032854040d480f8008620b5070340134080300c0d1555121800c59a401081040b94008100d01131104468904641d200e450035400c1603000200c8418070710500501314940700d01c1d480210344075941030761f04412010701590741600d03002c1c00152442d0304c07208030700f070000b468800c0f8440341003600120a40250400c4000b404124102410f000007884050825220300d038480303085485e0f8140d0417000b0070103041d00741d4542031094514410f1180003031016000d040c940d00505450340c184c8200020403503140000c0480400d05480307040031040b80d11004034903030741c000100e186980e504d07820003d0445900c500c2550380d001e000351a0001c181c0c592400756180c40d000100080a034010034840d07009403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 850564568 1250 850563318 850563347
    0x5030a0506061c021b0a0b07080f01230d0b0406050103060608150a0c020106030c1502070902190f090801090309031a0f0403231b010c020c031002130b07140609010c0807 74
    0x301e45d84039028200c1d01d0003e110000702e94107002581040711242d030020035030790021001d0000002c15410300340e400400d00d2008a00e1042d80e403840405080f40d582c0c1e403400c50a43d98010b4220f800c50b041c80e00707100c005490f0900050f69114144a80042c60203c006074121000e203034000f03025801e8482442c00f0002c0c0180148070003c640d21101d0100100700084200d400400101003c4003c404140401a0603d4001d41c00004c546206000c0c60040e0aa0012030341010400b9160507003e01e5481041038035610510f41000090390301e40382d00c0004040d0403107507201c1928010b4803000b5104d8648100829800c00c2124941e2100c0c06010209000902405c11720039030341407044400030a072811036140682c6402c00c00200115010381900404102428407034050b60100c1803000c3c000c101c885101196a90301c80311254004103038005011040301780001c2c040e10103054004207955a4503d40e00b4032949071050303030003e01c00c4c0d4007a050204500d140140326000710080c450710340b0750541c0d44010050f1380741180030700301 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 850565818 1250 850564568 850564597
    0x80f04030804080307060c021603020d0213050106030c030609020403050c09130b0c21012d08030c070302010f020120070201051c0501141815030f0d05030a0506061c02 73
    0x300004400001900150003900c00440d00c4000e5420860296a0403040030320641d0011000300c0d0120380c03d48064810341390151061207440e0003078408204020aa0384200010503c1d1900100303025905802c0120004113641d0306001064503014030404030720452000401c5c541c000f030101041ea0502042041d0300c0003500000055040160300d034038001450440d60b18401401c001451200141d08861103501c1c1610301078010318643c10f206d030842ea1900182500e024500340301d00030110050319002140007519440056070b0f00d9010880305c3d0395030341c07480b40001c0f40032400e086004030030f903841441202101290b800452000b0105803e1920055020040a0307041103000c2203014030349500f010703003007030080781c4844005510741c9800b18550b0526901c0381079074071400c9080e900c601c0844440307081503000351141c2c419440d140c4100002919258005c1c0e07541d0b401d400b501081407580340e00240594810070444005001d190784840070040300f4031034682c40c6c0914802c0001c14080b90030710b940c041c0c003440d0080c000e03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 850567068 1250 850565818 850565827
    0x20f070b0a08070c0b0405010518150402040f2c0111120109020a030e0312090706020304051e011b14100b062b0e060907060816031802101e0516080f 65
    0x2505d0002c580100c4041c3c843c1d81d10f400910803c0005050980419260100a040c2c01c10640550075440540640041c0c032558172408074403184103030b40d48081600c000011024004c4d000200c2c03091080002c010340f1150315440c2400c1d04240116580c1240c0812211511001d80c40e0f00b090302510080d000301152604150f035914100c454610304100800c0e030103181241d080c3c5585010202c80d4504455504080210b40003440100101e48800098803c801a1949071070f43d580e0018004950910280742d11280040d030100707005003840b803941041c0495038991801d5840c0c0c415529401c400380d41c80420a00d8005c0010003100802941c0103507002e054441c05000c0e402e8811001c4003043c1551130542c0a00c0c6550040418031101c150b0402010005212509045c111032a0480000c0450a010903d460038191a00d180c0d900d05540100151119640140a01070345041098010306000e4580c1e0000500c2d240c1c9411601e110f0300402c10b40c7c21404454880250780e202c907985103503981e0040445a8040b24040c0f0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 850568318 1250 850567068 850567073
    0xa03290a360227030a060f020c0303180c0937020f0a020c040c091203020f030a0e01020c010c2102420105030607030504020d0b0103060c020f070b0a08070c 68
    0x1800180344542400050f8070703204691100c1602481c8600219000240f0708005906a00c0100300301d02c00035000000000c0001d000200d08000e0b10440c0443d03051800300204110a59800340c0780d0910008654044070180103000b014081c031104c081c0d4403003010030150009880e40281c20011800d403048070941d0700140903e032889020aa80050140310424400440c0507000c0075810040800c010b03404840a00c50b480480310007429040c918095404000c155406940070f0500170440e02c100c05040c0000c1b20b9450f010000003d10301d4400001c5c1e14018055070142c0106588030380e02500c1d0301ca4024114400c40489148540003c000c000454020b501480764076040da203e51250400d5030540010210114202d84034503101c038070300385107400d540c2e0402140041c8029107000407540e921104a040009040d121800040d44420a00c90700400e0001c1c1840040108260341d0010791600d0101c0e001c803440070a5184a041c0c54204500403a402d10501303004000c5107900c1001046e0b000701d810b0401c4412440282c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 850569568 1250 850568318 850568399
    0x6040515070219150e0907050c0703050709060509070503040b2403060a02190212090d0213020309010b0307060201090503070f02010e060a02030c10020a02150a020c030a03290a 77
    0x544900f2168403200c5020000c00c0190301c0301001000c4549020020084444005064064041c2201003041230111344144e9080d000c114080141d5000021583e03103655400b24500075040d9802964041c540010200c0e20715400750f000d40340125400444001d0300d640d203001d08200d111405803074400c01d0081040d9102952030522400c1d0042100f204003581d95000c40072140d540c8001da00b42030341103610060300d04a0a114090550f543d0781c4c01241c551910016a00014040b260598900f0540910000601000c2d03003055100b8000001c090b416105c101d541c88509901300d80600d20050000d400410004000800060b8030580032441410506a10150200894056007008c00780d40d026074800103104058a00401c81c3d640c440701041d009518041a00030000d445000d0b406020310b0b0441d210022440920158050b102d4850041d8111380c1c5a84403100b000b0301401e031a241405009070300d200f4084001040c1e003409a90b8607809403000b96201c0ca019042c03040052101d000c0010355028041014450104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 850570818 1250 850569568 850569589
    0x417010b010323070c0539010c0503030705030a021201080a260919030803040b0906060f0a15111f150509010302100c06231003051b0414100303091202060405150702 72
    0x90b4259a00c00004055641a4104010b41e020706110412741490005440002140e500040c14a0111b440703031219404000030740240101c55a006004100108090b000003400c010018007940e848002941202200e4a0310300d42140014000341c0100701c010b4446c10082c82d10f0f204401040041c0031802d56079207416805d034105640484076601c1c60742c140060203030b080080ea50001da0449812803c413458030000b0b0360005180c41016101c85802c4010024a40900c441400c000d99617802d440b0000512901000345200002c050700900340b92078030032031700514405002000d403100030304a16000d0742550200300d42614105a03500800095450440008050f400303200500548031307a0107040840c002c0c02c0641c0092004101902c10010b101007040801c0d000290705403800c02e260f9000c4000c684040208014003400320039407044010140501503202e10411001003102d01030b5460000070342e00d9000c4000c00c817600c0310001c0e60040c000e20080c4103601d4014101550030840424051820802c0c5c0c1c08039240000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 850572068 1250 850570818 850570873
    0xc0a06030504020a09020a0f08130b070504150305060a03060e071a0301050907020a11041814060603010b1c11010509030a11030115290417010b010323070c05 69
    0xc403076060008600300040010080d000e482025818003800b00750080c03c01506035044001c07c98442c3c003084c202c401d0382e0a030010b42a0000f03403c07840c0b4540756070085c03d241d019106a0b6095407a0303c164608092081c8105402040001c11064820b0302d5501d43c42e01400e10416982094001c1e9100010001e0444e0800310052a2071050142c8961410007001025500100b0b81410342d007128514600050006200700700c825001c503130000f0300401c10307050005001007000300104403003034001c4c4e44a481d050026103d80308207011802030046000401c00e0086010141110902801d6030351040d07000941e80d01010082400c0600d011800d1500150019141c4058046d0948517410f103012101010b00b0207025081e0b8002c9104103400040d440c0404094000414040c8422110444400e00418014080c00c48005220035000c1c100100c0e8140c2009008120b0348002d140030070319003040304007841d4814074044544615125840e13a00c3d65031450690311311601503400c90307260254400b50b40c12814450a030290482 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 850573318 1250 850572068 850572071
    0x1b060414010609111204050102270307120b0a021606090b0403031413020d02030a02040c181a0901210f060315020708070f08042103030518030f0c0c0a0603 68
    0xc80340c0311a5400c454558000707481050410f516581800e00c08402c54407039030344044180c0400c0c1c0e41d5082060090040100300d10108401b0740c1ca0581d450441d0f031500607800300480030368a4081c0d950007a210182038500001f00b40d0822403000424940705a4060034042d49030780c0f6001949001680d82c0c50803111802c4044900d82480014007092590500c505506000852841d00c090300340b0003104080d12004071002032060612014180c115141400a0019140e0240c0203000d45000c282019041c140200100100c810004000103914241090007030b95001c211200645821504401140d004160700a0704c0c0842140d613010711205031f194031550b907072154140740001d08181180382151901d542603a04005075030050000c0008a01d500c0110b030f215030341c8103034090708040491500e00c0c0a4025a4820310070a8412160482c10340498080418000d201c2e6400304016507030b400c4c0d01d030103105141440382c00b0b681c010300101c514268018020b25030981e80000f1190013484001c0011100c0240342c11040000c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 850574568 1250 850573318 850573343
    0xa020d110d0309030b101a0d0f05010803070215090f1c0510151d2214060114120c01141c0204061b080a1d030d0e0a15141b0604 56
    0x4440c03000503940018034011b040050900d8151b5094040c4402100c04506040c00600809011b001d54800151000c0854082c4034941e0765403480c82c2c99070000071080c0d000d11080700400000c3c21782d58080364124a401001c14800405c3c01d4240310355130700502c2c003910414050060f0480071480c1000b06904030040c03c103012405000c00380d08030036071001c19031000c441d0110580040e4400402c02d44041d90014440814400f54010f412070103045003e00e0001800c40503000d501c181d04010302288075816202040d003007803010f02e41803041c8101080100c1c1d074029107400400c1402034540c800d54904510040b082010b074104001c85603421301407146003d1620643e036000a0400a090300448990102160321640000f05d44494039204005d104660860040043c0150000081684050034184001002d002c032101d01504810142002c555200035074858640c40300009003224042440ba080c003401c2d0340d01c640d82d6400c954000040e6400100d240083c1e400507520301e1014003401c010080c86903000b06028440e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 850575818 1250 850574568 850574573
    0x211801020d090309060f020709020a0203130e012102031f1b090e06040203070f0c060612030f111c0503040203190b07090b04261002040b1b06090a020d110d030903 71
    0x211307560703012074180f181c11111440b007140c010a5000440c0c070b448102507910069420100e0840c403c504065510080300c5001280401c03164043d241a1090300505181e014000740d5000000307099844020b5160b403000502d0314420501c801c4520004500c00d102083e00081000e101c100a040100a17a001540848007001401429410b070360300410b05550841c0b460510301d10043c5441003115501c2e0503c906845580200541d6902500c02000c8030b01c103020107642c030341c0340086c2800718490600e03000419400207000902000f1801c1c2c100f510001c649815030110b003e4040d2003a800c01003080c2e0f1b060141e4a00304002200c0030109100d494441d00914415141102d000741c03005246411040086005220a01802051000c081014042c2407040c488941700381c000d11307141c00903444101400b00d00105001440b04d11220182250a10000c0020500c40039840c0b11b59841074101d90414040c0d102c10200e0026080c081543d401049c0140780c004045007000d408111541542881200001ca201d0703c02c005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 850577068 1250 850575818 850575827
    0x1c020a23040b010806241c2418110304030804120201051501050d02070516090b09040203060403211113080f100509010e061008070605211801020d0903 66
    0x32208121030410000400e00c000034006840188401e010b0f034100210840002c1070b94014825401c82d6410403580d902c500f20000e99100e04aa4240d064a0304003c4d060840f0010054001195010b20321100c40303451801c501c0000e089080000d070a01d0a9503a620994440084030042d07104d00d020391240d020310b06040c60150618409070a80b402103900d00300601601d0414200c611004890918081c1c2e104c1203010410740003807086ca4402404e51082c030100e4606407814082003004c031200c00034108421440541440f858000c1201d00079415004400098006401506000c600060303241c0d1245800e901c02d031600301141d08801d609054003c0c0421480c1c0505461040c14001e004072402404010322807048a5a03150140000100300c01d46400000360f04010940c01070504031f0320b60080300e00341e08141541d402032170105e0080c001180a80017010a06d5801402202c24115030540d425076003c450440324240701c3c40c040d0150a0b2024010200c402e20038003400074100200d052a40021244e149140c082c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 850578318 1250 850577068 850577129
    0xe06061908030a05092707020f01110405060d06030803040503070c050d152a0908060106020105010807030f0602070f0312060e1608040f02030d020304061106040807021c020a 76
    0xc00c100c880398014050712070080151180c804035401e0168407032154100068074104c4003400d1a42c40e407041114000a8526008240e0084090f60250750f450703503040400324282d88038652801c1451400304010820303801c00714014405501381e51400984181c8958800365554800e0310140d40e580d0000c24603c00380a0300a00090081401300c44200404400b0380d80e5080c4840e843c0740d0340021664840480c0503255803444210441d4181c03070049805119841b5005c0c0c00c9492501400c00244a45c1e1300100d4094014450705040e02e42540003000743c40d1540d603e1325009100906e084078139540a1104c0c4000508101e405101f19204e81c55085142106040c91411070700c441e0b100d40d9401d0042c0b8188100303110b41c44101000d110441c90b1440003581d0b00d0505824040074180020741612608045450307842e4080302420640d81da5076a051a44400e800c41c055035264190780c090b00140081200700010301d810605485800c070098000041c0046136000909441010381c044908884000468400d40302070b0000721 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 850579568 1250 850578318 850578349
    0x1208041e06080c0913150801020f121005012f030414032104170a0b0411030708010b013603030306080c0108131e17090405010b1204080d0209040e0606 66
    0x80d82080d49030342c00179100c01040a83c0f01003407070762418507058246005400c8406402210001d5680e0080d24a20030055802416075001c0d242c001004500000030343c00c0e401046400594514410b21400c0c01e00d13030420503081100d40c031007245076041c84d40509400d00203000140500d00100302101c1c00307070b0145424903990f07100303000f20825250440e0400345209015903058609040c5914440e107948c04d0703507606d800c800d07040103404041c808041000700b15041d841d1030100c1310143c0640b840140d40b02006401d071482500000d011032031310401d122900c07240180302402c00b140b4a034020010081da03586100c080b0301030340050b000603441d41c109104441e0200f001e865907071000c0c0781c921154942a80002c4d52610308c201c0051070a18201045081e0741c0000740c401880d250800450391076034114010f014019842101028012030820000140b900741301c0013070b07030301c00d40014544844560b01c039910700031b02342e2000300000111a801d1141d8084c0307403107500c03c4100c80c031100720040ca1542800030810552145072541c9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 850580818 1250 850579568 850579591
    0x111201090b13090b01060f0309140a0204110705030909060d060e07060f05090901090f27050610030f0201030c031d030d0f06080a080901031d0a031709071208041e0608 73
    0x801d0004d9134001e81075044039036628280101e011081d408402800e55504041c2c40c10b640c0d101492482c201c042010200c2c030b4802c450070001c07400034003a0329209001c1c1b10340143c201e8200b4051040c0d2420000e14542c2d000400516601849403107903207040c22543c075500914043d501c903880500040d60011015901c0b05694101682441c8842c000207201c11814020802d4468a401c40f032202c0c0d81c2a0f40004002078080030000c1020b03055a4548640f08501c09401c0e55184640004120340c001c0040c2404252600481d21111401c00d540040d005040012825000c0580c2e880f003185611882d401000404019503014668520203099120180d40103000c0780c0d01d50700e1910b8020000c00c2000687c0e914440e5000311130710384a20500c00140e005118454070340c18001c015480103182240d0124a09a0706486a25080729406021840910b0194100c1e01f130704041d408070100740f06408220945500c2d09100d07102491030181c848403d00c01601400251480b00f12004805219854100300855409881a0f00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 850582068 1250 850580818 850580831
    0x30206070e0901050a060507080c0102040611100501060c1b080f010b130e300a200a030822170703020706140315010302070218190618111201090b13 65
    0x1780501c441c0384036040c140a40000d030700c02040300c0002591340302e50180000b1919a03541e890040d20007203d211850280b4007401d0741c14449000e05120f928181e9000f0344d2000790f030b00e48960755000c2c4445044840102d5007241000010492000c00907806007060310400031074070b041c80600380070f02c0d1050203215040250a003601d41d684060001141140030181100103102010620540d5200c5103401903401c044d00750005000000640041440b43e9503814104150f6040c60b01081d020385501c1d0041000b0009020080451084004d011080340d0294051140050100442c1d840c1103507040810109221114041020400e01d0380601010004229a040441c80b00c501806240f01920000381240c40c1961010605011644294142c0340307101c2d4050700700e4102d02c0303060421008030701c2c0c201c42140c04400032716941a06080d83e0f000710070031a244030050011000070015010003411a200d08880149024000019240300c82600c85000700101040014000902003e20200040d07140a80814a08000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 850583318 1250 850582068 850582079
    0x30a1d070f09181208070908060f0609010603140109231509010f0b1617030f180f0309040207020f09040c030501142a09061803010e0705030601210f030206070e0901 72
    0x201c40c0303552a0519017010300d640d40030310964034070f40b0580140e0058410002000001c0020503172460140c0b0044690391040c1e039070381030b044003070b502000960b6a51060410041201c643d070b540185a25601c1d141c00300108030805070300716019010448102c11507200a48620394141480d08101d4090203031070313410400260405d010262030740304648581c218146d0000740d150910240c01c919240101c562000c4075030301d080c00a0f11580d40300303040d07403802c41c42d04000100441c00d0f40300040b14090440c810010f58101402e6400700002500040c41c140c0e00702c611a1640b0080d9a510321b03030144111300c1048145803140c2181040380c211504c030103222010210440a1015004040c1c181000b00c10a003045007451818450070740c00c02e80100d08032550003403030224008405c04e5010500040c07a482c04e9008004c485200402a0743c0e840240c450755400d40c00820050040c444480d2020a0764001f101d104180358416030b40310304124004c1d01c1c040d40160005420700c007055034015556140c008049500c1800c650501 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 850584568 1250 850583318 850583333
    0x1d040201231801090803071e02061902010c1b030c05070902070311010b190306092604030314040509071107030813030605060904020f1002010e010921030e03030a1d070f0918 76
    0x700151040944d6110450070700007402408d050154003070805900c0765840b07040c040c01501e050221740d01650802d52900c944500c600e5820351480d4000850440c0007545480a844050842005440c580a00c100115600b4520300040185c1c62090b90761040d10f40d481800c180c2190310303034100d082c412408620b0610046040200da02c0583e0b42000f0005250310940c0b41101a40c0710000c3c070303100c541d20040388103c6d0000800001d0402c03a40281c1314905010b44007449000144201e01646500420040c041021070b8411100802e5624183e03044540a640303a4550503030300d4201c044407540c0c001001c035081c003c2204900a0340e40110007580e4801c81c80c18142c0c002102a810418900e00906603e0f800025084c800d41000795000c00c85402000300100074105000c8a49482d803c00c0364078080c06517001030f00b6210307214600c01c2c40d1580c030245040d61940200c0300041e2a0300c0f50750700328510103c1041410b0703038002d00100b4010018182086400d620340804681a15050300100000710585e4140b407000c1140c1c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 850585818 1250 850584568 850584577
    0xc032505070803130302060f07050a08090a120b070804020d050708010c030b09160503130b0c0406030b0118051c020909010b0a0510020c090c04030b0f0601080a061d040201231801090803 81
    0x40321f0322a00c40001f40c080c441c0350f008208020f8814410310f5481000c0c04001c20050500c4001982c800c0c4000d601d43d06c0001c111390071410014402d0511030002800c0c2d0303105001280c1c2180c030007407003440640d0407a01ea1519245290b0403c8100b0395541a00b52102a094820710304502401d030b0b0a10b0280c50403001d41c14900f003004000c3c205000c00000083d09040d100800f0044256205294041c5030508040c1c0d01c4554105008203008607240103244a510740c0554440c4844011910b04011541d08110038814200c046800540550811a0410b40142d4503010907501c958001800010112104401c110b8280d0942d4483c0c3e00440702201c109036000c1d40800c1000f038420094403000415161b01504403128420380d440035040000b09403e02402d000d480d411180111001d0781d030844035450b2885400201e49031031041d1039104240c1c40036030380d1004400300065801270050408031103400301c0305000e085900120202010404000403030710b42030b1180002c0f1401e00a001c0ca04190140d00346462240c1e284a03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 850587068 1250 850585818 850585823
    0x1b1c050c03031c150305210903030a18050301090c1202150f030402101b08091912060510180b03010b032d0a050d050f1903050703050f04080a03020c0325050708031303 73
    0x80424401f00300c2c0c45098110f60210a002d0100c9544101812005050340c429405071030461103650f000040500d0140124480da940000b684400c0529000b02600741c080010803c0b84c1050030101d126140b01c007104003401d5110b4046440f00d6980c40c1078030400500044020082050007112109580b2800743c1d011640c40302540125013660b51840c440000352142c1e145012007401400b00c0c00c010444c3d0300750f4400c08146601c6201e040c805901e4001d20840e085190b40207a9a0718000c40340003d2140f0495001000c44042c0030300002800c042c100080b906001004080b5980c42080307800514607c0d0300b00001c0905405a0800381ca08013005907a21612400c0c940f60650070010003081031070905000d98202c1d040000b044010780c010b80c202113009000f0304400c41d00da80c0824544000654030703000304404c0b40d01c01c691180040f4034186c2c01c0007040d0002d40001e400b45141e488140081284031040c00b40340e100004142120894528803460300c10314001c0ca0b0341000450307400034002c0418410b8544414001d496 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 850588318 1250 850587068 850587103
    0x30515092805070f1d06010c030c030e04110307021e07030201110f0f010c0806010507030212030705130b0712020a03081308070813081b1c050c03031c150305 69
    0x40007694480810825000080d2090046810024142c0660241c0070304641004e02508502c1141c0f010241c95041e046815034041440c3d1712001000034414641420114402d0030400c01d00c41184020408403403024051000c2d0076400401d20410381e4040100f8070703c0c0d01050100080e0340c1c0c6440951522100c96210090610009440740009140c00b486000004441c2c002140e98000814440e54061300750b150300d0801007010f00001c248030754421021960001d070150000c0c80c0304440e5034640101a80002c0896041100901007070030181103012025000300565200703182c90711100c1c2805458480407501c1401550302c034000310700000c0d0300700d140650300c0125a0000d40022040b401d00350715501c2403050052000304009911320b20305030244185e10a0f0f03a0302004a4070481301840c82c060401c10482080e5500458841c0354038814070005422142c1d00344103805885c1c550a1100111b841c5400009403070102e21015000d040c0b54003494810703201e854107030a03208446280b83d500d62035240c0c2d03100481660340703e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 850589568 1250 850588318 850588363
    0x30412240e070830090d0b0601030c051603120b030a0506060a290a18060f0906091404020c1c08010e0f04030e1c021c0209011401090b0d06080604030903051509 70
    0x340002c0c4e00341c400500001d80240000010b07071400c00300381b84007280e00c0c0d404a813404402c400080e00c82c0054840880804000d0303007100c0ca80341c9040e20039000e0006403140d140e171107541c0100a0f44062051040c45032259008140f00d0911034100140b1102c070303410011400364008022065001c43c8481c414400c40c1081d200d55031201140403c07940c1d0805801b401d0f800f610301486c00903c071a844090210410036542c0e452980a80302c1000321404c44040c400c100c00a04a901180050300c1e06d54000c107041442c0c0c0d0300b01c1d400206070b80600404459248908800b06900c04010461150180e0145602c42d40108400c903442c84c051ba0003a11100034540014061020882c6d501c0703001000040c0450b920303400030035020203069442d10910f00108003036000c900410b0810b000140844680002c201019816150011020305101483c807042e04580c0b52148244d03100c100003c2c04100501030180154081e98800d1012801c0d406c240e40b42040580300840007140382c00c10410001c03008601240c500f4800030607050345 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 850590818 1250 850589568 850589653
    0xe0411090622030803011508040525030c0e0f0a060b120c0706110a0e120607050702030a17070c0e0f04030e0a050303041212020609030412240e0708 65
    0x803125124518914410800c01000303002084e00518101c4460310081c450714540c2881c100c40300c04064600800036804002c201040201c0c1d00842200420300310703180b210315607030f03070b1101542e554080d403168000c103007000140503003030981e03801c420b911298000081c01810700e4840c002075244110b40c0c4c1c040301c01c1d0030304020507100c61b8500201c0b40025013183c01840020780300244901c2941c414038204020900c002e1040000e030409510746441802e09034043c2a041c1d40301c40003170710203500c08a0102e0341800b400702040b00280d159890740c000e0003400c00340e09441e2041c42c9810078500006800c4400c1019580040100c0c0346081c000055100b685840c10800603900c003c00300f880d030f540c1604915031501011030045080344083c0c100c8902c00c1c1c002c40084200d4900100c041e601d514050754041400c1e002080140150340002c881c241c1c03164441d00d4800207c1113260030071203070ba40c81000483d10301600c507007a02d116890708002c81006011100d01070b080140a072840c0803811580f40800c00540045500c1503140d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 850592068 1250 850590818 850590847
    0xa0b0324060103110c010e161d07030e0a030e180c0a03090303060b0408031e04030206180d211806211808030103060f090215370e04110906 61
    0x11440c5000c0701303d45e100c0c80282011400781129462030041ca10a550500c95008404410740c41100d16442c0350990009407500d2030040302d440180404145611031040c03140500e010040c07080c08602991711040155548003c0003000800e040d025076034402c460080c460403410b00002c54249000034100005c40c00000d207019006450540e001d03506600005c18006496440800106906c0048401c15046807502c43d0f465400341c0501d0101035081201030003400980d000c4504d0b1003c07040b038002d0448410807119999103032070024280d0444080e20f4501021910b0396002a400c43c110341e0414a90740407141810001842800031180c4071030f0228443c12038040d88801c1e6480514684903c2124105841c400d0902d11919407007807008440a6140080405840311144210b0401742da0090818201d00282807107441950404a550a2030420041c5641c0c40f8103442c12260369948540c2809141003050350724081c21780c4010600003806581001c491000a000c040300311029490115410380d1a482019100c10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 850593318 1250 850592068 850592081
    0xa120f11100609052203080c120a0605031b010806060f0d060b090307080d0e060d0b040f05060f0925050c0609070515120c0c03120c030a0b0324060103 66
    0xd049018180d40da11001c0000d400980560308400c0d07090119880f4190740d400000100314880c59012104d075000800644101851a0004030344c0c80c03418244000b00b09000540d80c1d050324280e04090740c8403000c001d070341018464403452800121503d09060000c1001070301c5508020300c42d074462240001c04406007114030056400c80c0940c61405c114842d101c0c400520b00b40c1c05580c6c40d40c801d10034800700003489000014040c42c440101d42d11242d021501005100e900e0300700c600c12400040d11b402e213103242a26a8824040c1007448980045140c1c105002802002030306000168000c1005d141080010300c0c1c06442c101d00300c50380004002281c40c0b8034004448901a40030109102d009a400740304052074002104c03015100308861101a102e900e80070185144580302c6401405a1034a0010301d4001c18003020340501603000301940d00c0c052501d01d00c8552128100d544640c078150100c244049400c0c240300301c4c0c5001d03100ba00200200c294488580d8034449503c4000c0b0311b501003100000d401a4404d40054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 850594568 1250 850593318 850593347
    0x1030c050d05090c12071802030c0403060e0a0303060f06080c0d0207140d081608061e100302030117030403150209030c0a0909030f0201020a050a0804081201081b01020a120f 76
    0x10009820f2402d64152114a040381c1c40f8030540014401801c03c0780040385000440b40d4003002c0c039441190403104032000c1d4200425640d0540307018000040401c0e0903000d40003140f20f8041c040d00c01504c0178079020b000c541040d00005540321854400380806500880d400d5007007002c1d40d181984a894010030310019100340e480041081c2e08440854414050002c0c800130b0204507a110100150744009030a201009801c640c0300000f02140c004c600d0905000180c82e8a03110044c0d80f00e40d058444502160301120840200c100203a40007004006403454500c025020b5291180550b25252451f1101903039807200150506105600241b0b205680d6810402c500a41101500701803050740c0c1c236040400102805881a0082a003030408611000e2040c401c440040030b0540f04c4c2400d0840001d000c540341200140101d90b14a42003200c29409002c0300c1c2807034020004d88000300489a22003019520750849243e1250643d88130135220700c00071f1425168480700c00c24030700c0e0100e4035081138003085407200319a1f10a07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 850595818 1250 850594568 850594571
    0x2502031303240c020303040b150d02011b0602030106020304061706061b0a02040f020c1506010207090905070503060c190c170c0c041406040e0a080d020f0d0e0c01121a01030c050d 78
    0x4283d24580c0100185101d10300815081e00c2d00d61300c10b861a151306040b594500c0e4042c203100390b41c40040d801003200303204c125841008060054100e0750b51034101ea00a820000c0540d0002c20100000c1e80c0c4001303100e0b0b140c00c50303081c81c2c051400e2003000f081441c0205030440040d03400810080a00c10f10070888031002a400810a1141409590400000398840ca040702d2081c0143d0844840c00c42c0054002130040d441070f401811441d1034400400000c180343c0030b0031100b81c082e01000080c1070794100182401900e1494141d41e9442d60b078601c00c5e00061005244000303210074a6190008220900c038642c55a8004054840c1d03900090641a418039000038031a507800b52806502102d8818044100b40c8900000c1d0b0341000521800e06a00303030b0318440010010701c1d400c81000329600020300d5401409081141d9000a410a00c201d9254400d90360788a18080c11688012855829581c0c010300c86008440040b204001b0810500300300f18a1011449449040c5622100032002d194441d50882c1c0022030345110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 850597068 1250 850595818 850595831
    0xf011d070f121b14090112020d150917091002121e04050301180b0705090f10030902030307031d15071b1206140601050c0a17070209250203130324 64
    0x1840384d081c10103c51401e000e511201c00119038500c245210f4039949400401e080e040c4481c5540300700e0190050482070413160341b00e12076040020380d006101e40c1c01407000503c454603904c4200500c8008010405080701b1548848144000ca40c2000100e5000040130f6100e444160302d80c00f8201e40d240700d2580481d402d9031034101c036a890390141e50402543c03241b103a5a0044c40381c813900e400b10303540e01501c210980c0c80010010310551a26141100c3c440031406800c010412907260740020b42550030144055010400c50f100010705154038580707183c6072400886008105401c9071510048600404000414000e20150900c1c803001c00030b011403004108114502c5021202454020040c016100c001140d02c0580c9000c100d513503020740c0568240400c000000e250000103900d440902041c424500096801e08110600242e01c07200c900d1440f40c80c9002405c944000c1401e990000703000c05844240c2150014403c504205000d5528201201d400c0300403027490300c1c451610300442031020001060014138061 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 850598318 1250 850597068 850597079
    0x403140105041209050f130b0d080d050f04080f030406150f0302130207031418040c050703080609071e020c1008011508010f0e0a0b030f011d070f121b 66
    0x1008103101d18443d103c240b0010030702d02d0056500e14003c3c000d00d85d04c102d40828002150412203820701c0340c180103c2010500242c840c012a480c8895a40305452485001400c7d049891705402240d421004480d944a154074080c0c840c3c0d026401149000050b0800000115040c00359940001002c841041c403100d0240381e9411940c429410b1501c0128011080082800000502442581c03841901602c44019220001b51920215842603210001480030f80d00040c00701d0303c4520403a0a14031007a114183d40e802c1e1802c011388255001440340b441000c0110411002c281d00014a20a610071100200c201c54554002607040c8102c1002c1c0c550130550000d92190660750015a090403100e2485c030500d024003003803100302d5103620240038950901240780001c00c1040c40c0d04a10541c031005508001660320f01941c0081d0404408105a8030030780e46404102c0460380350101c0d010803050600d002060000d02d8814584a0a00213100d00c515100a60004005014048100301d03d015160710801e401d0688030b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 850599568 1250 850598318 850598321
    0xb030f0609070510090b0706020924030a06080a030c02060d1113030c06091212050409020d050103060609270c0503070e0106091202090412030f021803010c08250504031401 75
    0x780301d014130580d4041c1c00b25410a0003205c040086d160509030701c500d00582c545650000e5801121008d4022030b4607c84c04448180c55004140441000d07050199a4203104c0c0c400301c1550744a410002c5d650700050400c4c030000303400180c50020994155142d54881601001140041c00f5092000c07290b92000a2a81c10055a000220003528890b20604100a0302c4032001c44000b12103004102400e41c401104401240e828400e000f054001c43c9091707854682c0b0740b89043d050b80c200501210105442d41c0051040004038040c002c09400e08910800072450380e4011450030302c01c500c10a41a150200c0b8840c804d0120010b02840034210240803203400d6a5115030440c1c011900748210748c0010000c0c0d01c0465180d00f1040c1c40050190000d00c1c0348440d0312161140c42586108040e04814141d44150151207004a400079005020741d0620143e50650690107042c00e59260459001c108130322001040859000070140c0b400e00114a00380c410300882c000004d4a0905c03c94101514860021040e1110300300705 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 850600818 1250 850599568 850599583
    0xc040f0207050120030c250f050609030a0914060f070b07020c010c031202090109090f090b2a0d0e0319110615130f0f061e0e04060b030f0609 62
    0x30304001c000113005105501c0d481c81d00308020021142c0108086106000e0803005400c4d00e890b420360802c803142e507500c04800c91900c2d00604840e211a001418014041c060000fa980581d100c3e01442c0b07002c40d4500c00410610b21406140a0140c0c40145070072103456200c241e07183c0d901d00c204240e0b80c07406107052011071032008882c0500140b10b4400c01c0c1555504c11600b00f810103038140c070307410303c25098440b5010280d0040b4070b50034100f00007d0301c00544844580295a80800c401000050b00249410108841a0003c050048801c02c40142450b400c8581000b24222417180380700c5922041800c0c2c0c81b00241400990034038a91001040ba840500611481c1595009607030704c2e002c01240103180307096100d10003102c105a0300e8100030034912050a20059503910b000c07002030001210345d50407500004440c1410741c0901400c1d07640d407050100c0107240704081d00c2810010f4003007000d1881e0820a8001c150005e1000300480c1d21000750780b605840c204100e40c107440522046c0c5080e458002c202d1a40e0381c80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 850602068 1250 850600818 850600823
    0x30c0506071707050f030606090d050a03081608060f221a041a030d200610321003060302060d200903060f04080c0312010603061a09120c040f0207 64
    0x303035008200914000c1c4d00b1901018202c0320814190365644041041a0b0044c0584681021f036603035150001a80500820920310300c42c1d03c980034142404032402c00d60100002040e800d00808009108050350384c0003c0300c3d85000121900c840d09a07c0d40c0691507520f0b1102004908030f0700381007402c01034014a030007400c1d80482c00d940400c100190880e501d80440000a0350315059000400e04148680c4a00740360065034038036100010b218481c242d09c5c50702d0044221040112052501c4040c04115854210340b41c45d054001c444607168035581105005580c4400c0107241315050382c0840c0070046019401100c011a0000d00041d240d808030507841010700312100c03142c008454182803000701200800305660807818060001c1c2195907a4506100000801030b206403220a000d001c805005841000109102148900c0c04d9410394505000641684d00e960010240c074000002c1c00c2c2c4240c03659009030303142510129414000011100a0a0704011800302d206800c1410140f0b224015030050700140800351 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 850603318 1250 850602068 850602107
    0x30a050d0b060301230307120c0504110f040608090a08040b0903160b09120f01060f03050712152406051e0f04030b04030203120f06030609010b0a05010507030c050607 73
    0x10103080800180f80b0003405039040c080002e0155014422200b00006030404c0044c3c00c80d0401a203c0c1c03030304040a0043e0320101e80b41640c041091210307051500031403203d5605000d4190514104103030011680c040d600071042040110310001c1d424000070003c40940e00d8000490301c0d0303a25200c0c5c1c10600e841c4e1060390307018001c0c07041e4502600e10104841c4008100c49450107000d0426500c03200f04408141c403009078052a2185a00e46c400c54102845414020050030710380c170130120714514240742001200e40c080d400c1c0018100e0a00c000c245103003640d000501c01c82100140c503d13402e0303100c03003c018014040180307060080100818110b4125000740401801c1665407900780c015054501d0b0140b103100d007920b1083c036050004100041c460720301d89030050f20a0054904000d4603000c62103508104895084040c5025418002642030611a00740c11040440081c86641c4c1d805021031031485251040384c0c100800010044181449458111001980328040d40c2242c14213000003080c0d100d280700f0380314250 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 850604568 1250 850603318 850603331
    0x6050d0b04140601142202040801060302010212131419080115080c0a0b090111060a0227030c10170c070201170f040602030a180311011503210201020903030a050d 71
    0xc1c2ca00250003412034804044114011820405118120341c00d01a020310540c0d401362440901952400a440075000c0c0d0000060898a98000207207854800041b080c0a210208603a1603070141140c2002c040d1072240d20a80c80d40407801000c078a204544403ca2101002d042d0b401190b46901034000310600d41030418812030250715800300580f5603032003d1a695100c0c0501c1c104003c6004410094000d0b003105040235404000402001030606004a0700e4003115980043c2d00c060200f0043c40780c42200c076480d0201c00204e490f0b000400d030b0f6000551041e91150800d00810742c0b041c0e11407070512800c41c0c91002602500d08048c00790b0f400075005080103e0128176035800180d401d10880199500c1207041101c6009541ca564441700029800074087c42c6104e6100d04400c2d04d10380c404240305581c2c51013503079088001c1c1301e0904440e00b1202c40c05540000c1d4504418200f01055003244c01180040c02004400343e5094041401d1f07009200da0302415406003c0420440f44054000c03000d0049905211414001c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 850605818 1250 850604568 850604603
    0x110f01090902070b091c080f0901110406050a0212040e190f060f03022404090905070b0406020d0e0306090a0303050a020c150403030c08010509071b02040609090c0f061b050106050d0b04 81
    0x135880d06c1e41004000428440010b100c13000c5400040e60440e0303007080000307a10040103602c210300c1c0d032054200743d01250303000a03080d4000781d04002e201c540c1d85030204514103144c10244450854000540161010410000b881284012035071003e1003120b0054020001e0555440d04100542c441780f005034407421003c01103109040c2d0b1942038400c1d1a56403141c103444c0c1403d150042c001800d400c4c405890f240700e014800318030800e80340000c0020305050340050106181f00840207092201001143e40070360802d1052112901c00040c07815504d07681400c02040c5565000c40e0300e0001e000b207802444a40c4101c040d40d4451038080180036028500a42c0e06209244c0700c500e00303803841c003402e205040e0010813a10004800622508058614403d000d80c60f020214960300040c080d203241d80c0181c0c00003541ea480344e40801080503119001020a028040c051038501180509810810203800403400002280700c7d0070800b0a6000e00081c020040c10100d681144d0300f0003c1401004880c00c40c1c0f442c0c442088001e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 850607068 1250 850605818 850605853
    0xa0f0f14010f180b070311011b0203030105041e060323010e070b0d02130e01231e18010b03070801060e09061002070e010b091507110f01090902070b09 66
    0x10200341038441e00e4a4400c0b0140443e107103d02040034804800644002003140184031006108250180e0b9a400300045846034072130869455080010f503e02d00d143d01590301c0d980110079a81140c2c4100d030300040304403003920310440e44440c2a8450344054070340320000c002c110b804014680c0c141d000700314000400b01080110303400c0303414a80440c44180e2003800300300950b8180f140200240c0808650140c20001d0040c100c001603000d60708500e1700b031041480140a03000160400c01042d002d003111980288600f46c010a8850803d081c004031601e01c0340400029070f40303403a6180c5010406680407050380e5071703584144800719003040c0c4401000071500400001d049102300050100003078020301211349a00e915040040c403020841030141540910b00c030000310004400d100034001c010701815250b45448103c204240095030111074142d8501c1400040041180c0007102211440d0699000c29885100360042c0d8070082103510001d6958000520710b001c00c00596140d5008501850488049075a8140d2040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 850608318 1250 850607068 850607099
    0x1e0a050709060e07080903072433030b150103021c0b0406170607120605031b03061605041502030403120e03011a030c190f080d09060206040c06110c0a0f0f 68
    0x50158400d1000c0000300d1803c06400d1504180d480d0800c10458500403028251841d8100c003e130364043d40c40c01220b1940321f80352b06502d41803c031031541c00c0c00ca0966443e0440310781e01801c0880365142c40040c5a6960740680e040301c08019150744141103210390001030300054130815000e180101e00389030002504880304030442004c400803034098050384d03072444e608444804140d04942e002c3e1361102d82c009070390b84051040b043c584d1002c6c004105603900d110141441c210029100341031501443e0306104445900c00190340c240c82d0398840c83d10301e085c240078089145000c0c42d04003600000c180501e0600301074000c0106803100c20150700a001d080d0354801440c0b03588070500d003000d8041d04540c024a03a03d14200507003102e94202d80c030741e10f15459251544680e659001c0e070040201ca601403003412105603004482c84005041502c018800f03850705030f4401c80251900c0c801c4d04207024010000a20a4800b407003da004454086c09403981e0faa50381c554014407014500c903c0e2045441c2d0403020480d60010707050750 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 850609568 1250 850608318 850608331
    0x90b0402070807030e010e06031005150c0c0603070201060e150f0306040206160213020c0307050f1216060f09120306090614100c05061509010506070201021e0a050709060e0708 77
    0x268100003541d203050b03a40141302c5d40d002e41001012003200f1103590b11100518000c40c201e41032050705500f000280b00a5164822074142140b02c02d1050388400b01d00062140c0c04a9015941c0c1c4e86c07243c590352400e90141a8a4101200c81e041e01020410420344052184182010403211425044000014181c0742c0b0000e44000e50030800400805056070301c0d0310190389810344081d10021904903101003840c2240c111400035009500006000010b0100811464000c41845006410390380304103020b94403680300d960103c51070304018100074002e0000aa10501012087c05d50520604005141c5481141480c25a4001103442c007107021416000b2445a00195215042076800b2000d40208010500300c080b1000c6041002c0032041c1c50000e4010301c001401b50a8a0030b502c07440d080514108042e180050708803500600c0d080c81408007603039000804022a44005500801180380b002007a03090401940d0040c0c5113119103140054513030303503a51100c004c50b034001c0e1b280c21040e01d400f10300b110358801c2071f900c0d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 850610818 1250 850609568 850609583
    0x1080112030f320301030204051f06030b0f030d020705030f0d0c02060f091c02030d050c0c090a180f0b010b04031a060a030f08030609060909031602030304090e07090b040207 76
    0x9071849034040c900d00d4243ca011011800c500d070030920100d03810707186140c002d070b060060044010011030410380241174100b0700c41900452100140c1100300800c628a1140d10200754848050b035440e80c443c488070014500c006000c0c1d0342c048110510113952120b05102e180d000348529101440018004240c0e07101005169840c00c0d5142c3c2c064007007000c43d4102c1409162290b0003040688c2c0c0a649210900a144115060f03240801825004150610895003c0c1c0c40a0100800020900403404104900c220760308441180b01070702c1c0c6681d00001000d4107030f201c02c43d0300b0402c40468107100c03030703a0017601c00148038052080003680ca460b00e484003801944001400480c2840000a03a200c55022403540800054a00d400d010b80c0d070384401c00101c070f00c03c1003510100800400e100450820482c40b41c0d1082c0f00385c9140300079042102259990380b080c4401906020b41e0020800b0455509008442c01490034440901600030004103060b1107480034032402e07240c071b0b2600c5051402810240207854003150014407 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 850612068 1250 850610818 850610837
    0x729070f020d0c05070e09070906081b040e0718090507120c0e0415021612090605031b2a07060e0a030303180c060e0102070e0103080a0e03150708060108011203 70
    0xc10790f040c1460041c100c3c1d550090010105040403020407091240300d441008201e01da10304141e0f201110115009403030740d80c0205c007101d00b01012051803803048110541c0d0004500c55041070316800d150481d0003400720070002264054460819810280e070050080003544c1420b03568803201a5210900c4c20020100c00245004000140076401640d5215001d0400c010026100031207100490b070100c520308a5000c0c40c40c003040305000f41100701e0001c40300c40b802d0a4136907034204203002d00f031400014842161a50118144801c0d003041400751802100301d664401800041c0c103a1083d0b80b0f007121403003281d032071007103140000b40503204101e40900e41d50094000d40941d815038504501610081007010740001c1d02e000d4180014050106d0342008200c0e0f95503d80011481d440024145150713a03110720408268040144081041e11341200c0c1100c220342001d9107012100e90119040020000b2168601e480c0c9c1410494440e8019461ba44208400d07a110304160f0380f0764103003a810b800144005800070340d42c8803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 850613318 1250 850612068 850612093
    0x3020f0103050c041721031504180501021c2007030e0f0616061508150a0b0a030516060c032c04020423180a020307050729070f02 57
    0x20b01458020454032a00c51400d034550000107000811101c0b54501036001b01000a03024045d500c10000044030308283c20710b9820315140c1002c3d080c510000b0700c0d200fa5565581292080c030345c9a682c5000b154804025034440380c030b00c800450100f08204400c65554140207080d02600401403419418145205101d42416800c2d28102d52007041d220445030041c24203480b140403070740c0c0d1401074141c600045049440780700306403403e0360546a00c031000804807a21298207210901020440038440b00901c1c9540c1d020b40d0382d00b4603041c05001c900c40d401e5088080b105001c400d001c400324080c0d108282403146a11107541e03500084403001000000078001415404074007174242540510390318050100c7e100b000040d04c04d1070005007242e01542c0400300d00340551402e681003074400d44200c1c805600486075401c4012030780c40c81040300040102000240380d400030018445078003407826188031540095034012811201400710321030340400c10070380c0480c82c6a08001100e0034400d00170304c40d02c03042e280d01411544000c2e5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 850614568 1250 850613318 850613321
    0xf0e0f0d030f0212040605040302150106090b030405030d0204230d080301090b010c05100e12120c0a180b0a0206060a05030c040906090b070c0201180e0f1f150e0a03020f0103 76
    0xb01c42c2990281d001c0041e0380c4811644011079010314000e020000f8a400d09240c043d20340368017000c4140420420718010040f0540006079a070454130710003841c1c0e40d00d80e00c1c0d1500900b14410240004880380c40418042510b030550310481d070451f82e11019580c1d4140800d0204420a03510140080a0710410801844a04002c0c0c01100d0800c070181042000d004071552000d05007581e01180c03990f600d079901c40d044c154860170400001d54500076a4098507001d602000c40c102294010118203091100040c1c050407a44184e070581101e00c0814250f2a44580b2112000b44945c81114241c0051143c100401c0261920000c500b089400050041103400130a006100240c60190425642c07240c0d00c00c941c901080000013901c0c42a03845030b80d0ba00f0580103c0c40050856407881041c4040081d03c070743d0500c0081e402c0b464103a0400d00c414a5054103549091020303002100141c4842c8004ca02020300142d290740c82c40400303010300320030b0b1a991440d5003a4400c4c044800c41da44000ba610640310f00744518194040d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 850615818 1250 850614568 850614581
    0x60310020c190b39090d050f0d030b06160b0c0d092303190c021f0e04061a07081b060108070515180f01050c0d030f0e0f0d03 55
    0x712800d03620000b6003088070159211042c001520380d03400d414204500340e01c045007a02103002c1c004062078034003c0400e0f40e60004060031002464401c0c0000394520555848803198030400b40c3c068100e0750341c01381745d80c032146c0c031040460003c10200c1d0601c80d06901d031f0b19190307041d1803207100b5005000300c198403d07403209200c821020740382140d914070820440784101064001d048005001c0c811883c040030410001c0d04120281c0c0c1400d02407a001445001e9903681d036484412407029061a010410304c529000055494600402c0c20b00ca0400240c0707440c09560f040340c40b0841428086038200304196680c04400403481c2c1d135000c03008020303108002d4000003c40c0381d40904800c0079a481508100c48000300c141d071600d5001c3e007045483d98025102048030340380c0700d107514002005035041c2c0c504102c4000c0d184082880050880c920070400a6507044a0341d100e0402d40c1c1d90f0358204000c03905e188441000140007041e60720010344109013022822070100348001a941c095141c000c000302240e018034202100100305 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 850617068 1250 850615818 850615837
    0x31305011403070f11190c060804150203071707020a0528081605030a1701090204120b060f061602121615091a180f010503060d30140306031002 63
    0x1002800404d000b504100003d02c40d00c1c0101821b004000608001448520702c5d03000341e040082260400001600500000c550810a02c0026840b070f10740c1c0105403903960b00b910307244010112520800100641c0010780c0880240141c0c01c3e550b9600e1001040341101c006d10440c03141e5010560034901c0000c5100c4000c1c006080c2c3c101407540c404049582d09400d55000403d007100041d540c200d055550303084181c105005181c000d104602d0036150002c01850000101c0e005003171008100300059035a2140665201c0c0300d00000d26441c0d90b10781c2d421000c003e011000b80c040c1d01503010b03421659088400010021801a440210501640d14081c104030340e1130020369810040050b0200c001540130b11507200700c03034802c0d0012001e0380c440101c4180b0304e01e08040080c03c248201e8244602d2501660884100c1e500418203030352442c2c220a09040c2803180c0045400303400b00d0b00910f10b107121000714410904910000c0244d86900c00e420008001c18018003060300e8031949504800206598074461354010321641070b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 850618318 1250 850617068 850617077
    0x3090803150d08040e070206100302100c2603070306080c0906040b010507050f03032d010915030c0308070506330121061e0f031509080c031305011403070f 68
    0x25420340c0d4000244e00320360f0040700c1031100003040c010a1501844101c0c1c0c040c446610700c00c142c0b4034640020304440300392141034007800303141c1c010b502c140000c40d0386072282620645800222201600c80c051072950080340d140b40028900300340402c242001262119410034000c0c1800520f4503090100300040003541c41d22410702a081203044000354050120700041d01c03500001d50f441c0d1a010340301c0780c00094200300515400f41e144406000705003428907414103442d5525000a4910344024140b0068103040c0c0018000310600c003c008200410b8100030103d5602c21000e42d040c50b1104d8664182d001075042c04014031008054000002c02c040a800e031001540c14940580c14031403c82203041000300c428484010182c840d201070001d5009c00b900149000c01c101000d501942c6810460515600039010003809031520603900c1819103000e0700500794854000101907651086540b50036075a6000e441c12554080700381d840010301e50b0107105040a4a20303216036071461581c0c1d1031006c0b07800c485603c000300e0511 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 850619568 1250 850618318 850618339
    0x1050f0a051603020304090b0105040302090f06030c1513050d0c090c021c200303070f0e0f040516300c030f0c02100f0b011e0504031208160309080315 66
    0x40e42c1e49032280c1070250190b0061642c460402800034269442444261305022003000708100503265002a02d82c002004d00c41d6001940710b0303000080c28001c420340c4580d8440c0700400c00381e408800000040c01c0b46580c00d6407401d070a40d622814400040f1002402a04e05000c50108004941543c1c10600640c42c192060703520003107110610f04c160004444203100010078500301c4858050301070480355000115400210b0071868800c41c0244542800c1c004103003000806d8062249640f01c5030146421044024070901c07841c0b8000d802440b03103090308251070700000d08e0302e0f0240211042d2001711010325041d0b00312043e00d1001a20342640509150246c2030100355072007501205204051041e1075948620360301600e4404d4140320101c2c1981c42c1031403640c490500d013902043c4140c0e003140f5201071f1a0803102e00c2c10164403800c0301c280c40c5401194400b40c22808040040c1c01c0386076102d50400c1c800d40300d660b14048030020307501085007102c5500e0802420480200082407407080340460030781e0500c200900000a1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 850620818 1250 850619568 850619587
    0x1b0102070204180302010e12180307090207082802030901050f0d0504110415260a1a01060306060216051207090603050f011b090e1b03042d0201050f0a05 67
    0x454100c5020780d94858590f80190040660a005142c000d01c2410020b15460074070a050081c148612042d08000001c6070010b2032954070180031036801071600050071900c5902504005a503940180b00298840100c0c44240d107000c0c1001224001c0316820303500942c1088402c4005491590003004c8055182c80240400151203000e40511480380344500030b20511418090103100c2501d8a0801d1050401003501c8144107120000d00034680c190a241d042503400844018010305210481c00e001d8031a5507841d2100c40000304a00b8054101e81860354101300295681d48120b0301c5000ca10903c003400a4000802c01c10b0b031800360800b074002c02e225410388100c4c5540b02039150464215038400c4030503030414840800011b40178440e04200724000d441e180c01c185246000104141541c0c083d0040d900001e10220314850445440c0300c00141001100546d02e04083c10514000d00500c9103014404012814031041031802c9020200d0055041e1200da040c4100c2070900c030000d4000c45141c408200081c81080c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 850622068 1250 850620818 850620821
    0x20403050a050a0b1e040b04060b1f08010b0315010e060903010906060f0509010302181f0806040b0c130b07261b0102120402010c050a0b160809070b1b0102070204 71
    0x307045100304000c0c894a00e032031401034500000100b011120302c0e5403180c40104141080b030100d40c0181e01020030521a81e4520b4070b0f0009141d20903070a5041211004112541140307030700e500d0400b540a841d0074245070b036a1601c00200b071200326481410103044c52425280c41d40920005c1014120042440d0308190300c5902107402c40c1c0c1c1c901001d0b42c440b0340740c00342040708000388034181002c0c160584103074001d507046402080ca051020702e83e18000f03516480018000303508840d4841c0450780000940c0070a0b558810700342c4d540300411b9806441120b1850301291144000e030080f168002c800502108209180c83e68003485904500419207a0f00c0280310341a001c07041c841d08201c0610301000305103895040301404480b00303001e800008100e0360b10401c42200380e0701c81403200c141c0c0140e091a211070035000d180b8250381000c1482c07800030040c0d00100d052066903005460f0741c4c2030102e40340d07890f960706544081c107540d0f662045225400410504215405180090041c0c82c0c0c00004d440740003620b041051b602080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 850623318 1250 850622068 850622083
    0x60d1104050624040501032306010c1703040b071716050705070e0a0213080102040821130b0d0b0102060c03010e070516031e02030324030120070b010f0e0705030a02040305 75
    0x3250b20f100010140400d40c0c052003031078405c141028000100d00340e14030740e1064841c0040c048a0501050000060411510b00c042500c1c188403140c3d201e45038289450704440c020000d84180380410000c2115007104c0780003050161080c1070054405031408070740102074400b548070b1141075420b8044c414010950314180c004580c00780c42c442e140183c2d507290003e500d82d070108c030b140c000900b0359004001c200080040042c07441c54001d42030038070950441c2802c2171100e940c85084000e00003816003000010300710300440090305040a150341d0a02602c1c00f007000490b1a010116000703880b00c2c40c1031005115460010140316440000e908000b0320f000980505112244128081203000070071840b00a03103000c03a802c4040c560603280f80021811410b14200c000803139034000800d0700fa40048410301c42c2550b2790941005968031601424203034040f5010b00072141951180c041514107051081c000603204c200d0114203c00c4516200c0c2005851701c1c2c05d1011141d5030f00c040c0ca04441c0300d40074403010010803010300806 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 850624568 1250 850623318 850623379
    0x1030f111512130b0a1a03030901051e0714060702150105100309020a1503150b120c0a0e2101050a0b0a0303120f05040f0506060d11040506 61
    0x50440480c0c54040860000141034500440c019260402004103500690300004807408081103a40d40f11403907155403403045200580100d000c44144880000107500205045503842c1c240940803d03082e00303050740c81c030410500c03500203841000009a60060140c000140d2844d0340142490700307800d501d0311100446130084000e0300b81c004a0610111a8040151409014001135202519031516001070412412601d0301014181c0311405d0000710340c0e0700c60200d80600352102c2d000d00a03c0c4096070080040c42d0001e1f540d01400d0040c8404680d1444d80410780d18400003021140c0159030b101c00306501107800c4807800f0000e004040110b88016500c4d8008402c00600107111000303418107000e0102d0035a540a008403400925182c50001103441d21100101682d0701400d00c8842035a0551803440103011554070702428624210500c020024a0800c4c060414001c070210707a801c0c0c40e00c0c01045000700201c2001410716a80c800c61072090704050b004150b020381d0040001c40202c500f05902011a40700d404203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 850625818 1250 850624568 850624583
    0x605180609061b030901060f2c04050a031101180f030e04050603100c021615260406090807050f0708010608150c090a0b041e051c0b060102030d050103 66
    0x918002040860760204055004265a00b48800c0444801c643d0312201084040c00000040401074250064001403d00780724500b02d040e56800c54064005461180c6007848a055107058443c1201840d00c500580d04100a000041c10750b660036962500e0106000e20710b5500c4030383d150508402c0480f0300c1e00d0580601101c103c51940c6107401410744a107514a54411842d00040c07181c1c41e00d001400c0100708100c2c81c2e0009441d2203500c026443c2ca01c0072040c0e4540c0b82c0340404040740b4414041200300f400c003003607110244180440c5ca0408050200d555510042c4903075034000a0120706103800c081441d41c0074a104500d00401c60b15041e003004084044d050a42d0300c00c0b80e040000034001d116401c0100000c0f40a4081300d81e040209200404000c0c003802c441c0c2c60046100981c580e02c1d10700800090040703a441d11b5445a90b00c0a61860026601110240c00c400240028030b40c10000344400400f40040751040b20300b03001b0360342d4516600015150604512040c000c000b00403030780d07103d010701950050b01c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 850627068 1250 850625818 850625851
    0x2030703020a030b040c080a05070c020901120204150602030a18081902030c0d1e030905030601121b0308090d030203130905090706020c010f03090201260708060109050d03050904090605 81
    0x101030103136207120140c6802546080d440d2044d581e0301010503604403003c01000b081945070014102c0e80641c450380080c1d4880744070030000554402e10310f0b80303c0c02144252403d002d403011240410400c441c49204400c0541c00070092200d0341d61185440211103d50b8603104c5c00c160ba00c94840c0c61170038081c21007040ca0f62240d801c003001946010803501900003800c072012604000f2690740d486c0060580603280802c1c40110009400b050300a5002c80051f08002c0d00300da14642c1d448035071440d401c2c603140060f21100f89c24000f102e020b040201400003501e030403c21041c80c00e4001c0e001c0c0300c141c4003000c4040d02103000c10301c9252100a01b074103658006014140b4045103604003d100103080c20030355881101558840251022540d801403590030040e642801c002403905e0007800184c820402800c9034140303441e0a072072041700010b09044010301491441d51003550341c0e41c0704401501c40700c000f030081d0f40e03201c0550301a078400a889100100201030004d007000c594407289a4403501070710030640781d5005000e03401c5c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 850628318 1250 850627068 850627087
    0x312121b0e12070e0c0705010c0f1701050d0b09010f050c04051203121f0b121f03081c0e010c020c24030c2a0c1804050c010513090203070302 62
    0x1c81185000380445104501c1c6112a400075990006446a180380c01801000101c1070b86000058480b19600080240407810f6114001400340e82c82d00455000304d06c0c548001060900b8590106060761406000020b03888400c0d1a076408801d0002c103070300c44541d29011404040d603898050b15019040000e00c0c991110b040c10200030341d210115420382c81e507a000b40084550450614a9071f90000552054012000c40601c0044032421068000c0740e00c480c2d0001b50001010518042d080c0315544500040a5180f40c0170980d22407010288009060002c040c000000f00502c0c02407102c030802c02e400c2000425039100d41d100c0b0b0954030b00c03411100c0540c0050f40c100c0340b0f50410079088110644102e00c4841103007143c80040100c3d00024017400c2c06541e002c00d41c0600210402e10400906042800044400c140018495501e94500f081d0340d00405c031100d0f00d80d0514402041c3c0302c0c0140d6010002d40427402c80300b40116820f80040c040c0d14494030002000298000a42c80114002c9001d55005691041c0a1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 850629568 1250 850628318 850628327
    0x8091e03040501170906011401050f070320010c021c03061707061b0c090f020d021209011b02031806040e090105010503011b020a02101116030b09160312121b 69
    0x51385003500c00003c0504211440002240450540394500c410032a07055011700104c40e44e01981c00c0c09170240cae10004181d000d00d03070010785001e040380c95035034600e8003240f1801e1064240d8441000c0100541d10074402a00e40b4102c03c80103404008642c5000500c4996440907166607400845e401c0c080c5803ca184d040c00081d90101d04009070703880440003502d0032038a55a58a075020300324845c001a1a5030307a107004c1141601601240d49080d0701d41c40c15501c07070703001c0e05c00808a07201c152802e00713880d840c025a4220781160003800c43d440e8002900510704240e144070b006d4014150034800d046e44040100b101141030001c107210140a02d074100300005880d0305140a00d400c40744804030420384848005103000885500240030100d003079050700c1c0c00240c0c10003080306a51000c0d580d44111340c1406080401001101c1095000d804c0b0390092003407001d40d442d6003000c151a0030214141c1c90b04481010418404070380d2140c503c040690301494204007021002804804a40790504000e080c01c0704c0b80800c0c0c00e4070360301 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 850630818 1250 850629568 850629587
    0x9150911130509060c0c01180303020a090509100e0a0912020a051b06030c0a0e0303190e0a030506061c021c1401060608180102040812070b0c040e010608091e03040501 73
    0x101004008500f000564a0359401c4000c1605488100015420015103820f401c400300050f040756822a08030887d00d40603004c0c4d000741808000150860400084d149070260005002d00c03d000001c1004c141860100e003c0040010940110107445a00000001d580e0103900180444035901a2152a20601d047c2c5e040c8650054800c00c001d01d282c2490980d41d0341c50044a4024404070590340d41e540c1c6480d010f071010640c100c0d031158540800301e940441941000014030b0b490010b9a030f61a980311142c410031061421a00025003203038001c000013505818980c0203100c41303030720190030820304031604d900081c0b00c1c9200c810190080c141c10341162040001c2451505135005910000b4040c5604014000300a00c1c0010a800407984a1415200d41c2110170350440f005890680f054a6400389840480e101e560304c68242200c0440c03034000090903007148035054030192420760b03500d407215034a000c20440b01584043e14030040b900440b010001d403648400c11802e03074184103070041c64980f49020005030130000c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 850632068 1250 850630818 850630849
    0x150c03090f0a0201170403030b03101e062318090a02010e060c150c070812060a1a0d270506180109020a0302062101060c050c010309031209150911 64
    0x1180042c04010b130381002c8441c1c078200110320030140954440c141207001d00a040c8940e50107004119218290090b5030b0880c580d12024804227031a0044ca02d82000102d51861080d211480c09048804240300055200c00c0248035008000b220480e001510031490345406031096180b6500c078014013070071540c0051181302c5001007201c0190921500030100d0742c8510072807915040c4421034800003001649013400355580315811051081d1180758111284034031030000c0d00c40743c3c401d8030b9203507001542c4000d8200e0080c0d800c5041c00e160b41400c0302110700c0405002a00c4000840320407030f40d00c003200b00c1182000a54614040c100500301c03400c000d40c50411504141410046d030380d05000d4010b000d600c401d4038110440381d050f90a00d558096480d10798410311210003a0401461a80000040c0c407a8414004281c42e0300036025100f00945031001901160581c0302c0042c0800c102c1003045600702901c0c1d101ea0741081c00b41380c2d4440c04038031090810342110900002200c05003040668881e803428401c928841501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 850633318 1250 850632068 850632073
    0xb060607020f1002071d06030609030310062f010902191a09030309191a030f130c0906060512010504420f0602011a0a120203150c03090f 60
    0xd46940100d801c005400d11181d000e0081c000403d03602610070060b11006103c00340c290001c200c210b01d03940a4008055030070340d01c43e12403070300442c866000c08003c803401048120759080c407840c50b1900c291908090706482200201e07001507005403400e000c400304400783e542c0b580000345006540c410466088000c60f03a1380718840300e0040621440d49820703110b10000c4040400c15842e983c03480300003071861041222183d0031080c40c0003102c08007941c210f200c10a803000c4c4082d0b681ca691010203a68540e00003155803000d0407012002140c90100040c03c651a2180920310b4448040e485202d038505403404c641c40800050030000740000a4842d104a190140004035010f01140709242d060001c02e860491000355603005c14040030308001c1d5911002c0c9500e00700000d040b0b070f07402c1e41c0d800ba03425020114851070000d5420308080c00c5404104406480c1c00003402031482110ba800c0c41b6009908504240c01243c0601c15801001c00104208480b0351081c45811702d80c96480c03805c03840c2141090b2019031110500d5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 850634568 1250 850633318 850633327
    0x3060e07080709052b060c080106020604032a0501050415111c0b210c0f010305060114030c220312020a030c0f020429040c020a051c18080102070b0606 66
    0x35030000c0d45000704e0b6002c035600710310821a104d000c0e090007113841c1d0251402903408102d0080000d0b40c0c101403201d40341d60302e42c00c006a03a5010141e84600040758000d0001c0e50341d080381d00340e406043c03c00a00001d000820705410105694132030307003101c2013600c1c1604e103908240000c1c1c108141901640446070402100c16003414a21031a0200c0154803845c0c6094803601c07007070322407440e868052030f44081d42c045a01d03000210fa044c0001d5a140c0804d8880d1601624240c014200039501034041c4500031401a0768000120b040706848080d00e40020700304402010080090310440350a13421184003161484e4a124503403841c3d8a450500d0720a0824481c00355049100303801c0100341c00100c402046500003030783d50703501305030780c40042c00400003407050011080e140860031400e1000c0c1001c050000c10290313410050034510110a0784c0d940580c03800146036910101d08000e04000e80c0c4042820203d03581000209240c0f00e8070303050030070940d0340c000c40e405070750110b02502403050303000302c1d00e403c82c2041e108036191 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 850635818 1250 850634568 850634581
    0x14060a110f0705120d120c2a0201030f111b030c15010f090501030302120702190b27030a08130306060b12071826101a1c0f0615030303060e0708 63
    0x2020349030120b40d00c81c581c1e60300ca2803106030043c0d00d0801d5010008c202c0003030078104030300c40d0b804044d4400000da00281c6043c804801200c0c4a01c10156008560000c031030800000b4071541221001449250905c0e01041c01070700e0041e08100001c85a140c00d1003400800ca40c10206d0500a0030440c2e40f0003000d96040000400100750007080501001c0c600706019940c0d200c16001082d904000f0341c0c41305e20000e08072800018030390003000c00fa00360320414000d0750104a10340b00e908213168040710084d0358550004503002d800202c04000402a6400003070801e20000e9507900d4040444d0815030001c0380c0d1a00c005241001c90b6240f0300700c0796100c00f00e0305194055a0040b060030f085030286005031075100060418a0700b0440d00359402c22041d404075801c4410380c24941c0d528001401c89455101c1503481000724020091504040900303d1120461080c0c5030150341d52030b00300380385011003415a101503807018031004103a660400000954001e440100e9020310346165515540c0d8000c1240c01084180350a100a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 850637068 1250 850635818 850635827
    0x160b01080a020f1c021203091005030f0a09080313060b04320405060c0a0201140c0c010e0316062003040b0f1608180304240206010b030114060a110f0705120d 69
    0x402501071b248804100c042e034000c646103100c0e01c1ea00c40e600c2898900142e2089030720600031842054116601d03025a00c0c0e110015050382d8948a009120040600000300c080070070461f00c8001d2401004007298082010740450704641800d050040380d00409200301410205d811440340c0d0f02140d489005045142c00c0d2501500ca1201900d101034000e0700081500d00140b00350800b500350b02c4a10300e04585030400c5100600c1c50342c400c106100c125424811036404500000c0b00759036071802e10300120451207a41c0e980e100020000400034401c0700000000e99514804034401035807103944194002100c41c10b10310300041c80c80000401042071504007210240c030041e032040c0815000f07c5101c008200520b444078a40303042d0301458100d48604290182c4414110304080003850202c02d25030282c454990301c412140c01103202c240912140110415404e803158200074000301000a500d103440f20348103965229050404101441180c0d66911003481480b240c0752a022092513100d645009181d1058034450160 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 850638318 1250 850637068 850637119
    0x628020d0c2703060207060b192108040e06010c0f0501360f111203191404230405040303021b070602100f14010305030a0305010801051902160b01080a020f 68
    0x1456130b600031a21008201d400d4214002c00b000041006d81c8a000d0200206100d01291049078204440c500001c1d032100385004a099605400c4008645032604200f11003104180151a0504010080500700049a034000e6100d882c00e101e0707000440c83c0d55030140c44080a00e400e2402501000503200360035a440c01d0302c0024807511354401d40d030310207008a03402d241e6010048008565000188005c0c4d403141b202002c001003c007041600200d9007002d015140c100d414228142e422a5403c60410080c42081813440d4031829144031045148c0d03030000c02e030000c101582c80641d400c8000c690045020203490107004c00c280d12442404008001262510300000c3d03130b0714194040001d010307a8901c0441c03d42030769900b000030340b120554402c1600d03503903d2500d29606d9015800d500e0010789407900204140c081030042c94000c038103005c019140d50304031120441c0258003914211020100e1140d010001808000d00c090003402510b01801c0c0e074090702d006110b88a040e41c5204c6e88a02c1d035096103002030b000d1104501 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 850639568 1250 850638318 850638323
    0x311120406091404140705042c0c070f1709030c040c0806040207020415030308161803140c031b010201200f1c1a040c0c03020628020d0c2703 62
    0x3c034400140010500810350880340c101090340c81010050b0a68102c0d00400449007020325102e10501d6020880c0d000d0b44807a8402403900b00d54801164200000c0e4001d407035060700420100b0b00340c500c40d1340c0d024048440c08602544500c8007242061107032600f4000d060703510000355804c0c00351458a1720001c00c405402030285104030340c04105c0c6015074a5a6002c800c0c0d4a289170085104207031242800f42044008845021124101441801c121403084860b0050400e000c042043d9150445d80d448800102140e825511441b81c03c54a10a6580412080740b01151040c0302c68032280e0400002400c1d180816540381c000d00042c0c0c240c510041500702120b100345440c40307030300351110203c0c81e06030030fa050310031403050700030f41030600b29003055034289600000740758102c404020600c84004140d588804440c00540984c2002c80011404000c02c440c40359046400281c0400082c0ca4000c41801c90b00300411505c1103a9075011908001a00006402100c3c00e080100710303201000d61041000854079800f00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 850640818 1250 850639568 850639589
    0x30915070f0f0309050c15120108010207060e0d05070206090103020706140a1b02030405040b0d050d09141804060b010201060f1806060237020904060504150510140a03020d031112040609 81
    0xc04240d0007d45040d03c0307088607109111110fa503968181c41c0d010f500058401d640701480e00e489400308150010701000c0b1014903465250030b00360f0036001c010040d00f00440740b5040c10380800c824000034802d072242e520303900366024207048142441059402101d5140c00a100a21030881403c25240d070000240d4088410846000ca20450f41c0d4000c6924680702d110000d00354821803614114040c5c01410050a680420f56400c030044da540040003440c402c0c0c140f04042e046084000f00d400718029410001d00c4442c10300010800e256034500000e030f4022107038459440b040400c4180303900400c9500461004129138801068400c690a0040a44003045c0c1580b25024035480c2003c4459042403410040c002d03001403c9520501d05420201c002c1d05040318121501490b840c3c600e01517130524451302d405600280070300040c2c035060072400c00581c081a040150300090001000005a48010f101d809140c440c0d83c40f01800801941c00c0d624180c038201d8101c207012014402484804e9104001d28101c0e0b008400c6d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 850642068 1250 850640818 850640839
    0x7120f091a0d0501080f0d020606060a0806122e09050619110724060b03191b02010c080117030f0f19020c130e03040506030915070f0f0309050c 63
    0x511015102d44516455a6810000001100075000c5404039000712803c05440010740c212508988414080380d20b180d015106008030520140b00d84400b036440b81004d021183e000d1002001b59190030111174410300000301c0b10038107005001340109905a054400c120901070441c4540d201d41d00c5660042114070300100c014032004001000d504102c0003140704860865450840d1300b8010900201007941508c0b108281220803100e103a148100070441d400f1200e001e0a42c1c0303031410040c09207501d900d0010601a02c0c0c08028046000d0321884404048141d000055007800e00c1401030000070050307100902101c101003000303140420100803036400b250300c00000790f030b070b500500210102c0c4d00800a5034800d210041c0c500d10415500005c032016100703c21240c621003a802c2c4103e03041034030100d540c0310a00c0d8105002c20403481c10b088026540120b803c0043e035806081d07100f1000e51400c0c04507080f03c0020071030811510104c0c0c0000309081034045c9480c00740300005840d06d800e561219a0741c01c041c012100d086 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 850643318 1250 850642068 850642109
    0x80105060a090c090f03111008090a12050409140105030105010e1b1b06090a1e08071b05060d0204060305060108042f040c080a1a101b0b0c07120f09 65
    0x2d000090200940031524007130700d9041540d101311090303803d203006074250748083c02c4950107808050b2152b50800002c0022014540d14190b51024031130070b15042c81420300c000300d0001d90b076015801c411081012404201d614000401d42544e1042e80b04210100c0c00d80c3c20f0140507480d50190340403d0b0800c0c88041da644110381c844c045948000003524007540180400d101da200d40c041502e12003180144078402c40174007035026091445886080061484408001000010366890051146850142019010f030f0342d4440200d01c503a84803040c01e0b5107459000034148007554041c0f0613250040406c0c60100c00b9840c10b903840b0f03101e42029800c81d080140700444004454401c24081008a2801400c2803090300d00d03031007014081a0040d500110110b0810400507400340c8100310340650320500500d00c4102000644080d11040502c1920003000503400d00004d01013464001542d00422500c020191b403480315007421000e0b42c1c0442c04903001c01240c00207051205a00002c904140c40b051140244600c1100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 850644568 1250 850643318 850643327
    0x1e010b0f0f0d020a050d0b030d0c0212190c090f09020d020607060b040f09050c1206071101061d041101080105100509030f010f090b252a0b060a080105060a090c 70
    0x1070400c1c90f4000103261120940c090041c003d40042d424041c0040c1e54241c0805884e000c8071080d220001d0807449948000d450010981404d13000c6000649644d03059020740e9511106500800f5100d0000002040104056500c1045842403c0c100c080160400ea6800540b014855003c0603109460224402d0144005584013100790b2030001d000f044a0400c00d5580f6020307140030041030341c4c54003c10380014098140300c00d4440c03036002c400020f80b0803035445050a64000c0d6005046140941d80c881d070104040400c800c01800c1042c0f0555062a645828038242140d040808020f5041010903401082581c80310307440003040b01014288644c498030a403020030301d00324004151400139803e200c0c1803401d51245601514403e40500070035039950f500c245030540301c5600c42280040301e000e01e030090701c43d0500c1940d20005003850328004010303480083c406032001c203a44600c15205505082c09000a924000f01214000e0602000a0044d4507140c000903103484010310a03202c40507100c2240c065aa4401c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 850645818 1250 850644568 850644577
    0x2b050d090204140f1006020703082d04030c0f1211010305130f0c03170a05030103060504032d020106080a0b16090e010b0c060609040b1506040f0e1e010b0f0f 69
    0x7410030442044c90b1003a90781e078004100750345040c08051030200c00700700248045510701c107881d000800149449504400322580140c44040c1400d0a03280740213542c1c90254260092000310700034500d1801322400d011403141540429480001c486440c0c4070048c0028a41d00e850304000703075090a0002c2c1c1d5036240010a0b400000f00c45006281075902c8800104102401d441c14041d00d0065a00800005a402c0098000d1150180301ea000c60428401000080c281c0e4011130740c0320340b292801c21046442e260f149400584424580805000d0380e000035000d1383d60912542004000c0d480c020007100300c403521350340804800508401500c410000c102075200c1d004545800061001213080e81440da03458441c0440c9802402c9140b0040c0030382008030b5000d00d0020038940c045c0c2d0b040300c0c0c2658a43c40319040e50800001c8041e01030381007801400f0015040002c4040e0000620503070a0301480d0f4030307060805541b80c9280802c221819207410006111418525044e80d803010b004429040c2d0b5200201c0c45403425014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 850647068 1250 850645818 850645841
    0xf07030204051003090b07050310030b06030309060f0702040e0706090308090f030f03120123090712050114090108032a030c03070c0e0a0903020c0118080f2b050d090204 74
    0x4400001d0030b41e0341940305000d04c07401344c207003a81b040d22540001c6a041c8001d644105000f00700d0501400481c3c40c1d205590b400200040440f4942504800850180e4201c6a00380302800c81c04a00c0509500300340c0a08d90741120010060090941040406400e0003080e0001404056001c110200c032500c40c06d40003008501e006003103031110351354440b411b03940790b1141c00d21002d940c65070000000e9050800c14040e640c800e1005164107540c103080b05001c1c04250040c4054100460780080c0311103558148101400b0340b402c0003403948240c10510602049180c1070303000141c560320811000d0405090b030303014a4148211302c000000c0e00c580791078140f803440c044c000780c20200380000542c040402034038860a00440704840039114082c0d61744117450080740c8001c20f014001d42c12200500c00d1940c803810b107902c550040c1c40000005107848030b10641c0340205c15100c078801030b17207c500480b048403003200c0e00700001800d0722225524030108100c001c0903401155140c400c02621040a0011542c554024080d9080c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 850648318 1250 850647068 850647079
    0xc090e01081c020705010905130f0603081908060904230105152e2003160b060d120e0112020307090f170303060904230c1807080f0703020405 62
    0x5071039100c81515441625141c1c01e00200540381a11624008540d10040303038016120380380882d1802081c0718522000c2481c9419256035810041281d800510036500610b00912600352513000504010803d0840c0009110610424204024640d50f81300b20256010380c2c032201c1d41400c1c44002414100a500078507101041d5404d185c20061420348800000e20300b4041101c900e01100031648619a56807144403a2104000c1c0c1d1540c14156140230f60b442c9901524081d0640401c0301c44510394900b035420522100010011103404e84050110314030300700350004c104076440f280701d0720941d50340803290040910410074405800c00d41c03c8503178046c0b034100f50702502202c3c2c2550340e0302d014a0300a000c02264010215241d00402010401040c0c401074541c400300030780011131554a0361000c006490030020400c69032010411480401404120b41d030f4101d006003d0004d0602c18284010811101080d4411303001c0d0b114490100802258000c40c466041504210b03082c0300790702d50030400c5000e48102d03000702d41c008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 850649568 1250 850648318 850648321
    0x1415040302130e01140603031b2401050a0501090f0e0a14090d120e0325080c0a060b100509041503120906080f0705030412020106030506010905040506060d0302030d0c090e 75
    0x103601c43c1e00541e0507490359030f0080040042404940c40390b81c209640081c0c15500078030440c10701407150100c02e0010400041280d409903043d810ba2101c0c00c103101107001202d414400108141e040862101c80908000d0820450307083c1090805e102e64800c5104099001d04d403000450101b415030350103500c290344202030a600d10710f84030725580d6541a00c10070313403400213514180310050784d20f0700d01c0f50842d69803519016515010061009655000002d032500c0c5600041c000804005807114000781903203031420026003500000c50409404036031864101034040e88078003144001107a441011038003003150031540008d1100e5060281c0050f200c09030801003e03031180110440c400341d044082c61084504540da001410755407600c1c0c48118907015900440131420500100700020100003a4409020051000044c165a00c0c0c80f854503100e005c0c0d100b80b054981c1c0d50144000d011040c0f0403240e001c94191b42150a10000c1e0750000d43c0e82c410006068580c954401e060b01ca608c0c07142c180f840c0148800c0420850310b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 850650818 1250 850649568 850649599
    0x30c0602040b0403050f010509210f070c1514030a05130c0e06030d020c0a05090702101b0306050f150c1e010507110a03050319110c01090c08071415040302 68
    0x160f10600003a81d00b841081041140600140141441075074030700701520400100a03512201a40035150390070303c81c0018002c114414014101610900b40100c50b801095450071441300b0050a40d506040108041d44114841c1c0541c002c1c02c581d041601c010001916613246a03c0038000c0d0040400140808002100000d808080e080300e680034034422400c0d2141130021880982e541c0401d85420b0b60004132010f810420303407402405095011840340192035807110070b036040d80704855180c00c1803918028901030458011340e16204090180600751011180483c4050001d1141000480c040341c00600010b85907042201c1405130020035154401408450b03412104114080d000490719500010050056407800143c0021114902d075019140c40b461501c6140030007070000907038a4590803254548000580490fa42001882c1c000c0c550b00c0000b4088c43d0324036000c80c0d03401c4c2c10b500182e240c0d80b040744140101010703140591000d00080721041194075504242001c1da024581c0003962054065804c640c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 850652068 1250 850650818 850650839
    0xa03050a060905070605070b040b13050304030c03030f051810030615051c061805070c0c18050702030f1803070b220f060815011e030e010f11070f030c060204 69
    0x1220720a0f0151030900e0b440b000c1c00c8440e8003c2901c050f0081000c0c80c003050100d0f540a9034141c0085241c451062003c0705074442c145140c0c0568404c82e090b0209141c00c0003850390105051882c02c0716031510750700c0e05003c0442d801502002040c070600c118901d0325120305982c0241d100c41e00a04000350140000c2c629914064240d402094000340010700449928450b00303071a1080c01c081e01c4640d6808000c41c0e1285400c8001444002d0800c4188909990101c01240b0002d0807400203088820f80180c8160080701700d00c0aa420107000c800541d03009004100c095221403041d01c050500c0010f0401c0c00031654400a850146564440070300354800180c06108483c13410104c510314032070307100524141645d5410124102190b8031402c0002190700b0040f403181c01c042484100021740c14500714110f0395072840c5040c0d404022a80c0c0c3c0c2c4c040703942e94181c024000d0082c002c4c0f140c1201d003c80c080200b00311000f196802072162410007440403004c01c4015080501403e03001841e141c11040031900c680e2102034640 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 850653318 1250 850652068 850652081
    0x302100210060b220e1b0405090a0c1b020a05011b060203090705010207121502030903070c06021c18120305040e010b040918020a03080c0a05010e100e0303100e060a03050a06 76
    0x20000100556504c00001407071210840340fa907401401241d58a40f002c40c03a591043d480241280702c00c010000d401e0b92681d40c45e1340940b204850000d50040030315805000300404801a64844010039011005650360154010480340203007090040d0032081d41d0800b011040322000203054a2001c814020744140020701c1c802500c0082c0c0032905007036112003426a8104400c2c80050000002884540c40d031480f503009180c025036003174100d078200101c69503144018003c0e5044040140d110092203130340b002011100748242400303401c00a840004904007041500c00600940030110030040703a4008040c46001201e00510401d003032134089507100c0c41c00c42c100b03038058400e500d541c6040c81c917400b402d900b030300140030003861b4010040000e103840e5903181600768201400c203000300d000700130f150350214200780282c03e4014070700e002402d0007900c51081c4d030088910780c002c035521076801031040150744800880c0b950140d071440300745202c8650302e001c005507160082d0340004185014450542007005040e41000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 850654568 1250 850653318 850653337
    0x405091b040f0221071706010c02040219020a02280b0a0216031a0115120b0102030910030b09010807060c06020304051204090c0905190e1b0310030506010e060a0302100210060b 77
    0x300205d031103211084408000440c01c19020580d02e50104095602454100b46900d1000c0c0025040c0400d00542c0304043c7c840908580258211040040c2189000c440345102c40c403441802c013171080701ea0255085454540d00403410030110000e17803580000d00070415200110324a030001c120030350b00e901d003440c40c1186800c409980000c400c0d0000c200d010f04079406603d0f00415a650403050035426200078040d0405144103811f50000b0003c850307050b11440d1a880d54103003031351404034041038800c0601c0700740c1505a0120381d040d04000800d01040350305c4031800351060780010f00075842c2d840c2ca0a000341440c02040d075182d804000042c0c0000c42005542151006c696135442e040c5030310365070390f003404014007600c400805005402c0f001442080900079080703820045220a0505100c081e880e480400c1e80140c0d80c0d1381408000c00350400401c030b0108500c0d409844c0b00703851100130742000780c0800c0c0d6085c51800000d1043c8a01c925108201d8070804c5004401c684681062101130740d11090700c14540e1011020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 850655818 1250 850654568 850654627
    0x3030c0417280212030a23030c031306020d1b030b041e021c0c02070e0a09170304110925050301081c1e18050405091b040f02 55
    0x144022050100c1c0321420032900a02e00401c4006040c896840b072810510100d0740901040c840c001141000c10240c0b50480c010b850344070524070f1112408803ca83ca80040b04444141081040192094102904c0c3c01103108401011411210b02e80385010b170007003500556505240801c8020100743d14041903007603101d05e0705e04002120740d030824801a80c50240121000100c4d00070b178110940700c244d00600c0411a1000e88004440f0095030b00010303500c41c00865001603006410501400000e0940b00f07801c0303000b007441007000d110903070380703840003108140e9008002030404030008040c04107055400328441c6000b8940da105182c0b48490051000e0310b07000c042c00c4000410200841c1d1400307101224103803500d01c401040b039600021018408440c4140001040007460304c0d19000502104d5840c01003a41e080e15403003802403090961141010165122038400e50500d014000c00c030101050b80c0103142c0349a1002c0b1604611403010502910a01d40c80074490f601c0025a1451402038625211000212028 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 850657068 1250 850655818 850655849
    0x1050a0b03040b0c1303061112180a020f270f0604020a1b060615020f06151806190807053c030a021003050f10080705130e03030c04 58
    0x11110340c0c81c002120024103c400301c1d000b080720400440064050307221600c54a4403110303200d5403290240c030b2000565415071480031940c94011919422807507404880719407200c07201c0c1541c1c0c104956401c413501000e4003a000094810f009038450510031b0108c0b02c80f502c90b600e0200000c80f4003990128045178040f80400a230300c0801c0847c070f028000c442c5422482d50f42c01d00c44590303000b11041c8400381a14200d980e04da84010000e503942960301d0720f020390405600a00140608a0b048905140008003140e021042202080e44aa61010500392102c651b41d5013400e81591550049207000400140304c00c10b0300220300000070781110004103030042e01c8007520040c684008680741c03d100c2c0c2c42d1200e41e640f00d00c2202804d0b10118407140d01d1644805000800b1501c0400e215004148041010182d040000e5100c20800002c00b4480443c41e0b04501c00c200c0c0a13a0343da1500000c00d84408081c0202c80c030442240303c4038003800000f50024031200a210054035500d04091038807540c550301030b101b141c1c0032803003840 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 850658318 1250 850657068 850657079
    0x3121104060810081204061107030203060c0304060608010b0616051501080f15070c140a2306070c0c26030a09081005100e04240b313201050a 62
    0x300740202c144511117650500342040003d82d1404c0c400e9100c41624031800000202581e810810940596070f03580203944d0300d0a050400c8804e0740c140d6005031200780e04001402c580d940344c510848040d05170181d5111013441c414a070181c00c2100070880380480c60450340001c10030020201d900c003490140c2008499400c900f1600000300d1101c200c9280000c60355445068020403c4001084a01980402030341e44602c1c807aa03405013101a9210402440002e411200040001c204030280e004916410020500308040c0d440c022100c0039409002000c0c41038124010100d441c0166044020041d14117032a150003002c0d8004110310140d1180c0c004611503140039038045401c0c4d00c40c0c1c1d402044103610426841c2d0800b0f56114240c40081c1c8101c5201c110709608070650400c480e8010b000622200010910030340a008100d100c08a5903c01e403010198580d4580d4421807030302904110501440c004a0010608440fa070358007186c0006003040317800c42040a201031241503a91034160f0f503003101c10b0b80043d6200c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 850659568 1250 850658318 850658323
    0x151009060614030106050c0a0b0c030a0c0804210e030f0d090f061d130203130323030a1a0909060f01090b0108150f0a0f1809050a0312110406081008 65
    0x201c07031078220342c82080140143c1c0d110700024001e01d003030481280c3d1008032958a8400c9074000b20340c05051441c002c070a11082d24640c1c06422642c080902e022103060400380c0360150302c400d0040040d04400d4203891890390090145288521041d401001d030703180c1d1801940c00c251945a800752660014548200c085035880c0055140d005903041d03966502c1c603030000a12000700344203020300f4842d400000700a0707140944240c0d0005510070080d44900c26042d2047e8030300032b88801008004e40c501141d100002d10b0200c41c0890a80c0d9014a540c2c4000c90728419007100e082e0510710310703d41f954004419004002c4000e500044140c042c660340c440040d00790313a8846078402221052200280060f144e000440c4044660a1000104210003040301d004094108005043d010069110400d503c18081003001a02d10082207041005021a818840b0300e8180d17030385030b45456442d2001424032182144050381101c655008004001d004180790355901d031940c3e00545084012280d600849010100211300782c0c034007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 850660818 1250 850659568 850659587
    0x1504060c0c051903020c04020c01020a090509010b1c090f0b10211b210303050f0112030c2d111203031522020a1d010207120201021510090606 62
    0x1005420b500f106407058140e040d0a510003078086210f440c01030051a5903500c01402250101e000042c0c1d50302520402910115051b4402c0d440b880400b030042146509690854015403002c44680c41c150187d241c090b070090400c0940074004078400c10700a800c00c407520440714064001d443c5017005181c0d0320000c140800900b134000004d113018042140b000038039951201501480c2e4240956001c0e901c4250310150428114060911003840e8a428020315400d441150303000148599600c03565810110683e40c82c80e004071004040080c00d10b054018099107105a105100402152800583e00d00c8119044444001010380b0882d02c01032140c45039181c01101c0c541c4904008000d1801c691320b0300700641c0c181008031480c83d0040b0340c150800078403010341c0042c2d807544d0401000051720b810b28080010410a440b4444e039141860b1940d0103110f80e0780000c0c044040764120307014078120700c51a20040b41400c480340c0000c0e560315208428000e01d10008000c500644100e00c40410bc01b41e6100c4c0e044880a01c13 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 850662068 1250 850660818 850660823
    0xf030b01090e03090645060304020a05010f200c01080c12150d02090103081305011701091d030307020c150703091e08031201180204080312090c031504060c0c 69
    0x1041100c1256400c10001802d44c141200d80241c29205603508103003600d144136141040c204c03c0c034a000703075000d00d4051881b6058280503500c40e0300f5440e195003c0780d40015103001c0c0d141032240300c01240c4c801c148190307007682c000142942d9050074008400140f0781d580304102500d50100d2901d200203410000428143c07508000e00d445440381c192a600642c40d40144001d01042d04000c0f426a1b08000d44c0b1807249c80350003140f00d004003e54800564030000c1400126820407030400140e034021001d5031541e0041c05042d2a8240c200080105100d10f603080b003000c13405000e844601001c03080203002034012503803010501c010790701c45484101d400e003010030070312591307400502281503c07005000a07948a4600320a614203031401c40340164071400c5503450b607000242d803912640000c00062000c0700b090a0b1140441100740015070030310b8180340849440780103011070326a40c4004100007501041007000401100000501500e003840c403141498501000216002d0f1500e5081c8441121180e01c50061091f0454 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 850663318 1250 850662068 850662073
    0x1a100f0312020c1518060d020703050c06220b070203071502130e09031213060603200402040b041203030f0e0a03030b0906030c01050307090504060b04090c141606150f030b01090e 78
    0x849562280017072240050700183c20001c00d0002d81010350443c4001c01d491806615550380751010f400010740350020040200344400724260340c0394078411600c0c100708801c0da800b444413085c5e03940c1d2160882c914000d4010207032208070340c0e90070703804d035407405078003c5c41144480701c0202d031003985848000111200130f4410506543c0b040000c0740710404c07000411038004464183d1409003201680381e640c195281904259006018401d1001d1440f481d0301d410342160783c0030354041d8117282c0f41c03000010060145116007080d10680291840803d031081d8032135100d14030321000800088550258803951248064412030110340390503020402490101801440781400500800195241000454481d040a0500d50034440440e030007043d039660718014240680f90340341825841d40c0c0f400b0003510503500030048020074845016041e181ca03030b5810048801551030220000c6680c145850450000d10303c0f10810940c000d24080080303040420012240d080b00c2c000c030960342041e40c8503014601140d032031001c2000d003507 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 850664568 1250 850663318 850663327
    0x1206051b0f07020f090a1418070501080627011403030f07030c02060d060e1b070f03080907331706042304060c030f091a100f0312020c15 60
    0x401c4840300400741d981c0702030101c200084440c4041202070f54182e9000e442191120f004150b040d000c01c1986600200c4601d1440303c0f02044110703d910349105000d8141080004000189213485492500d4031035001d1b05000440015105141004683c0c20b0140341d44106441d101d060507450b00000b5520094443d0248034076001850303905580400025404a030007800601c0780700c940b000f0510690005000c0d10420a4291500c082c3c07040d00c20010800078904201c0c28003503070700031500c50b4420441c4245d060914003a03648036410710030300e01001584101c82a41003046105081440b00c58081f42030044940360440300d50707104009507503201401d000210380c20011350016002d4078007500702010a81011421021081010940d041805001c581c1958410340b01c403203a040581d414441e908071a041c98504110451423540c42c0625480c0e001802c420741100310380410b104000728590100140b9502c2014103c003684d92a01c41081c01c0c02d80e50760009401103203848501c0d420442c00703403801c040e1800ca055240 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 850665818 1250 850664568 850664587
    0xa0b010c02130b011110020406080c160609050319021606020102120f0705070204020d02130b0301081509010213151101060513020a0c0b011706180a200a1206051b 71
    0x5001440f0407904005138040c00c1e45031310006100311a200018000c0c0540d90b5824000003a0540350041d16420300f04004000d0039051b440c00d0310400c01220342c03114020500c41807504142c1d1440c002d005240c17040e46841a0000e800d04d40004424a101940d0707103520480b40c1c0d072840168201c1c020311541502291204000421051600c0f00c141c1e03002d0840d0600e1420038004e50040780c100d820002d031510070b59a000514290004401c0f103041c00070280000d80c0e5181d981041c203a9900c43ca4001c1410254081540104080800070b405640c1c481c00070a80803100b0658a0003440040c031035080720030022071a5800503003c0e002041c05680140d13070016090010045884640e50000e502014401e000c1004034228500040d2547c8115030080c0500d01421401e024080310441c24090040c0c6203c1e00c0c0801008041c07021a800b0485205c242d0b04040d48001010141c83d00041607091100800da009217000d074041500422000b404489501034a402c0089594031ba0503803141001c1200000c4030442c003441307282030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 850667068 1250 850665818 850665821
    0x3101b08061c0b13080a030b12010e100921022a0108040f05100e1e03131e0317030403110a0203060a150b18012601091d150a0b010c0213 60
    0x10040700304207131089803100940340c001c080e801c06464000025200d185000d0307280307008000e5002d1003d40b140200200d41c1813100c0d10b542d4001d40f204080d04a0340303900c0d6080a0069000501c108800ca000d0307400c14802c90039100039203880f0181c4543c0310200d0f850051400329510300321f00407035269041c0c403010000e4503142c45914007c061100e081320346116408211307545040310300802580d422200002e010010980444c440280316601c440d50042d81300340301201c03c1ea440411480c088a40103511641e218102c1c05808101444681014001b9460f581500c20b8400340c1c407005620681c00f9584070a0800350140003242c039900030081c081d500d54061400b142450a05a012198045480078580001076a030250103240d5000000e103254504880ca140065070350300a83d412007904601409800c64895078100340d901184180101c54140e9990319500c12740c58040a4003842c1c6100322811a0405c1a02e502111842c01049a0360340324542480000b000390750284800811a60740204030000184510150a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 850668318 1250 850667068 850667071
    0x120302030a020903030703090501080a0e0c06090a0f0e01062606040c0201180b0109140f13020a030204391b020d0f05100516050f0903101b08061c0b 65
    0x41e0034aa0802880700140e40400081c804a48240c603800e00151608001503c4d00c04e000b0801c40300307903050803401c00d4005000300380414070ba08216255503c40d660240031a105030590380010000e00b01a0390f001c1100e000300006541241c1060341d07080e840c0b40010200f40c0f104411500344100b600b240307901040e100d180507004090750a50601c00041c121035002000c8240010688080d6400e20300e030001801410203038001c3c81008100c11500070b074682400384092401000c003c002102c0d40e5099240c1c1000c40d5107505005009540081091060134a5950380c4c00ca001c0070304400740d00f0361140c40c40c680449003104110380d402c101d09844000c98400303042c1c101411a90740c0740d401c0b41d000051000003000100131707510307081459000e01c1c000d0107801d054580c40800c030b42c0003030100114104607080c2e042c0c115500c0802c54151102c1000c5494075008030030003092402c003c10394040c0e45141840b91540f00c3c041030f100810a0311a0030394a0803c162120820f00c000c50140c0394141010054144605011540081d90b09 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 850669568 1250 850668318 850668331
    0xa05010302180406150216081905011139030a230a033201030f03110609030a0e0132040312020d030506090717060f1e1c12030203 57
    0x241c0308a040b00b00090112501c6030000668072080031418000343d9030421003102e44031400c0001031071050610740c40507030303030032112600264590418004030208402034002d8400d6800341d02c8203d440e030381c9001491000f580b00750103030124291040e2402d0122000e0100c015826005100078500d44001d040341284c50040c0c0d01c00c0d022040d01103034450100031000c00001e00d4807108564000a881000c40d075400c409804a4403105a00c0b90400c2c1140d034480840c62515045036800380003d16034408524003690b901205045014050040c0410072002c05000b0009080703070317122070b80d5210942c20100d00540d403140f5002c0140c402c49185031004600030000038010400151141000740c1040d0b500c2e600d1100c40720303143d08080c0050300880302540f0034503054001c00c2e420010441e5048107c3c03926140040c1140907000e0584070344c400b0383c80070071800d03141d9045420765454060080d50180d030381d01c54100e464182d0503100d00d0080c1c140c1585044a54911000b21b00b65942c840f00009035240c0c0070800310007070b4001030030740c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 850670818 1250 850669568 850669597
    0xc072702070b0a110f040807030c080304030b1501110d020c0a150c120507150209041d060f070e191a04030201020d050c0c040504120306090513020405150306040528020a05010302 78
    0x140c480c58803850700941b008283e04001408500c2c06c6103000100340c0080d034030440c11540180000d02c0040c86040d001e59101ea01203c00c2c2c2218860a001200c040d080c900b0710751164080e0941821103030358003258514010109540d69052941d40752101c000085000710000c0004100607a00d200045001140d4640041545007a6080100f56110304594a50308843d016030740b0350010b4103a002d414a8001c1400e83e1914074980d129030794100b0720b41920f03500020a8140d800742d641000400c80b6005940310000280090642d2001c01584d9801e0500d10115000e07031880800000381c59090003001d102224140c87d4182e01428441403481406c0d121a003001a2224843c01907030404100d0780c4817849501d10590140300200c414001382c50f00a42160084c0d0040040ca900301030400209290264000701d07115819900018a540d50b0420b4112038082231b0722940d8180240e009000074868001140a132414501d16000000c4800d030000a80380b80310780d1002500300f9004041002a98029805040c00c2c410880700b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 850672068 1250 850670818 850670827
    0x120306030a12020703050c10080106030905100507030f1b140309100f06140109030b1603020c060f0f0f0403090902030703180c090b01080f13080c072702070b0a11 71
    0x158080e0481c02c441d10080107a02030701c0200180a03040250110f50081a07903003019030800380200500090050162030281500c9030021f00c2040410005140491010360040105081c001002009003d24108000389030b81880d103c50481d01010100b000c04110030340720700c1c1c0301d100051a4130445810017440c0100500645000343d1a158042c0030300f032840c06040c3c0d0700058080c146100a02c456544250480c101f04a05201703000140080883c03581042c10641c0d0803001c03540c0c064080300644640d901c0c00d14280103140030310002140c0940741300e020700c240c070800008680d201c604c0c0080e803107012079000c0c000a05261303041100c0c007050b90065401c00214540810344200076006c5c85842e64003000300311380c03d00701040100b05081480c030400c41c49020074a0328142e54142415002c00d804009400b4038080000c00d569101005900d008403081007448100381c86284c0d81e10700d4142100043c600d11410309401c0812516850b46e20361003114009070303204424601c03586a40102c58028070112200950103c030801 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 850673318 1250 850672068 850672073
    0xf030a120203060f0d080c060f0117010506030d11070308160b0c0304051f111303030e0a140f0d17030f0c0f1207090b0f03060418020a030305090f0d050c031e120306030a 74
    0x480180328027409200354005514003044440d00600303100640d140d592402c01809828bc2e00484c403aa055185403501541a8003100482400c203030155000515004d80080c103d00c0c000d401340d0400b80102d00031041d10041d603032000131481941c030084030000c109802074543c1c464980720040741001005400a00007039031074800c0280005540c041043d0b00c1044101c61020010154004100359100e03500791005181e45240c9507944041e124011150751140303490b0700c64800b04da11141445064030b500807080441d240344180400c0025401610044103445080c000100355012200032990326000c2003800c03d00d04803043c00b9140031001c000c0e100e03100300907480c2800039132050490701503c1c00f00e10b06a03040d42e4a0409000700b00441344561650b405030b00b4180d001d080560b43d0022018200e9415040c038a43d240481c0001a042e520310005160340301d14130358008820302c1030000750010b0340300054040b00e910520f400307104091080350700c8482d80e03207501295001041034030300700145801800203011117441c0720541c2d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 850674568 1250 850673318 850673323
    0x19031515030905010b0f06070204020f0f070f0c1d010519030819080108070609180f06060503060306070e06180d081b0616141b0f030a120203060f0d080c 67
    0x2503a040c0065110304192042c001c00f8400e00342e030705808031006112a000500414524001d084c000303841560302107603c1038100ca214044a2074900c107041d1166075400140741581c4000b0446100ba03d00d0b130341c0d42d0004100d020040311403c01100400100f9100d581c600010010795030780d0001c07204401d40d0801400800203450300c0150400c09080c045502c02c0505c0d04500500d081b5050b44608601d50180d141082210707004a240380c1620b00da8100c84046501150360705018110000a4108083c50241d0002d039a076441000b542c002c2d082142a110b440d00da162003161030b07070103003255141e10400822406000101d006209204008080c100000026180e1500e00d040d8000300c078221100303e00320300c0f6545160000c2c003c0b280c1c047c3c0c050203001c04e00512104028665010324042d0101c1050028058290f0750f00300c5a4244617030f00001c12155000814401d0a489400204048021030410024403a40d0449402078038072a02016018200f0b01450408015001004001c1a20681003c202e690310002d801d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 850675818 1250 850674568 850674599
    0x106020721030225082413020307170109030311090a0605090103150e0105011b0809210307060e1c140a05070503030406020c12040e041b08070f05040b030102190315 72
    0x4404d841c05001e450840319505140b07040c004030050f0700301c1038080c14a20b08649141c0d500040030300b60480845407540301191a24401d50007402c0e100d184440c15440b11001508003091440c4a030b43c00b4804070101d40022400c2d805404d1704650301001d819400c2c402240f0480c05407811010514000c41c4c0e9081a00059220a1740d541203880880d40e58001480305507084001d02921240e054443d22010f44c0548414143d8003485003654480c074480d01c0a00040d41c556064603200c003000c0000d5940c1c403041803038240014403c0e61070900c020702518600b4803024001c04c003940c443c0031554a405001d001031655000081d400302e61250107005051019001144040020b5403145106490050b030387d1103070341c840c00c2c90110380c001c140e01d40c0007080009124421501e01096000359001d035034082480784590030b244c01d03004250840d141a20a003100003401c2c41d003581044080b200141c0e01000307801c103100c0034107090b44503540b9103004010400603900015482540b00400303601100303210488081e00d6080d440780303c0301d9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 850677068 1250 850675818 850675873
    0x106150c020910211502030f07021b060d0e1207050d0905040221130b09010b120304062c040f1a0306062d04050c0c0601060207210302 59
    0x4260121085051910b401d03500603c841c240e08000a1801d4404885040103008207a10426090816410811490390b81e000300d0340c042805644914001c20380c40045902240c2c036070b0040c8038000903d0850149005090903031100603098034508030124a494018041c0c40c0840c20b0640300b140e424611400c0048003401c42a88503074064210000c00d41d400a20003030031030f00458405c0e481004280340b0704680900c040c1c031001c1ca8485c202d91654951070a08559200f1081c0545441e085c0c0d42004902d0300e041d409110074400440e040c2005200804402d40d40b4010b502503900803c15110882c180b00f00c0706c0c00b1200301c81c01114003014006440d01c010905a56005042071680307a120341940d420045d00c80c811074581c440640091000340340880014000c924804030040d12848062907103032828800f01d0240b015028058800d000c68200031420004580c04100c55070480c0c001c800012502501c081090300c111130841600300c1c41e9034070401c021203c00b115000c04805510500d005004c2810f543e01d0000740c0c451 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 850678318 1250 850677068 850677077
    0xd050103150513110d2a0602120406021506061309020c010c0c08090d0c030f030f090b0a090e2a03011401090f05060904020c0607030b040c05040302130504020f031c1b0305070311010615 81
    0x30300d400e87c041d10303044440400a000c40e17020b000910950b0b50010700743c03907000c100c8114000305840c0c0301c0125070742d031041103414188859034010102d500071941e00108020b400040081220303044150003106c00c0c4502c0ca03001000f10b0010072424045103002007031413800ca4040c581c00c459103941d0341c0d01e00140002510045000c2039600044052170ae8110300c0f4440181100c1032840e01e072139202e030300003442450305000d140d0070184000c0215a40c05080500c0a945401d0782041c42541c3c081c0c9500c0413206d400034450380086c600580700d1650203500c110031203c1200c80c1690815441800c4c102040210307041a04481c0d00980d003400820700181c020000300d40542d005880c0040c0090300c240600056030708454480050020800c4104016250690792084801807911700140d1900c0d5403000407902004101841d605104084a9071075101c510504026040544d85440300d508103c540d030091846482c0c0c3e405000706901b8080000800e0242e14500042c43c01c0c0000007503603985607100c44443d041060003441c00507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 850679568 1250 850678318 850678403
    0xc0302010b0a12170f04030510050c09090c09040207080d1d0f0c0d06020c07031a010e01050a0306050702070e070f02060c031006050a050d050103150513110d 69
    0x5502881980790888003616419a15414a80420707159514104002c0070390308201c01c13130b41c402c2d4181d07810b48502c01031000b8802c1e0b035181d82e0f003011a620301924001030080b42c50032021a401c5240d0b10201c2c0c00c600c2d005440902d80d507903000551110b607044004940e030070a4080010070b001030703001c400600348c181c105c041c000784c2c40e10410300d15541d00c94502211a5140d002501748000d841c2c0004222140760001ca0b00344c07048015501c1d00300081e0240d41e44c120402d1244800c00b008103ca4200b107120b4100e0005050809682d0b02c0481c081c00030401c2c42002d1f0041d80f040410b001260403a00855401001070048805281ea208906200320300111a400c00060190000804256060201c542c0010300c00c40100e0460070306404500440d00244940ca06103c40003a140e64800c0c010400e9071200c00704c1034403c01031980e40f820242c0c0440180c1802e404503d15110001c1c9040e4540009490140d0f085811b80c0b1400c000360003440300e804181801907820702288025080c1c6a90100d001c804003540095401042 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 850680818 1250 850679568 850679573
    0xc0f120108100c1e090b030903090321030f07050702030a05070510020304080d200601180c11060a051008031c1d03030a020a05190309030e0105040e041202010b100c 72
    0x401c007108148442e424180b0249824095006400c003100d0410310600f039038584407402058a40308056400012400804010807a81c840007102900c01c43c0000e0301035940244c07690b160104400540d4048030b0f081081800403a11492050318040c0e4070080b942030107440c01c51250000382c80d2416455048985a20440d030601c032500f0f02d0142840244104e0005608043c2419800b54680d0810380d4014100810184580800920b120701c1024400f00c0700240d0300e2950b11191181f020700034044a001c0c0d60703820410241d2101e440384600300704803402c1c2000f90015888508042d005088060116141c400044102040c2810144000c0c00a2004c0700c42d601111280e041c4c0b500705441f07107200f02c0f80e014210015822100074001c000c40b507100c15404001695145285401d030350364000c40038441c000c03a01c1c12140e01d403425011b60002c0c00081c06500c0d00c065010718000111900d2140303000d01c61800000f8004100080e84014031820340c58500d0001190306a0284049420503043c010034070001081e98045206 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 850682068 1250 850680818 850680823
    0x20c070602070f0b03010b07060b0a06020d0e0a1401110f07120b0a0b0901030f08070b01030807064d030c040311031902120106080d03090606050a0f0303080c0f120108 73
    0x10070000399000c1030681303084801081d501051180f41851200041d0f00c2c1c013084400c2d401065075001c01402140e9481d21150000e40e51003803041c105001c1105d44c02000102c1c40c0100001c02220541c0d0a4408084e154000440306060134020020f03082c41203864038011354400f442164058403049103082d10024140c204205071900182c080d1032550320303003841c0d101e494640c4d4a241781507a03000084135903840182c0c900500e0500c903c44010300360944034000401040a45802000150f0141c002408903a440c07820700761b42410207402ca985e500540d140020941e002c44e00c07500240a40110100d420078a00000100281e03008403100f0300b00890000e424010401d07107c80e00381145005600604803a02e040c01c2000e0181304190001e07120703d0045042c481c11120035003002d030107405da24041da01c00c000e20303040160191840d4101154003909107040440c6d2400c1c10000b0004032f598081c5281a030500d50345042e0b4100c04040c1c81e100c00780100700281c4050051260033030003485020441d8101d1903261880060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 850683318 1250 850682068 850682083
    0x30e0a060e030d06140a0509070e0d06050114030c0319240b030f01140403202508010e0c010302130902030709140105031b09010908010911030d0203070b160c06020c070602 75
    0x24244001985d10f50468035003442c82000d80c0c5050300c80504603183c9241c1924104598a10b03960f020355040009002c0042c0c0350402e5040714804442c051050180f8402c01d912209002c59007a0580d1200d41400740307140c803203450380308028001c9580e20500d40e1250303604945d08403070405141405468406100c007509040062101e0940c4103070081003004c610f045e0482c80c01502610142c100100b8007a030b06001020054003205000d10b12084030052551310b600380b0542601a00c4c4107410040e50fa400040c050018002c4040749441140507210b55152000154000d4008240c080010400c0d0b140200302c40f07160f840214010149910b401e8040c40c0b92132064003164040a000b241040028010b000000703c0c04c05241000080e86030710151038084900040b0350380c0e02240d014104039801c0040355420300c40c1440098924190503025541ca04201080036a0b503441400401011048200002600c0b440b007141c07184140c082600d041351031034860707403902d40aa0b0041c0c40d81107680d41108208004070703a010003119 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 850684568 1250 850683318 850683329
    0x61401030b1023010509131401120c170106050a080c090a1a040926031006050708120912030903190f050d020d0603140a15050f040201030e0a060e030d06 67
    0x1150745900301030000c861264407210075031000d10381010703e07519a03004070181e410b482c030054a03048080c5036440806000c2e11040c503951904540b54000030440e4550920456045a0006d80c0e800d0041e280c40b840a041002090600100b0b568440700270900382d541600010062600400502e008070303150081180d0440003414201c20300f4504041e4488080d82c00300c0c075076440402103070009006540b9003072481000d680080c02c42e65031002c0010554200050750040c50250b006224070040307881e212641a81c440c410908003800c20942401b06003400d8400c00355441e0310540f80c0302a19048503884262904940066401e0000b903040451101c1948200035040641800240b0b00a104c00505400c098424454014a5401c003600000d0800003062a85c0011000351761000c21107041190344181c55440300807020085840b540440140010300d503060040e21701501070303902072450980311a801500141200c05a42505008004141000c00c2e01032258080c402c071401d0181d582c441d07a01d04003104951082d0040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 850685818 1250 850684568 850684591
    0x1104060b0a0e010512010b0306030f1c020705040204030209012d15080603063c1509130b190b090c0306040b0a03050d081312020a0b0105240a0c061401030b 68
    0x180c0c170000301c0081241d04458580035025600d0301c0e004c01103400d11004500c00c0c0407500c2240301250801070a100c04000340003056003611011521102040240e1041d4031019602802c5680103004484c00700186562183e94200f8808121400c100611400060703907000740301c00800c0b65028982c483d00201e2440d404a82240603010a28101c038080840d001c0c1001054100c1e048100081c1c4e0120560184800c12021404405035602d024084031132225002c000c558000e1985401007426401003a903140b128a61100710a00656a074540002d56400110710340d00045448040c82d8004e9110340d0a581d01030495500710948c1c900d8443c0901003034400414146000f8043c0707240800c0807940c0851010b0540e01c1c1d40c40c208103240c803001c6014070300c0c440c000406004400020300d0000000c0c0c0000704415998802e09000c000d0303a0f40c400400040940c0360756252101000d4400d0301d030700c080002004054104030343c00c00b1048503900381c542504440c203d02e01c601290b550b000044c002e0148425110754800b803003480 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 850687068 1250 850685818 850685827
    0x8030309060403120b0301110a140c0a06091119052409040209030c120a0309150c0f230c0405010905040c0608060a0506030f070e0102030a0e0d1104060b0a0e0105 71
    0x3034090303540100500160800040e10715102180306241c01020656000a009110002e0403c92504a941c85443e100000c961030f003400302294030600041d654241c25190181008024945500001d006100000c946a0348281e07201c1c44641d980c910800c2c201c00701c003101804030380d09010500149612043e81051800b4030b4026620851310104d040350140e102c15100540c07108901c00101303140c4030003d08070380c1e4400031f4103000588490000425044140c02a0b4414082c0d070f680303002030040c0c0c6c030b00301c500380000500da4207000b0003003802c41001c0c00110b44281002e040c0d41044141c852840c244103038800249030000401d49041c0c2ca4503004841c050300d0b07035030420403a600381592408890065880760005101c054030004080e6540c00a80500905000d03050710303640e01d000c0c001d40c1c03640201101d0420201d16440c0c10307403210307500c0001600d0094005c2c0d02c41c10981480c800410240c0d5030324003c111920b101424100d60103807514000d500080100d801c14544501c3c580a02510400d012181241080700500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 850688318 1250 850687068 850687081
    0x90c181e230c090f040207020a060c0b06040603020a1203090f0617010f0b04150c02060706020c1c020601090216050a0605012102242115041a04050c04121209080303 72
    0x40b0f40ca40b26040b14078940001074100890701a0042c2031000e9441070204000160840e007009070074501c50b01c40d08c00c1000e00d0303030340400b0081103030140d001c00f0f90030807107071308040c01a11403140000004c40c1c000e0801001c0039960b10b291240000c0b06401c0000003900e000103032418044000b030f040d805003c48080c42c00b52070f130a02c001600607014611036180300e070a4840c1140e07080c5010b14445044660080c00b01596180c840c00d064002c0d512658120034244100c0703032940800110001a01c07480c41036540030f000f460f440c00d80001c02035000000304482c600702448800c000900c04100030441e007449002d011440b90302d400c4801f110031510f07202e544070100c664030840d40140c0e61001c0305a801076041220722001d40c944c904100309070248030032403a41e2007501081481c40c1280820b01074440d807158081c00010b0500c001c140300c10341d494051091242c0c440110b81070658942a08219802803900305120b05069441510b00c41400f4400c1050354502a98040b009040e94441003c1e0050a8404000e61548c2481e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 850689568 1250 850688318 850688341
    0xc130e06060f0f0d0203010b0417031602041d0a06140112150f0b12011a030f03041401020a05100b03010f14040f02040b0d11030c04090c181e23 63
    0x5060300c0001c000000f0b000710850500c40680c0c803207101c3c1910440d140d40e1201c200600586c00750082030003105840801002c244000003ca41c04052521901010303005203900788405459042c1c02c001c41070040114028030481c080204101640c000e075004203441d83c2100620030b480344107070403041e8406450010b00c0041001c1182845000c103c01000040399500402401c0c01003c1c0150301c50350007071403032054921a4a05401c001c2c141c400e54201d410000b40c913074003010b0791101e50740070549075604180010408410451004004258180107803a480490f694a40c0c0c00d003001c50204060903555a0a01c0e07406007400d1040303142009a00c8401c001c20020303000c4403030840000030b100818417010303021028115180d0790405154003602400d1142c00c00401d02d0301c100b42000380c0302c2582c040d10401016243d14503090280b692140c0d04185400701c558105000e0b0301c070402030141c0900045407150031445003a40302c00341e062190460110001988010507038503050fa100c420401c02c40800b400ca00b4000300390201c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 850690818 1250 850689568 850689577
    0x6090f061c03021f0c120204060c0f17030f070215040812070c080a051c020301120f140316050c03071802090d0b0406090c150804060b0301020c01050c130e0606 70
    0x200030315490120150b1400300c0c41c0c0f0724050b0110784881c2c03502c980e202184031103030028a0201229203542c070511078118020400c80c051072040000080000302c0490201e2159240701d132030305018044003803011420f06000710703030f0ba4801d031101c000386480341d8200300900e54140b00c9126458030400e1004414186038640704401d02403009082c4a018002c1c000c5441c80d8003403803c2c0710b001d90340501c4460725000c6400000c0c066812400b180b040500030643e0224400e865482101c2c142c446400c2d4a9101c80c42075211038403500c0310708004541a06010205110340071041000c1c01400e00c20240098801e0001c0c030340503041c00f000822882c0240c2c00203805100d001c1c007944081c0080704211500603203404025000540501d45040b02070310508001c002c0c4400c0c00501c0e000f054271540124a00100b0030758801c0e01e044c64002c0c0a10580009203e240440d00080c0541c000e1044440014000350810346400c0c1010308486003503414082040c030005031080b5140116852078018070b000c1c0000170300752a00c4008100c25108 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 850692068 1250 850690818 850690849
    0xc0103180b01090203010609060e030a0b060a1e0938010c0f06050108060c07050307030503060114120712061a030a09121d0603041e140a0b06090f06 65
    0x4840e1601014a51540d01940d241a0800000d40e1196528000400258801e014000c000f0710070103808280c0c01c2c0142c40c095143e0001400030b20003207203503441d4014042e0001d07100c076500040c207100009544c0a0840c10f60b0404a58041c8120b080380b82ca074400c012a001400f0441c10074481c0039580b00300f0407081c00c5011800c140007076001314104005004882c207040c005e1300101000003001c2c85005000a40d44014107881841c0c08652050b154407540b940c440c060704100034403681c0300f0021031001a214101031504001c1c18102140c1d01c06d00901000096000341c80020403041005c1d04100115034400b1004080140c1c1c80790401c211030034101401030115000311261a0845e00101040f82010103501151409400c810040450203801000401100c1c81100d07014111089c10000302591424204aa0145511503010440e1251603074403c584071818840650b904080800a0044803200748500c64105100710600203240c80c240003000720841d806045082044501810841c1507101e413400440c8901 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 850693318 1250 850692068 850692071
    0x31109040504140a030804021014041a0f04090203040b1008070302091503010203070c0317070807030e01090c080a060609020309070506071119051305100506091c0b061309050c0103 79
    0xc1e51030402c07200403031000f40303c05000d00c00c1080c03203800e15502c182070034010340c800c039032040c401200d0b60803c5400d4804040c211651142c200400c206041108429600360310740046094209000d84403240400d8006611060901e50000200000c01c02082c00142e40a1401006408102e082103a01681c6032411300000b4024107685c00821066000c45090b1f100f4000d000f0003c0d9602d1808203c002c00c01c640c103c40813000301e03c0d100d402214900d6a00c244511680c0c140ea1051542d560f1413504030040c014500c44880c4079542c440c4000041244505c10001800d000f0b80200245026880e10601325040d81d84001800c600c1441480f00704c0074003064100c101c80040b6282a26401581007001c1d00785801c015055110841d203c10590a403040c4c1d44840444008488159100070b000500c1e00503241c1c12580703034650807503d0300d0034005458030802900800c2806403141c00c0d0000031510502501003868000c0c1d405482d50800c0100318500752180b034a104504aa007400381611540d64203690744261100e042c14107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 850694568 1250 850693318 850693321
    0x9120102090901081507170432010c12090c060507170d0f0b03010e071a070b090c15040f050f040e0303160206070e1804081303060b030d0311090405 65
    0x15000d406071085034038001e100401e5035a41c1d0203100e549417042d103161440068000e00084006003d982400c0010740b90401c5005075603229a1001c4150744200c0e44203110f055442c90800c00c1450b54003c440030100d80c00000916181d030400054950700e040c9e10501d4800d0b0614079503400048031200c2c5d2b1402c490690512940300c2140d0301e06078040fa000811802e10941010507862041403041e00000ea000420300004c01900340c50314107050036030715403c409034241c0c0d0000c0c0c02008200e0005d4a41340d04210311100540c2081c9250361000c8241038113445642d220340c4120303540211880c03d040030704800c819001e00c5614251405000703400c05401881210710840000303c811101d038481340c01c1200304801040c00c0c0d03642e91500d1802e600081c0c40904802006200f22000142c90500500350b003540d00f00018071040d21510003994107002c0d0140240f007250454010307c0943c0844008260140146100b001d02192824443c81411729141c610a849010542483c002c0114588650219982000252000b1815 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 850695818 1250 850694568 850694599
    0xa0b0f0d0902060a030504030e1806090613150f090c120c0909050f101a041e120506010611010b0a06050a021609020c0c06211e04030309060f1109 64
    0x107064002002c2c2d04010002507080b1000d41c1688080d1081e88640caa514207451a0000d103c00710340c284e060300003003030070318400710391545800c0101d42e6104c0001461443c500780c88410717a50a8400c00c52a007240060b90850910800e00c0000404020f0020481c0400c00c3d010484401040100c40d04030300c81139195201018400c41d4480c102e01c90241c0303001c0300180014101603088542c80d000848048004500342003021698000703121264002051903195241807a0804d205590001100071040807483c411b0301000032401c0344ca642c0d801840d40070310007402c155071400c04060f1105130310721101e803110b903d009445150380d80c50040702070680e8581d01e8035a45541100000307034038082102d140b6000c0300c08400000074020165070006c024a8880c0001e0b140080c8842080c84518041c030810b410700c0f01d9404405120000450002a81c4a204d9100c480c10711100c80ca403858034400c095070103a00080c1c45410a00a0103c140954a10100c000364100a0010a110010001e0084c0c0c891144a1042450035420 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 850697068 1250 850695818 850695821
    0x30412020a020306250c020906060a050c1e191a0a1e05010f061e0e030a1415090a240e030c0106050f0315061027090b0a0b0f0d 56
    0x48640e02a0441e401c500301071070400c1d22441c030356200f0b040032480b40031880c5c01c00f8071410003e0021070380908000c2d81e41d1903602c00c2201d10f402032525001007000c10701000400120400c40c020911811590311152200881e10a41c1090225000181c11041c2000760000040d11801c046080150405204c01342c0d48480c601c04018016450306d12140c4002644100343c401c003d58001c60403101c200c884150810f644d4a0251210821000011440010703035000402107030080080c0c080300b5200809941910015656680044070b080251010b80d50040044c00d00c810f00349e000e0503421080c072900500d21251a0b40e144007884140d032011082e91051081811a22003d40c0c00865884219405880e112003411250900131300c1a031013418403810240311030750341c1801c011170f100500840044841001c2d0f501c0800f40300e5101022802c000800c03410348801c0aa03008104042030724540d107106880740d0680f8121100040c0c8070725166440c40368507200c20070801081c0d2603040314403400c045002c0301e0311250913100000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 850698318 1250 850697068 850697083
    0x4140f06090406020c2b170105040c0207050303070b010e13050d0309050c330901080a090804031505090607080603030d2013090c091508150406140117090303041202 72
    0x40c04c5204000d10f803c418180442e90340e0030701b4824101c06800c070302140400c60f000501000110b000c040c4806c0107204c107007880c1e001020b500c07040b801160f01203035540780442d29503070260000343c44888202c00141321501c0304044413504000d4011403c1c00d000c259842c1d071a00d03400c10031040000d2660341e40d000b81c03c12200740002d0b00c2010004000948c401d8406a880c100c0c0c0160140125494000399407240141c40e0700b0094a045c808182c0d40d5006641d11040d40750001e100786c98086e03550036401d201c000300013039252401c10040c00c120980030500f410900302c55890243e01034684001e1210a20401249031400400d881c03682d06400340100c0c000d0b50000c51203051809000b4202280307280020002d503040f5044070322504861801104001c1140200411216601c0501402010640c45900c18588071706c1044c1158106462101ca003401440c1180050100c030303619802421041483c10005180350f070080c60701c14a08c20810231000385480c004c80800c0e16840000c00c01810782c80d124400f038074000d20811000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 850699568 1250 850698318 850698337
    0x1030b0a05091503010f090c0509100b0a0c030e01030e0c151303030e18010807050607050f1b13050f04080703020a08030a0204090525052506050604140f0609040602 72
    0x101d2040c1451540f01003884a008403050084d0708081031503550a9031841a0316038070b50001841044075040004020800c200900399640b2254546804151145588020b2889030701c584c4a00400d1141450007400e100d007601202070500d444d01145004900c008600b80041c40c0341122030007000c00c500501c140d45802010003200683c03500640101c10160064200401d0203405c40711941c2074800761200d524402d00034000c0d0b20003600102410460340c00e040002c0c122092250055134100ca1540802c04d2924941522100c0c103100290480e400900303242a42424030051b4060600c0b4a2030500d001d0001e00102800080220200052000c02d00d80300b0700c03041c20001d911464559603820318051500c065001070080d841c02902e01008514940360004032901d20441510350175041c1c41903810252015046000000c8441c440c84582006907080541149401807041800240c50704024060000301c80d1481c03140f924164422042c082c2c0480c035104802d9201104032142004c41c1c0d194034081000e805840d086 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 850700818 1250 850699568 850699579
    0x501030b0a0314030424021507031d060a0509010e0303060d050106120309030b0f06030c1009050621100303120e2805210d09050f0d090f05010906090501030b0a05 71
    0x324105854044005d004a80da03200389444550020540705031091488828000035034000001f441c01c01c1422141aa0701a11904000981502c04c4c1c064200d034101c0358812490b070303400c10001c002c201007880c420f16820503900c0000304559858411141da991002520703c40c4502c0c01025134004005003500410003604ea40e019800c0020401d1801815080860200b11a407603000310020780008480e1544610a500040092074040c44400522181000425400003000074030729010840c1d842d06130081034041e10741c2c079445a60a55191032419408009050828181182d007010000300754041d804a4048600c4d01c0005818803034074203a02e10b4056000d04031181241c412101e1200c10b181180202e01036801007059640829030201d0041d005c0240d000000760041040c4041d041030480e590020746960320a004403005000346101040c0f070084610000000035010307580074440000690300d40c000404080c207200e501c1c42d081c0440540101418001c1e00d041642d2104a441182e035040c0c5600c00404020b0f05 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 850702068 1250 850700818 850700843
    0xc0d05120c03070530090a030210020c0f032d030c0109031709010c08131a04060603020a0f0e0103060b0613090f0612050d080c07080d050f0618010501030b0a03 70
    0x4074a0300e0f40c01c100300503106402000801d1030090802401d9500000d2100d0161002512002000344140c201900785604901c0b031200100050322100f10200e0404e0094000780080704c148010012004c120013800380c0260000c20100b0905200c0300c05144041c0e000a140909000058030402e185000f04454294150300340007c060502d81c12009800c260341c113580000f03825030354000b100350070703148044a00340000d09a50001400b00300c060000d002d440e84a5800089a0030b510065810700040684041d92041c0d5545070400031481c045046000522101035064416031601000c4809803034148000741090340c071000c000003103607204004c0b18031120714a02c0d0000b6280c0c47d140c1250040104010202441e89440c00220301d4884007203446004a82c00070042821000e0440c0440708281c002e450418800b03810701005001400e02409441b443e80c40b9100000c49140c0031400380b0389010050300e070a02031324801005034a0b60180b1083c40781513a4003824045003a0720702601083e000c0103d07030f2015010868940c1d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 850703318 1250 850702068 850702087
    0x6042411151008011e0e030c100509060f01140108060d0f0f050717100c02160b0309070e040803060d0c050a060504080705011115040303090c08030d05090304080c0d0512 74
    0xa00c52801400070a01009039943c0301e26040b8221001120200b5a119400099081a6059801240e41c0c01d400e1403c0d00c0c200045040700500d02441102c19010390f0351034008010000e0410044a94455134500f080c0340b0360352405294143c4400301180440c10032465070000792181e29a007103140351840d0f200010703800104041c14180049400c4820072035190041c030707000258a010a6410b441e40c4912407001e0b200c1c0c0501440528000d040d030a4141013035024200601c84005c003030308010802041000e1005551380303003c01e03d650401c040c90b084111585400414440820250403d803503200c10b00340c464640c042d10f9030808547d0192998050350740242e583c04040342040d808406031080342c01000072503540c1c0c0d44032801980e001604ca489801d80e680f00300e8640c09894003034407141d07402134000e05000a6440321074503031070500c0b80b45c0c1d0411406640001598010107400344541680115200061410242040d10450302c80045c6104c05119107503841090040c09002d02510f56600344047c485955a110031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 850704568 1250 850703318 850703353
    0x1a0d03020607082d0415051e06032a0102010605030d0903031704021807091a0403030215010803090607020303190c03180602062d0403050d0b06042411 66
    0x466250740001d400d80301007441c440780d440c0e029854852400f0130465520501e41e8100c01c1200c001d109550740c0361125400c1c13a001c4410f108060060303240b00080c91044000304042c00b81c08402920050003507008010104483c10402e001c03140d01c5401061040d060102e860040b40500342540010360715020711a99220b02c15008030b22001140c1c400d031038128041d00c82808038410100c080700d0103500400f480300f8907a82102c141a070306030320100030704003d0741280d12010f000800c2103440700e02f2250a04009000d10078160104441c006140d9040c2044180d9810b294885e40c40340614403029000310340c040782d11021940c0510035207015070001c0281302c41c681f07038080000f4001d814041c0c007900407506d40198080301404200000007641d5182d00240101d8451216002d064080450074003d100c3d0302c2c010781e040c242800480746001318000c0d0b60350380d00d03907400e18642001c949108401d648a10b008200c1004000d112180c0444501c0c90017103000450600a10b0035600c110140d03020901a010381c030080c580b0f10343c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 850705818 1250 850704568 850704571
    0x1221020624040c0305100b0301150503091c180b0315040506151801030e12121305010e060609070201060311060d0209030609281e170d050a14040b04061a0d030206 71
    0x201d280d01b0b65000d5483c110613110744030a000701040940c01c10032010741603018600858000540c08202d0b0042c2903002215062000c980f5082c4001800056507146170220464045002e0075100100c82d2a600309481e001c0301c42002502100c1c056070b115000141280d64503800721503040340760419650b40d92203280d0100d1500410449150200340703880c001035034101d00020403c8144c805595203a1426121503d41480e01c0310081444010f40180241c80001550a02a050200000d0001460300e0700f0032108003c110500200320004580c9001c00c104041007060300b55407100c9600381c80c0c01ea40d9035811810203001e403040000c10ba815200d8041032104486002500d4440d400341c0040300b200e048480a20036511700c07680100074000d007400e028101c50002d01468035101e02c502c90602e4058400e4064481a079903004010703694040d40c0d1782c00030850081c203940a00c1501800e21901806030749010390311541d240c40080c0010380303810341e60f82d156100d41c6162070400c1100000148004948661464000c0d0f5440c0f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 850707068 1250 850705818 850705831
    0x302030c071d130b0c0d060b070b0a0c08070c06050c040302030a03021522150b0901090c0207080f0706080703020c07141306051e010909061221020624040c0305 70
    0x2c1a90000f400b0842044240c960700d5030010003803415071500c0300054065081100340e5148682d480b00005584654000146011072084100d540704d0f02d8801c0840f0304950070101c00c0020701c003200382080741555021401d0301c0740980c81200010546c4481010181c00d000fa074100942500c20412000241134002809040407450126200182d80e1110401c40020035055038101503048826800300c0054018681142240c03001c5a000072220150000240d008800f070f03009003402c6650b244c201000c0d41c1d0600030203010788a204028141d00031004c1405540300324038446c00c003c00c0001c1000c42d10881c800d13012070300d9101101044070402e40e00c55841801720900080030074480d008400c0c0c07085003030049001e190120764000f0305000c615521800c41c1141c810540748418100580403401203803a11491003040050a07000e17149015400c55843c0981600b890018003101c03100941d4055102503a000511507400902805480d401c01e10308151a070b642e2560003440da61003402c0ca91440201c1c0d5040e4403441c424035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 850708318 1250 850707068 850707119
    0x30f0103200d021309020915040b09090a020f01050f0f130518070e0409081c0b010512041e061802030d0504030302070308130b040605271c0302030c07 66
    0x60100303241c440550307030721009035411070002c00d40c003005031600d03624004503400310300404940007041c2e5001501e24841150042034003c482ca88201090030580f10358664140180c81000e024100044071580d21940e103140280308a03203824480c02685d21403070643d810f00c1c0540301e4a60303c0303481050750386826030032802d0041c1c841610500000349038680760100a064082c2815049005d441c1c0d030740204c8501d9900c0b00a02c0e0441c0e00c61000354002611100200181c403103c5d2304808181c0384800700c0b44183e5803c425494104001070015452501041a0741070b0803561014003811420318241403540340300414400a012286020700c1c0c80701c0d007a00c85900c00340b504d00c00c8080e1a140c04030b0707681c180c965028038040500146d02001007400011081401030289000942110900c4d941e40e07041200c40340d01c03a402420003c1c00c01716000090503400c10035444030307802141440214941c600003103030740303590450802c075422440c11001d04245802032088445e1620b80c0c40a9403602620358510b0302600c500d403128400410b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 850709568 1250 850708318 850708343
    0x4050303011a0a080a050603030c070303170a050906071b0c030506040c0b042108040f0f06140f09130605030105100e0f0106020d0f090f0e040b060406150f02010e03030f0103 76
    0x1600c241c0c2c1103d076070195640319240c1d2620f0f8696403c00406004040b80d80510007000790b0402442c042200303200840c800c0c0e8488112515809016900c20005040b18808600f88024448561030200d007240d40610395203001ca0605801c41d046c9104204850409448100403141c00300600c5408201c040c40742c1d00503a82019510356400c0030024910545c0b081da4a5a006070341d10000c10306240b15400c05141c00358050350304142e1a0041c0c008901c006906c0004081d04c000d0082108c59048800114011401c2d00d14600340160104039815910400b181c6a10030035503110440040c198540c020800703881c024000b00010310707000c8114151a440e9000d028503800e00e600008491200031441d840c103803080d40d40905280040082c007030343c09102d888100d03010300501d1030300406c062420001180003804190200c001c14105414030b0240d24601402c40c0d8003903401c101e01817100503844d40c0d042c01c1c50382580c980f40c040b200910008900405801d020f02503540000800d002c8480d0302d89140c241030340c2c0200c2e01c40b80030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 850710818 1250 850709568 850709609
    0x15010321020606010f030b12060a061a09090c1b1005010611300418020706110a1403090709020c0a02031603260c25080c011e090506030405030301 64
    0xc640040740d0b20f0b40000c02501c007540c08a4403c1d0800503a455011f0400e40121038141030321420100212440210180d43d00740800c00042d441e1203091003403040d800c140340f0b03082440c0082890300308024071402c958800000c04401c6110b9125048105d01c00324000c0c0d8201c0c0e8010442007010300300c04e2142000058245044c0c4440381c0000c2001c5983c00000d09034900301260003a00503010720b52003440c09480355000d010025425203d8200e200d190300d07812a005a07544424a440c0f41140c002202c0c48084141c10f010303802e4940d4001d403c900500d0002200d060300d990300e03d003da901e081543d800c000d840314004940224400d80015040c00c125200720156070a01181d454808080600303071101800303c00800c221002082912041080f0702e20801c400309180001d005c035040d15201000394a04405200f0740708003486200d001c45a1805048040c020703000d690400d8000901003208122111100004591910241d5016079400c1000303010180109860703203094184075403241c0091052400d100c0309500300841 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 850712068 1250 850710818 850710823
    0x30720042a030b13110c0d0206070f1103090925030204090b271905040f020109060306080d0e04061214010f02091c02030f1f0e01090c0303111501032102 67
    0x214070805800b00071000403420803000a0407500c1032900c05c4039802c00402d140a84207003e20f18480c0032940007000b01c0e00745200002d0408098000e00750810158010031031004101204840e085201102d2000c96525454003010a16212039035440d0444400c1000c080c280c0d401d50007500442d000d505041040b10700c203c0602c8100d0b50302200d011224150540510000700100c0390080d00b2011680030300d203181100f100320000301c0b034040d00e084d40e10120300c0d400c2e03400715070b8020b100c2009400d961400f8800503251840c1960740f070550402080074800e40082d180413039226980328000407c050b03020480150b0190608552402c10f49010407042d50a00d010140544014001c9510480001d40f0b02c18007146001041c4405004038103040f685409000e4100200010070440c1c3c0003904440010060307940c08102c0311004403040c032181c10300e20b40d040c00005004103216071a94412241c1600305080c0780c41e20b06076880d0603c0c228088070503014496038000310031700c1801c0031400224140f403010301c00d007040d071400d0903a03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 850713318 1250 850712068 850712081
    0xf1e0a0e0c030a020d0f03030917040e100521010219030501060909060b1812010e060603070501030504020f060f040f03110406080102030f1623031017030720042a03 72
    0x81d00040560700171000601d080e540d59410718003914000070320302c101d5940ca0111100d00096207060001c085010b0018182005d00310b5000030303240e514400b00d00e20b072002054685091000c04940c0812041c40c1514841c0c007901207034000505140035140d4001c00e44d0000e4014907007800b9a1002542a61001c14075071040e11a440aa031552039015003002c1d4a0008445144096000070390071115011244007c10802d00406840e03a1130127004d4107a500e049002c0c503141025980c0018105402c1c08248809616482a40442d0b840260741c100e90f24400e514810116200d00d900c0140794001c08100042804030115170500d410404480c1403007400c1e6a400524280d00065682c0c81244908c0c030b000ca850791407280712200070031109080181c0313540c0c0d40c503102d048158103021001c01309100c00404c102074841091361010180c50340c1da2075000000b015051590b0ba0740590b040013002c40488200307100d01c0c14100b4107440049200104144154200d58034840148002d061500d4544c002844504031880d02030300034036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 850714568 1250 850713318 850713323
    0x614010317072012160e1e0a09081303030c0b0c0301060e0120100605310e1e0109050d0302032806090608060411030d05030f1e0a0e0c030a 61
    0x1900d10310f62a00804280080c000c12950f2020985401c101981014001c50f2400c245400403014824681071304980c41c00c0c8001d24102c4c022100d143d00c0700170340713110302e00ca1786d04013540d02d0000481101501d80020184698040c40070b0040314580c00200f010391000100540314454042c103405034480f0000c1c840c1c41c1c0028024039020400000a140c0349511a00e000c2d014011044801e5001444020007103043c0710300703007119541780380d2a21070130f101e14100341c06200e542c140a084001c0c80181c944880e1030f8010032500c1e8640800d500d44428440041e020030800c0d013900c40404500c4100d0440e04a054000c0c0070b0340904864034010264240301c1d12f4002e10079244590b42504681900308043c0300c2c81d4224200c8002010a4a0394945c0302003030240701e521074400a0035110004298074101401c01d0b248600056072403e1081d8011034000d44420303404001da85d0014402c7e42031503500e4030b59480d0704401b015010b50000b6918100c100300402c124640c3c001d407038890940004e03140c045502205064070740e4036102c0d02 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 850715818 1250 850714568 850714583
    0x10e0601060c020603070c1403070212070b0901051c05180c121c11010903020309090a0216060504111306050a1409010e07021c0903020127060318061401031707 70
    0x40b6005814081c008503800a00f903d0441c62040c881d82c0d851105928110400480381c0c80422404110708020441c20104680107004000062038403508074600d11400480764100030000c12245c13694201e00d00465069080030500384050b01c5e012014603803607050b09904546a02c5100100c800a09000800c144251343c10320161034100002d24138071002454069014013000b48100031011001c0081c4a0240e00038802da01865881204200300840d10001801c5108070a10401003078a41615941d400d85100743c1c84400440d2076903590825407111080000c103680c10111038424861044540d60054040d9002103030b0080500e520b540c45100408c00c0101607617003100303002c001801003504030907400342d002141d8411283d07001c15078030813800858011401d41d070104004403028402c641c1c10060b008555216101c0101000c2d20049001c0b40c200018030503001030641e1200980ca0702460040e8190b9200c0d08441c00f0700601e455540e044103079500903c400c3c1c400142103032411400340ca0010071a030303034240c0000300d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 850717068 1250 850715818 850715837
    0x5012903060c03091911180112030e0409020405070c0c0f260a08041503060909052e02120a06090e070e060a0e010303021b060405010f18080f0a05010e060106 69
    0x1448909603c0a0010b0440340308410342d01051000c40c14030707452014170031300083c4510354112090088201c0b8400420030403105800041c042090030021041c00e03990035180c91014234048a012034010523004c07101a41290405041061b03190700b12402c0c8002c41c0c03146065a40d01c503a5005e10b820201e24034050308205008926070508810740012460000c058014140d8002404c43e585004040e4020b500c040d1b003000c5524606000e90346c05115420041184507000e0000860f0340e540c10b5103030b40f0030707800404201130f54030304102d010304400403198100740910404555500b141c803400d202d0810202e410b40501307418844c004c590245180585c2c056040413200030803400342004109241854010103840d004000311400084000030794094a00031b5000307402800c488002c1810311a007099803820700900520082208204603644a61300d01a64041d07480c2806512440810151504a560780032550520420004500d65100071461510581c4140000c0244801600c480d41d140d0f8001d104100c0402e40111 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 850718318 1250 850717068 850717081
    0x151d010504031b0e04150c020a1101050d0e03030a0e1209010e1005120408070203010b0a05150c0102040b07080c061b040306050402030c1009150302040b0901140d06030501290306 78
    0x5980b600d03d29588980e10040d5142c0d010482e8001040350151594501003281d43c0030140288a28085d4030110320140503d5400d68940181c25402c000409041010029945580c11403690241401c0c4400c4004d60b9502c1c1440c117101c402810516940c0e0b103141c007401b90b04588010361402145c0c1c40300810303114815042007050800464070302c1c02e0310070028040108400c0c4845041c075245181710b907100c2e582964894420340141421a80d00003445801110000700174402ca41c1c94180074207650075a4105130b5940e440d40c61b10350b0b019008551002a006030003154480c108884a4040c21000180c4000c540540c0d40b00c56a00c4045140581205031000c0c0802c002d001081954000e16480740c0050304807202425500d01280c0000024400400001c08401c0140009000147d023071100745402d290550600b41440c07a11a020312407501c40c1c1e4140940e020003600e03c62201010303140100742800d020042075a6038107000380a006602050300150314950600120450b101002400411010b002807150f0b5807140c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 850719424 1106 850718318 850718333
    0x80d0c15051e01090504051e0111040308120f150f01030603140115090209010e0d02151809071e0c080d06120501050a0b030607050a18151d01050403 65
    0x85c052002184000420458900e034001e21002d0100c00400468010404000f0601080c80046800400d02080201070101c08154215100065898404401141d0003c5465180c04440060721802c00d0600f2007505038680010305000a84c5500c0e9241d4841032044d21010210382ea4482d201e29080e40c41c000824002005d10303840170341c1841400e40c00601a0015802e03600d01401004400300155900d0382140400e00403032040302a5075440d0340c8501c404107601074214500a42e91800410300e1603200b21520541c480501101d150200b4015108551014024034140da81207802c1c030480030405d00920500000745190300042507039003c01d241c902d003560002426010720500d40003150709c2c1c0ba100030804070f0740064246001a6100345404043c1c1d8010300340d60890b02601100440400c03074404900311118501d449855109451503100300c10a0340c154240071440c00184207001c1000050600f = true := by decide +kernel

theorem cover : BRFrame.Cov 850539568 850719424 := by
  have h0 := BRFrame.cov_init 850539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 850539568 ≤ n) (h2 : n < 850719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
