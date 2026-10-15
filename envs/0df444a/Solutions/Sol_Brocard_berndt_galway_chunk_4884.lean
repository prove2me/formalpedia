-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4884
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:03:04.30544+00:00
-- url     : https://prove2.me/submissions/ab113ffd-a437-4658-874c-ecf4f4e0e986

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 878237410 ≤ n < 878417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 878238660 1250 878237410 878237417
    0x40906020d24090b0d0629060c071e030b04050307060b100507060f18140d02010e19020307031208040203010516050a030b12070305030d0f020316120605040908071101 73
    0x204101041074114400b280c03c00c50b00000e4100c0460701081801425840c0541075030301d00910302c1d03000121100d0003d60545d0015210391022041410092503014815810388264048075083c4282c208401166425200d603850040350942daa035600004c0c07030001c66044800d90004140ca2041203202c0c002d00351001c0e000c0310390100c07001e117155005041340650600a8412515080e9030704890a07594440030300310410001400c2d1800560404010001110510380f1251260011501050b071040c403500b0340e24420100034043e240d0038031091181e01000000147d03814040d40b44000009001c2d104030b4803001003079480700300040c0303840d004041c2110701c000c4c03000f01110000c501c100b041c19402070440350003142504000030414032400110b10f4207103180c003102080b442080c0020080c40000000307007540300e501500a00503000d01c10728400507408152501c07218500c401c2e403009c2c0c800340644410f20040400c2d138000540d06990300001400d440d010403043d00d9101000a0f11814803090407406240400d080c02d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 878239910 1250 878238660 878238701
    0x1e01020708030705070303020d0f090212060636070207080f0a0803070c0515010b07150b100503090f030406030c0206060906240f03040605091606080106030218040906020d 75
    0x48501c0e00e940300040c031500801c000054590f0815009a0548580001920302006079001007030691000300b001901c144c1c0704814507142c102c0c1c40000016918801c1e04040e0001e00042e0304011200304a040c2048078800608440059640b0f0700003800016109071981d500402c0b07034a103000c00040c1003000d41030410345a50407a10306070300404c0500003220b801459a1400d045160980c3c240103080c0060315581500480b5600000038258042c03201400d100ca02039451801102800c440c0c0320201c2d01c3d501040d580001c404000700c11064081e1014560000c4d12405840031140705486c0d203070641c0d010b900080042039440740960150b5604208241c0d00034030a031041d28085c1007a070b00003907016030443c103064003418605103001c140c2600c0ad810b50311a6080001c00c15200e00b010718003980030b44421031311083c04d48a0941001c0c0da04150003034880407a40c068444000603401c1c404101c01a40c03001001d070b08449400c9820300d0494555104540400c1d000d03250058450740f609501c0302c240e400c042d00c80c80a513845003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 878241160 1250 878239910 878239913
    0x106080906071d040b091f050303070c09051906081006060305190e010e01020301170c01090612090f0b090d0f020a020109090c140409020706062c100b0c1e010207 71
    0xc51550703440f0150000c6000c000842e440014094001c5090440d0060764034803c0c0000352101c08189241d80340c08540541d429038507a003c2c540d0320300070ba5401810b003000c128400c11812704503134007882c2c20048019002c80a901044021070968400d58030450855100c070002801c420744501c103c7d0007800452405118074145100c0028030700034141d0940302066924060b5070242c1340254031030304403088440c0095441c1c2d0781d41c40d4209801c4060000385203a40c05151003605944d849580703040280e610b0f54850100c0241407000c248010006040100c4440940d0301100c07001c94080302d505d41c4104140300007406070441e00300006102031032403481d040941d40040c994070010703078201108101392110075400240600340c60038202d5826108a0b20703446440707400200030030420281d07001001502d003c1c07034080c496266605116036140240608a20800f00000c01c0701350702c12081010250440003601d80c0442054036041c0107605a8081040031540d64013000c0e1000713240007000c001c400c100901e80001c5082c00c03940d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 878242410 1250 878241160 878241167
    0x30a0f1802150c15040c0602010227030a14010209030c010815190b040f03060608030a0804110102071e0314070e16230309150408092106040605010608090607 69
    0x600002445000c48004a9807416020710641d10515a40030480b240c0300310310011454101c2c020b170303004d03a50161402800304485005001b101e9060301c1e1040c40d0444030091f2445900141c001200701c130f0707041c00741d50000404a034018665801701c00c004400160f64a1300030040610740080e0601840c10f0220500c04c04c407061091007820400414251100405162000d05066103500c00b03410110f403800020074007140c44078200a941050f40e100b0101084000c2d2503c419036601e004100304040040c00c0400003c0c002400c00440c641c1540041c01100e90058a5000030300320040c030003080642c1216008010024408940185c2c010049690003034580b05090418840880c0030080c130003c1c86156182c42000010300c502480400c58690740041000c903620900004a90b40c4156242c1d099441800c0070803045034440c002441c000ca41c010000f40c42c241a100c140701840b11120709004406114050581104034180702c2e50b4416841010700007069814214040e09101001e00054401d500000c10001c96076003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 878243660 1250 878242410 878242451
    0x901050634050a021206090606010e010e0301110d11032401020a0b040b16050a0906121121010b07050a020103110d0e060a27082a03030a0f 61
    0x148545941d090440c00400004001c05880781c2000c029a45a00c001441070219045070aa072007280e450009481c2500001c1c1e84000c152442242600000d01246444d13000347d40c480480401810960b6000f880c0c400000d003102c0b442c9940b80024080000ca1043c0600544204d0304400c54200c189425810440300c401149213502044030040003020110b8105c980c000c1180c0d8003a80c0d0311030f181300001d140074503284080e00d1060754409602d00e151401016154040d000781d511031140344d0f80b803070700303152074160101c541a0050280441156840018104086005005114500d004002900003103245c1610003d4100142d001380d6040b20103110060003d040410140b008540918012030000076400b40c0491030f101e03034000c02902034030780b1b41517954081f0081070082c810300f50090200421400c03011241c00c0c0744048521101d25596a00e05000002ca20101800308402000010b41158000303074550400b1903500124042c559102008001d20034220b03026240300d0b4042107009020901146924200602 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 878244910 1250 878243660 878243677
    0xf020a090b07050a020d1109100302060702240d0207020306070203093105040609051b060406030e0a0f0b01140a0513050a0b09160e0301330510090603050609010506 72
    0x40000803142c0500904002041004d074000b040e150380001d8070301e0318100c14a000034607980944d5480f07000483c000c1d480708801d812290040c1c100c514204080c2d00300028001c0c1d8040420321400b4110074048a21071a40c0505250f100c100d10059896040740101403070503030010a920215401003140c1e4244e921119081404510020b602c0d0106601c800d00096081c46210700c040341e841c0c9020300300024008590070500c1c1e100d015a042d100c2c0d40a490702200300d82c03100040c145411540410007007250f68031983c0001a402004015503950140560700c2107001c40d00b03254107035030303c03003001c001804490310b89440800c08200403a8501500762030304000c6095030040c005034a01c001d035030b031000421040e1b56070450902103070010014412890310340710603121407400711000d1001450313240542e1198101407182d442441221642d9060360f440361680e07102c948001d01c0700703402e000c03030440300005068031100a071046101c0c2549850000380d060030001001c44600900c05480380d4840c40040080d0707180c03642169480c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 878246160 1250 878244910 878244929
    0xe040b0a17033c0d09050d0806090f0f06100c020d0b18010612030c020d0c09062d120c0902070606181503060510081b011107031101080402151206040f020a09 69
    0x184030304d01034500140000c1402034618000e0030007083e1046c0e84110054440c01c0f007103e03440d5031500c03200d030410900da80444202c41d9024440c4003044203442d044005e07019200107440c101c0301e85600d40d40451003014640d001242c814200200b80030480c460707405100d28440d41c800080001d02c0c500380c5404121001c009010b02441a000d03610410b5407100380b00c014a0607041500007401c00d545294000c018010351181c41841980b240946c3c1d90b198142f601034681a100c6a16050414201048040d90300313028001120404031380b10001900012a0000d4170545015060000d02145001101d100c0f03060b121400405c030a140c0605822000131288044c4103494210300c0001c0c0395580c00310b800b030502600707412080e490320502c1e0782c19024005c1031000e0395460701f00780e0b111010540850740a65460f04c4600005145110345030142c910313035200c0c080181d4441d00040641a024050101c0a612580300944420456880004100071810140610060803050490031031071310340d00c1c3c174005005180c1b9014480701d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 878247410 1250 878246160 878246167
    0xb100f2106050405180d0504030809100309050607080f0708040f0303050a0e030c0703050c09010f06050906070b041b051005121306290405070e040b0a17033c 69
    0x1800e240d61084024200190080109040103003000d00410460f82001d08503101340011120b21714404c605450444e6030000043c0d00f00b00c4003108000c50040c031408100d0400d40e4608105d00421800c100340c6006048540741c54215040c400b044426210005210b4010702400505120000d003840081e0342c421f41c1c140c50001642d894600c00000a02000b0304199064400801d81c1540c01c0b07404030354401124400c0040341c400104070002c0c401103074403d2003881010720300d00030100700c0d2a00400c010180003d00504080c64403070143c0e0740c03288401e001c0e142500c000480d5104c4e01003800b075002540c00a070004440c0b40000d0308202c0802450340c45140c14250300c01401c040400c104070b19112641c058240e0010040c45408282001d45d210b19664000c651111a0161000b0142e0300706032043c103020740310b19a00d0305071041011040c4009400f10b0340403903412504e13100380010f8803208407083c500c001c00300601441d503803d00300344164251000105050441814018041d04010070296004104001c80c07100d01d46 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 878248660 1250 878247410 878247467
    0x30b0103060e0702011e0b0f060304080d02031603180209070c0f0210050913020a050f0a0c1a01152a14032a0f0a0305090f0d060b100f 59
    0x107844242d00645003907501e1400d100e0700c10307019040043d28440006220207400c046041c0f02c0c09035100301c0010703908440345200b1805141060001554014041c0135514503014590703807500100d0340103c580020044481c44240b0103550700d8003902c0c80d1040d0030060101d1040f01900000c05803200a003240c810300803100840700c00c100207030030045000340d0010001c42d040408070101a11507031002070301500c2010b4007543ca14012203d031080d9882011255142418103000f0189102258817030b9243e0002d100b065050f60000503a5000718180c04080212074540e40c0d4501640c0d41000d03403a007281e040c188500c002181981109000104110744100002e60040c21010300308081c2c04ea12600300001da6000014168804004c0c1580740412021105050b1000d90759001c801d540725000c401c505007268116280c1c801c040792182d4080d1001010041c1031408083e0100c0000300740c042642e104540d80d030303115030b003034040b610b02106c01c24900074180c201002c0107060a000100f4012a1044d07003662503004180300c05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 878249910 1250 878248660 878248667
    0x30e21030714030a02030f010f030302101802030a11040528240e0403020d051207031d07090902040f0e07090504110a0b091504060207061103071e12090302060307030b01 74
    0x4541204502d4060341d030381415900f44001c2c4d4030445c1c0701a03001420302c00000380c5a1b039121019003100c0d0598003801c0100c03101c800410150040c001480348540340ca20346940540d4090008140403403007032549641000c01d00040c003056900c010b258002440c928032004902c11032140145400c0c0c580302c00d000501401c40c1030541162450800c001001038001c000200d80701c819206042d0145010f6000c4800903104c0200407a01c41c030411402ea04e40c026011f0209604a0180d0404030a1140700c044001000703480001c0e039480c0414a61040102c540c0f02d014510a50034184a5012850011074090054881601c06d455440c0d4191051406c2c007a43c0d00001414880000d000c2d034a00e40c00200b000c4500342d40c40000a81c04d0b00440b0010b44240310707030b2076202240040d2204a03001c90b0850303009001c40320b251601c02d940c8481204500d5480340410420400040c12003000e9041408000040030055440c1c1d080c6540c2285010800318140101c201c02400980c2e41c81007620303400306c40e528000c15039410f80d40048 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 878251160 1250 878249910 878249927
    0x3020f120412030b06093f0106060e0a061704030c060203040605060f010801081902120d0f0f030203091b060c060411180c041a130603020a030e210307 66
    0x103903805019080c001040540010000c0305080c81c1e8041c0508034090040000350312070a50155070003040c509603000600400b00001901d220000742204144542034810500700000f00408103003130b5034882c7c06109254200744021b801e081d0036035000c1c003aa4201360b4050302010785602d0318411548a080000d040600c01c070381740b8a069502150135500c03810300341380020141130103881d960302c034140c03c0ca04070b0b42035489944403034101c41c80440140300d5000002450001400800c00503600320000342d150711080042080b1010030f1700c008e6500e610350421a4880100700c100c000f41002c04042c01041407041e92080090341c1e03880c607404901c1108520300390000095003841004188095030049008000911032280080000c4203002d50340040800050142c0c0000c160b0300f111b45400e1104c05100521034413003030161111a0081d0080c4961820756544200320400c44550f21400c00681c00140d06521079501d40508001c40b06424014560880c0a030f6612808483c003000e11005490044001000b091084012 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 878252410 1250 878251160 878251177
    0x3150a12060606081f090e19050c0f0603010b030a020a090e090601210503030103140f151e2a04050a030807060b09040b070f030b060c0a060f0513020103020f 69
    0x944085003441c50500090000351080030040344005001500603107605490f130307652081880d402c1040900302113020000b8002e01031101320521a05e411261b0055851041c001d40302e00610007049800f96000030854081440e061883c018042440100407400188050700d03000401801c0143c0c580d90040801c4030002540d60040300c030f20f100107090101003000440c410b410785410b800001c4801d00d40b201404602c8500b150b005104c0c0d4410001000400c28541050085c540e802095460408644c1d109626042429400b1001c0841210501083c00072206d1159003c021180c0418841c0ca002800d40040d905114450944120100800c003040c810700d03000c550281c50b0060054142c0303622800c040c450754005a02c112411440d0064a54052400b04645d5201c0d55001800e0035a40c2e48840c0c0c00c660944a00c2c02e044103044d100c140700141e60307544c24094036440510300001d020326401410040180c41517403d40c00c1c02245400180440c4000348105070041a8080c280035079180403590541e080b42c41032011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 878253660 1250 878252410 878252429
    0x7151a04020f0309060a021e1b0a0c17060f0402100c050303070504031505100b0c01020405040212072309040c020c0d050c01081f140d02120124050603150a 68
    0x10900860440b00e0060342c003502040f801c50341a5510749070303440101d1152041000d0740811060f007440400a100c801080448241c402c21000008507d843c9413401c002c0703848c11120444444010b1100c0d032881e4184900c220b600f05c00030803460038410804803000e540500064080c0d1404034900c00001d006203242d03180c259110f81140c1e5a072401e940020015003242c00304543d50018400d1000b059640e501070305004000034445108400d1503c00ca603c255488400fa000c1195000d00000999949906c06044070080c01401a00700303280c140d03001000c0c0e44d03a1406120ba0716000e807900c04900d01c01380341030301d400042c03c0d20009240010404240d1400c000c09104a41c040300b210001e03401c000010680c801c208100b070700c880e94142c64402c00280001c9614556450895141a0401c40440900c00382481403c0280202030500c15039004a100c14010208044190b9114181c00310780c44003c0401250150b0301d903074151012420540003403183e00c0043d08420100040c9078501c01d0303a43d9030b08141c4009100052 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 878254910 1250 878253660 878253667
    0x3020a17030c161401020f2806020301120309080102120601110c03010509030c12030f070c0c09090c03020a0506090616020a24030c030c0c032a0b040c05040207151a0402 74
    0xca103d0307070b10200d0095025194200040d00d0955000081044074180c079400038100000c1080f1000c14011042020f81d900c00b0024056600070504070700c0118040c1142c2420020065403d040c040c0ca4200c480c0d00001650f03104224264040030303000c20300b640001092802d11b1046412900792407820101c0580c05605520f0101403148805c000001130010002070b00035503044900018041000340070031103041200888010001d503000e446454040011441210300001d0030303131900c070341e0407c40304215401c0b10780401340c1e18240b0039860701c0705c911401040d0840c1c515181c0342d0802d0125a50380500501c01300149001c903154421560b491405401621485c004d00b003080040008454541d040c451003400803915000e2084140b611a000380c40c9856841d4507043c00308002d56408503165124103e00c00b410300c1c81100c585080c1240201d0003040540114414589405c4c5400c0001300d032961640018405c034410402c540028611003020a07055034084000a03998282e2a14000210303c801c40640d885803002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 878256160 1250 878254910 878254933
    0x15030816151e0b030c010f080a0204030c0806041506081005040204020417030315010c03051c060e070906140307140726190c15020f0702100804051603020a17030c 71
    0x101c0d000c20882c040a609024100043c4141038890305a0b40302d041c0012840400061002c1c010012a030700b00041e1a40189003660704e4940d0354075000503400007003803a00b1020902c018060004c1c98400c42800030b902c204250361500094035034070a44c944c0d054811680707441c001800d55540c2c0d81550f00401030b1505800007421a420700a440350b008440400180500040d10a1554865076445c0d83c05a89900d409181100d40d140018150150b441c54241098440c030340032070303262004290f1034011030440e181d5080c09414004040c102c206842400c0244200610030000b000741e02040c040040002400301c00d0340c816040c200b07407202e0440c0001d00c208400c05149103249010001c0d00400c80311000d00b641d400e09101d24441140c00b00075901000e80321031140502140004190760040c0001c2104d0540585002410781c049070181000c402900c0c0881ca40303004110910005000030b00698594000000c440360a55001584010460281d00400d0100711010381c040c0d20b081003200c2401c520034040300e60038000c4c0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 878257410 1250 878256160 878256191
    0x1109090702070302011b110103020f190806120c0f28031a010b0712320c01052805070c08070b071e020c04110405100f031503081615 58
    0x2c0c0c40100d002a80380c1d1441e1144040d221104200190312856182030746152030300446c080d401c800d40f0324050103c200400407412030350301c1d401041d0081c103448070300c107901e01101000405100d40c5114603040c0c021246600d0144d8a40c21a1003001d00d08840000a11840c500f510216260100c820341c1c001410b46004000e101d0101000045000f030600c858072b01b41c1c0c0758030313202d001400380740001804100710303565501d0290300510b02c0d51b0940000840394070740125008483c60680c2d1342d0f0a0000303011900060803c4001c8400e0280f1a440042c14104260b4002c00382105005a1800c49481c200c0d207940c1c0b40420700b00c5209072921511290802d4456446403c5410145d20814080e40c042c0d010070007840c00185c04c0d0010b1640c20704a80810b80242494079000c0d0184806808415010b400c420410072002c0b070345503100750300011041c50a543d801c2110541a1011303044440400c00e08449550082040001070b5000040310f042c500c00c00d0703e0040c00d10091410301c03c64080c080130f40403294100b401c650318050740d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 878258660 1250 878257410 878257423
    0x90c0f08100605131a0301240f030302060c03040516140405070207140f03070323011104051f020c101106130807120c060903031406041e1109090702 65
    0x4444099450740c51180429400b15156071007415044040135409400c1003010307500c100034154003083c50120488550001a085504980c26007401c00700300c82c1d80c181c5224502d807001001d40084c1c2e41c1500628110749002c1d546020007050624448800400501044011301104141484181c0303140300082c6c4070310903050030b01c0400704503a014514100004070312520024466048540c1c000208802925007801e01158000f003074890342d01403044c1a0008001078601040340c070344188400d0f815a08990140c2d09a080d076018220081c2c0e05c0809100c20b1001d40d44a00409002032201c9014034050800d09401703a09286102e1411350380102c0c4d0b0103059407032036005050480080c01100c20b440280e6920a00707a8801d40480720084c122000904c17280c000074403103c4840c0894181814880c0703000506982d0b16041d11003d490890003e41c40d51144d00c10100e07a10366681c0c01010488003446164010b1001140c11800c0c54021001c841e2610514100d01102000305c503003680028180c60000c0c0780c890000b2759911b2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 878259910 1250 878258660 878258669
    0x1b0804172203030807030522020d080d0e06090f1c02011e4d0409050103060f0c030c021c0c020a0905180d020604020f01030b040906320f0a090c0f 64
    0x50150f80005d8990303220744640c41c0700f1040a8043d80e0648107512100345d4074611070700704980044d100301000020810700c001600d504481203101042041c5480486d03401d04001800d80f00d41580034a41d0b8040d030b20b10104100c00d10801c81d01d51002c10548015089000d40b4140b030400c110714096659103181124150829160201a802c1107a0032164024040803502d0300e94200340482d4100306400940e4405050901983d00d804441c1d590500341c0302c840c0702e0226070007a40201d601c6030707a4005042c00b103c2e61b0701400041c00494182001950f010160203900e03059861340743c014400084031010300f41030050404510854015040c030007955141c0740d01000070a4242e07401150641c0041a11450a50020340e1a8184500d68094401900d50741d0030302c540700c100030325198107054803191050340c039444a1080d816002c0c05010b01040b10b417a00000c07011810360103003101c0b4510fa910144c40b4404d0a0703480c509504070711103000200903580d030000107030001c1c500641d0042200d215004005900720708503040d40c0955 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 878261160 1250 878259910 878259917
    0xb04080904091109010614030a09031701080706020d05070b06091815041703070c0b0606041203080708010b2b0209030f0a2a12031812061b080417220303 67
    0x5d03600c0e00c1055628848111405014000810024041544035000200e0325486401c200500c5034900d10b080b00010400d801856241d40200300c1040610b9040015140d14191403c2492a048240d200c1c00b4400c2e0000b041e0500600010002c1101e421070048074000000c402815104400985110a24403d0065038192042c0142c10103440c140851902201e00404c0b4644801c0300141c0965100a20740c28001d0000b81d101c0f00074000021000031510f0740d841c44c54801d568030302c0146000c8401030700e069010f1b0000d4202200c24000520007010180000c0c1081030040c0520a12101c0007a104000c0d100c1c141800e5010b00500207405100480003c0404950b4451420703201030407a00c00601040c001c10300010740c0202c400d0107080090180826030055a5402460042c66101c02d0610a04280c5280e9000800c00c90501d4a03c00c280403141c4038254501e60542c0b042c000384c1010711401000801c02400141c54071010000030300404031504212454820741e5a5548201d01c582004041100301610003a0040b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 878262410 1250 878261160 878261179
    0xf090f0a150e03011a1f260403030e0105010b220b0705060f01062105130c0311010908010b03030307141c090b0c070b16020f061005030c19030b040809040911 69
    0x1100400e03445c4440c020003906040140c140702d21100d00080c0108400e41c1400090010010b041c00c041100540011080b24018030a04041c54005c04555141c0301d84003499140000502400203030604444401601000c0c0c0b800000c3d00103d50100145142d002c0200d00c0400220300c01007010109a10340b01e40d140307440c0c08501d40e0381d4a6060307c1b0362000350624264001d00101201d40410194001c940084d003c9031140c0201845070f9480069130003a4106880795120044804020740e8040261360103403a02c00000d1001500680c04030383d41e400094516814407408060280000040105540c6100004200704c03581014040680c8014001c415007550354203026000203030507055503422151815444205440a550b55182034060902207030711040c00c6000c1c0064243d4005400c0005178050002040000c503814541030030036151140f1028150300880081d01140003880310f00481c102140c0e0401c80c0303400c2d950351342e2500d20f80c540308020200350310929150740b0106100078a80001100b01098511038507 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 878263660 1250 878262410 878262431
    0x9062309130204110409050403020703021005120f06030a08070f02030d0302040b19030221090610230f0d15110f0d1503060c050d0c03020f090f0a150e0301 68
    0x840540484801c41094020040d2600508155024100d0300c2007140c01142000e0321154400207544c0199030a0b00181e01c40390060040d0302e0b004c120441d0a25585c200940751120124001d20400001030070103001034122070014071340d503d0522043d46000e502c0318800c2c3da1104503207014074030f20f1000d140c181d00a11800020b40c40c107502a200f107030305946010071500d081940c1d04610056080003c1610010142c00f881444c02660424800159541c60311050504902c0c250f01d501d854082c0080c14074419000d0340c5000c06c07a1030000d40d4650364400c1c3c80c0d862580d00c0220040440c0082d8441c500c415002543e01d4056070900c41700c0010441c4981058a00303000c1da148080b42d01485006030080d0414010003000b000019003844e511030a503e030162017024441540e282c849004885031402a01c0c040340000a815848600340d2146041a0606080442c24840c00700241c1c00c0354000c0c1751100c0e00803000e14092120b00c0e070760fa42c9031744010800c4d4203c06150f59a0800020b0040c100d0300d1030b4a010b507080140041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 878264910 1250 878263660 878263669
    0xf0504060518040203100f1a030d05160809090103060b09060d050601060c0c05040204060e030d0f020a1401021b01061401050306100c08160f0c050904021513090623 72
    0xc403100186400c46500c0c1080a4a4002d00041d1040740d041c802e020103404401070038083c100007101004ea0015aa546803030a40c071010012060181c40382e0026200201401c2e040b10540d80c0380e41d541c10711203078038420b85e1034618102c4c866001c41070b6205110400000c1000301c3d6402ca01c10010056800c5a810340315001807102002d46424001c009810420062100074495a00f1240c01c9000310304025401d96140080307800c0743e00942080d80000d000b5a51601d0508080245030b12105031341c07410a0b00001c110700c0007911000c102d10000c2012000d2140c2401a10094040e1841c442040e019038202920a8482c0c03070080a06115030407441c1d80706d90407501307070398007030300960303200e1180609103580c1014620342c100c81c0da480400044440e01c105229510a107040380600d03c11580c414507014120350940d0070b01404411103540003900c034060341002c000050300c40d0420615501c40c0c020b40c80e500c0c1d1003180001100404160440e4800e04d01d03180b00001c0d2007844c40c46000641d41c2007120b5400e05e40d400703020701 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 878266160 1250 878264910 878264921
    0x315040e19240228090e06100302070510151a030c03040309080303040b04021903080702130f0e3406051810050d060602390306100f0504 60
    0x1002080402648400810078524198400340d1005030400315026980703003400226000400300750200803039013010f030420a00790681c1d11500001c074288401d02c1483d02d8400a07407080d008100074054411403602184490081e01a01d48880d804001e0f201100044e1b10390f0b20080030207090b07403055002500d40001e51070031f8108240c02c803101d8429100b8039640ea80d401b4407500d640041c01c02c40404ca290b50700054114070038400345002c5c511944031441641802d004201c0c0e45110044c0700030030601014001c20000310703801c00300c0f260b0a505a48100e8001d030301d00d680100034a1164030b441e0b0864280401d039450300c040491012080443c043d482030001320404907140d0300200307c40ca1486569040c0784184541c0d0700400150441041049585810f05c280d40b020130041c0750540803000c0400c0c0040758100680201d8000c24014120902c010241c0c42c00401d2003003005101040c1c0000303c002039890740050080c000124803540400602100d01a090041c6880030f03188240c4180d03040307210b00450119003803400340100d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 878267410 1250 878266160 878266183
    0x10030218150a08310203030405060f03100605161e02040e25050904020112021903020d1d0c010e04020f04060e010f02070803030a05070e031b030c240c030f0315040e 72
    0x100840b101203010040d54000c4d959a060364503100601000445035104401010540000406141c403400c1020107509010b15542094051200030b004500d120846011007500840d001303d4283d9981c03081c1c1c1d90a281140556001135003140c1040e601012016000402a2120081e055550304c091554049901403071614080c155004c2508030100b00598894180801400080c55005244c2440100c618242001d0320300300b4404250042516540f2101d035200e21a00b1043c140341502150240d40804d54a403080300e64028140103a0320010003c1e07031500e40c117540000046d200c6103076480c0e844040241060b05041c5815001403181082c00300c5035840400e40c42c0807510028015800c503102c100b61000609401002c1c502001582c150072070095600308203400c01005035036103c5144800a00c10315003400e002403c11406070428440340c3c4000901c0703031a00c1c040f12401010300b5460340c000c1ca03090360561290580c02c505002e0b012040c080520b60580d81c10b0a00700088408002200003111455200d4600d82e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 878268660 1250 878267410 878267461
    0x70f0302120106030b01050f03041208070203071101180315020702040b12190206070b070c03120b01081b0408070306020c06070306050f0409030201060f230d0210030218150a08 77
    0x400103680130740c200564001050618904180042c6000202c0307070030485003900d4811300380c004611035079000504503401100354400f031458108252942040c4100300180103040100200c020301040c01444c0e01400615800b5110308481d01e85074402201940000500342d1040c0e1401d51018400d140280400c03480300e085801030542c02c2280e00c010301c10001c0c23814090741c02c214200001740c0000c442c0c039207061151005031101a00c407290781c14002e1a6585034491150602d10304104050241c2e082a100c80c1d210380b84030500007241140f150100094000c5502c13040340c5120340b810100c1003002c41d030042c0000b80e010b0300880e507242c0e44011046060350300d036114040e00706070b036415070b4042030900c8d400c01a031441c003e000200760f8036910816228500b00c10740c0081c3c81d810b200750241390345940c81c01d18a00e90500807151542110b54540000d608880045d07444420b16074001583c07002441e002d1010314907240c00800d4010320540e014003600882d4480c990a10010b101d1100156604100526103078401c2031049 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 878269910 1250 878268660 878268697
    0x90302060a0f23060a050d140d0503100e090f0f030c0f070b040302061803030301080102090324011203090915030605070f0e040207020f0310060f120305030c1c060e070f0302 76
    0x10710103c028015140382d8100b00310140101e8107445004a070f06046100312412403046074110b082505060768020b04404010742002408900c142000e0305200b0f0b14401d1003141c0f00340c0c464411580c6442d03c0a0912030340f500407001d444100401c08000741408644910035141340043c200e4045403221380c180948412000c0030b10050001d4200107014140c840e40e240205943c034203104001a2441c1c100b41d00c1020169000100c010080c1070507c04184071910b00b4020b0118103a44840c540e264240501a01c04400c0725010028140f51142184c08010514203000300700d00300000d000c4049002c814001520307258204004107005911401140750300e00303096514440c1040040c01000301075030008000342d900040d4905034a2503998144000c001d04400c0c1c01000030700070300d0701140209001256110280e60240c90703c543d4040b9800c0011264081084d071480b65039024294442004450143d1085050300d24205c4080303031003664100080e0040b2240d40340c21600c03850008007102684a00d10290440b01000e8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 878271160 1250 878269910 878269961
    0x9070b03060301150f050f15090603070c120c0b450709200a050a0c0c0b0706051b1303020402090103023601030b0f10050c01090302060a0f 61
    0x100285402003402000131aa074450500001294041504040c44a440d0000c04010900e42400d144400100039262070304500340c039920310708650140580b0b05004440c004001105c05100315980ca24282e0b10001c0343d049404440d90050050107058411aa040c0e0814080741209050040440032407801442644400d60b105480e0302108042002d0582c10040000a80008460901104014028a100010302c0c858120203081c0f100c115041902c1c1180000c2090400e407640c040708940117a100c40c02d1002a0446501d1314001c400b1455012040c02400401e504082208513040755000b81284541102000c10b0204030030180d100360100e18a52010b1580c0410060906401500011724141001828000c2d04c5140320038002003404418001f02c080b004042407140004881b01c40c020003840c0c200507100a0744085015403850581c3e90f48500c81038100d0b45400346c490320481e8ad659101c00000d01c03402c1000d2401035510002901c80f9550281840c030000d10142c100c0c441c0c100c64510060340c1c05800f4101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 878272410 1250 878271160 878271179
    0x1404050d02012106080a05010c05040f06030b0609060c0102180405010b0405090a02040b0f04030c140a0308070203010905031602030c0306090319030b040c271511030904150317030907 80
    0x3d1008100202085421583c001281d0701c43c2c00020040100a819160100d141c264210707650004d100060200c180418003d940c0800031140030f480b441d040004620350b60350300140860086101040c0e101385d0000b450382140da010740140250305098080241e4440744e8004120540b03409004040f41c4038024403080116142c19055160020101c000c014941a210140314442c1d80c800d00522681e450006410001c0040003e04240185450341085913240c190400061040900348400751903414081516402d5540a6020304601607000c0100e0740c1e141c040b10944510300741d1380034041e8032030b01620340c003650f0608010915510a420020140d450624a50490f54840041190100c00c155030f940b00c07429140c540e442031452825058641000e000101c2e4002d1000c80c8840d04802001941ea440c10081e107000003107114101c0b481814500c2580903104002c6142d4041e10002036402401c164041c0391000c00a14410700307990198800c448524010111604584402e8600d41c0071940311901c01c01c002e80710f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 878273660 1250 878272410 878272427
    0x209150123130f05180f010306020a0e030105040b090709020906090d0c0305030d1401062d12050c04170d080f1312020607020616120506010c051603031404050d0201 72
    0x16220805080c4003040d40d400b24682c0198100ca9121101d07490288054501041c6907141030100c0481e000c400d14184100400e18041072100402e0a50049580404240644841a8115800703802000310b4907090500b41050350060300c60784294016804080b40e80c0e0018002c440341124003904080c078002810092060b00c0d40d502c041035442615124010000035000c1c401040e90049046000c42c0f95003009804800000c2c0680c8840d091080d4264151059100ca0340300c0341642c030351500c1002264110070425034000c800004074443c802d103013100b00001c50b440c08004c6e1090b01d05500032240304110186410383d071054948290000f14460720005041c400003d5444c6600c507199110b00c003c2c0340e04640da4000c90500c80350325440960000400c00c0452030381044170540c460030540d440d00240380580e90207400d40703d01e841035000d0340380c6480004100b07900480c1807007130b0142d00c00c0c12140c0982c00020342e00002d030f80a00003103001031464203547c6240a2504280d0301a180d00800001200c0140e80c0152540003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 878274910 1250 878273660 878273717
    0x7080c031e07050114011203030c03110d0218191401140705032206051b0f0a030f030c08101809060c09180905070b0a0c06050c0702091501 61
    0x8410011140d02034203601e550070004a111010030b46460035840c10500351000b00000011004e040c400400050752000e09101c04246c050a000804416030b003411800b41000346811031810500090412210311203900a01e55141c450741c04c0e051800c20302d410050640064000c0c49036040700004184200101146d8444880b00141402024010800348414483d04000419601390701301040d100e0b228888a00c1803082480e21020402199003442d9020345140030702403071049ca04046514082d40002c0802003c1030b44010320301143c035654501c0ca0010030714024240c5c1c003c0060b013050069481a401410058054074144a1020100d030401c1c00050307100051504c1c96061584814404000c1080341c4150182c1002650f22100300740d040001c00560502136074900601c480c68810a000400c4011a9400c25544045040380e5502e0303050204071082c1c034050402a05207031820080c4000fa00040005201e160310075101400b40360b541c10380403001141c0107144140422402c413082d80f40904009101842c58 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 878276160 1250 878274910 878274913
    0x614030d1103091c0605090a2423100e040206041502100e0601170f1009030207181401090e070e060a080a050705040b100c081c2901050403050307080c 66
    0x2020303d01c00151801c03800400354840e004003400000a21285010744e0f6070100c109002031100c18250703500c900c4810b5403061440d03c10701260341448100340d010b402104041203034001c103500c02050fa0348181054602a02c405001e45103903440000c0018000550620035074000b048075003024580304210210041800c010003c502071440c281058121034800c030012800124024500d940c101100b007007c8108038207094411382d01800c0d009801910000c0c80000341c1c008044049a114001d01d8180d20341b40407500183c0203884c0da294510700c5c61201380d02c0860029101d201862182e41d0745c4084c501180c0300a00880003d4200e110309124101f10110410f81001d0041c10544a00313664001240c20100980012147c84e0000300d0100081d01e054019108140c50448441c04800070703500004e0b0040c554010014109000410484040e0074a090100c441e00b10658003804480080c0044c0c0001010003142440d403941100e0014a407544200706075810340f640000290318207906c41e1661034054101c041440840e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 878277410 1250 878276160 878276167
    0x170d0f03020c0316020306060f0a14041b020c0301180807060e030d0e060603070f050319150903022b17060604050406080318030a03080a0e011b09090614030d1103 71
    0x6000104001c0000c02c00405143c0f41104d59881090305020000c3c148510940020304010610740d01c6580140440d41c210300f180142081c4800071801522129040c003003441030311803a026019401054616074414220001c1103c101e401001826010303115002404421040c4540c200040b02940300004040794602281d04114a0180307080c282e07240c3d021061800c0e0408020300040e0300303041211001a1090030f80d00c0c481c050604000c240d44002c58845000003003925008942406010500d91403610030811080c000c04280f400d000e50307104201d0020b00d900460b4511500c0d05400b8a110300320b180da030107a44a4402d07810b8003070f028114080152403203600003010440022580d031640304160080c0700c1a0051a207569142d08a4403010014500c2580281c1143e0002c5000a902420f10b59020248482c00039002c5400d40740540185103201d580003180704640041b0954680010341c040480307180000a019181d1691701000056244042c013541540c03200e15885002d13805007203805d50241c41301046905 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 878278660 1250 878277410 878277427
    0x3071205041a012d1203080a0f020d0209091501020601050d150501031b080318060f091003061401090e180f07060804060e030a08070e030705040f0506030106170d0f0302 74
    0x1d4a1080c1c0c045040c04440103241c2103c549403501c2c40002c01303484030804413810318101e902d040c0704c00c031080018100419900082e0790304481e03a006691000b4182c13003c40d100d4101c6418070000358001c000b4070344107400c00b2001809040403091140000e22041c2e000d02600e9180a05000034016680c000300d5402020326600610050180b081d02d000318058612a00c1c3c180c4014415200040d0f0394100001c1500200300c4406401c4810103290742000f4140c071050303580d0f2803010820800d40180914250300240c04480b000c5c02c80c0c3d0580080301500c408403881d03014011840019116903142d80b254450240400000407401c0701c800b4580401172502c0410b640220001c2070a070350030402d598001c0000701e95004288018414944908540c0d811080c005600d092880c1c03102420206000340004100f01c003480d00400551418080301c801400b020340184614101060b8080240a08807841d50184d0301c0e05034000385110441c907900b80b41d04824006810b050311603040c11034005d0f100d00110f10038183c007000040c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 878279910 1250 878278660 878278703
    0xe01020408032206143a1517100f110406020a1502030103110d08090409050a060e191e021e03010c0806031b04180b0a060b0307120504 59
    0xc245140c180854120003d20400c000c2412041d08010b040214200c0580c4480301c840f000c42d07503002401e140d003840c0502403400c0740001c9007a000d12201c0301076040c1c1c28031011000c950005940032040702e80b81080aa2194848007151640d140496055400600391079912a0075520014904440341e0f40800ca4180128984216070700c15030040005a000c0700010701480284c6145150000e02d038074065141d5491900c41e00118031403001c1c031a204403a966426004c100548040f00c00040c4043d2051003509194240184c6655191100751085030628040031606900810390700008016603030070700481d4026880341c095031a41101002d021141c81a00040541d070340c03141280c0c45411941a101d50301c1c152006244c00e5441680c40c420078450080c040c04041e64021841d81049480044800d0750701450304005006004c0800c140440c91003490207941c10b00c20344102c0140706e22050b00c000d100315552100700c2c001901c02141ca04000440d104110740030341d079031900640c3e042030040d200d0645141c951004071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 878281160 1250 878279910 878279917
    0x607171005093301080411031f020c0f0c1012020d050a02090f10090b1c060602061f120f14071e172d10020405040b03030a120e0102040803 61
    0x60803c410301890700300310030308120394401030440b2070b01000c1c0e003805480c1d0000c0c003100f07006880101100100d130800030503603c01f00b02d50040744216841e40321110740080d0030400254003800c1e1048a500079400910074050300000c15050b0000080c04a0312900380f880d00c212030111400c00002280b039000c005000450813030303004460090840210042e5121015000c0000e0440c424051034001d266510703966010fa078214030b03c0c01c121007405411035074480c0d24402854804169070034140907146080300c04521260300240301d5200714041200340c01140c070903500402e2582c505110b00c8003c2c4190309800000241d40781c500d506810702c1450001d0701e03030002110b110306200c0b154100070010504000560304100d0181c00d500010002e490b0b04401045014000f2502c40c03c13a00b1000005c5042410048508452207140400400940c0c00f0f8420b0319080d0400e00c4081e60042c420786104508004100200f850080211400380c2c04d2074171803000d90070b0000f0068003e4140954500c0c01d5541c00c0c4000110301200380001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 878282410 1250 878281160 878281171
    0x3032a050105010914040b0402040b0d0605040b0f010501050c030f0a03060b12060a050a0f0e1f0b0c1506010c031107050604031a010801020a0c031119051e060717100509 74
    0x129507507050500560403182c01c101007180a00d078900500002c940d8247d0300d0f135005501a140801c10990b000c02141120b000319400500542c50801000148804610503501480103010088642c1c1d80e2800111010301442809007510b4008020300c6807030880744002800701c802e442c1000300b00c4642c1c828600c440e50f04445446440001104204007282c64070f17000d1100603282c00c40d880000c903070424481407240303065401500585502c5502089400c1d4141541414030720942d61342094075501d690411241390031040502c80300f44101c2d1320541e2025072082d20a4828501a5151004001c258608468442c520014210f00b40120030340170405448201c000c5c8065030181e80361094015243d2980710400310140c0c441509644140550308955a00083c2c01041039014900203015040141036503061480181c1d4042c00c603107030748010400700700c008100c150301d10944404900c440201c7c1a980c640f9000125034540000311028a0103501e003d603600f4958104080c0f240d03ca0419440e60049452584103440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 878283660 1250 878282410 878282413
    0x30c030d0b0f10050d0b12191704080d08060301050f04020607030c0605010801150506040b040303271d070908030409090303020c10020c07080a0f060203040302011b050405270103032a05 81
    0x101c5c080801c001b8010302d03008034003c1d01e800311180c0c19891220f031900010040c2c620080002000f2809020b0400150201026041a140d0356581e91302e1603640c0d90b00030707030380420082009071000884624040c071400d0311030001078910442590303541d403c00c40320354003a2030100d05200382c40c00c0c1c0e440860068400d03a8068007100000040781801c07001107800751202580300c14401c0b10200300074449450b10005440441e0350504204025504e06504807024be041407441d0b080100241d64002411341d4104205062840080c0401c507403030f03c07100d10480340100d0900407409254001c100400c180425a4000d2101c180645030050400c032100000d07a0402e0001c660149c880358022600d0082418144912402802d0340700040900c038950343e44890b0740618802d8003074410b6a01100080078036000790460a08200d400c4071302180d07402d41c28030150454006025060003401c071007103215000c40880c0f081c450f10811080320100e4907880c2d41c0e030894820080303070001803a0101c81074402d4400107201d10040000b81c403400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 878284910 1250 878283660 878283667
    0x3050309090c1c0506131a1c0b0c091e0109211403090a08070807060c140a060e07050409030e0d1b03060f050a050105011b05120403050a02040509030c030d0b0f1005 72
    0xb0820281c22911600c1b401d495260000049285040201410b44031005460f0686060500b240102d00f40c0c0075820040e05000c00002000319084619000300004c02c0c0c1200c804900f2240205c45e0fa81c401d407480c0ca41400308114020500c0014800d18030b440c00c44c0c0713150b42040400001651000c16001c0c80002202c0707075a02c04205c0046615028540c000501000001484207502d4008079030303a40d403514407505007400600c0038454180010300395100c3d08021003070704861030b01c0b00600e00200100b90074410066070307025039203011a03240341902440c40c805415541e80d0341e0400854040024200300164220399020000c0c800b42c144506d02d8415900a500171540040c01880300391006042d210001d04107601c041c03411005004d6a1303001050902d5039410140c1d2911817240d9840c1a44c5000018201e403032030b0341d00c007140000410000080d840011482660140515101c69402c0b564a020b07250105d181c03500244940c2001841c0ba520107a1181d4008001143d082a801d000c1012100401e210f08001030001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 878286160 1250 878284910 878284921
    0x9060518092e0317090108010e250807021513030311040e1f0501021609090c170d03060f030f14120f0301060201050f160509040f0f050702120403050309090c1c05 71
    0x5004e049003084210030860b02d810a4000001c1440e1014004c0c403280021160106251103546404124905c04026100038200207011010305160000c4800e40014403400c2c185007410390303040306c0650103500340900c400807081da103580c00e901508940d051036000a00c184000900401c0d01e071140c1d405022480d61003400ca1004100c2003400c01c07200c3c0c00650640d800540600072000c04a14410102c1e950f0001c002005141c41c6070a1129250503071041c0d08011258941c074440c0280814007144d41115a1010001d003541c40002110600b55840041c0003441c41480310030105070800700746c020151910003a28140c1c0d00c94019945a0340240c504c00f111380c0c1c3c005c40140003564091081a03002421144c0307800640c40c001340b007100040088105c8004101e8007250001e41921141c1000c80305152181c0284060b0f50b010500e400201000c0b20f103000148140d912011010301e00e1000c65003903a8006015501d0807450b202400442240509140c003202002c000c07180c800c0b101c0ca4585d1800c2017aa140200301c03400c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 878287410 1250 878286160 878286173
    0x6012d03140a060b1204150606051c0509070515130e0414060906160e06030103081207050c030d09321c021902010215041209060518092e03 61
    0x81018410034944034091200d00513000036920990080704803c01e242d1340c1c1d40751490550b105130307810040840c14020302288a903000405001c8130341104260107440b60340910060150741c0c090300c403001c55800c4001c05203c903003441210f0b580d015000c90241468401200c4810461090540c000c5015541c1c1c00280b00c02c020341d600c81604100b004c1001002d80b418855255601c504000c0c02230500d0402c404400c40e21580244640c10482d1001440ba80c1c807507a4906204281b5444400003200e00c400c004000f681540c043c40949404444500003181401040719202c0b00a180e0100c040d1410040d06806000c0e4031403509468502580c01207031244d102c203410002c07900e40858061100d14a21382d05c0740070114550700040c4104040c45d8980c000f1409402e82c00141d003042c000c10240001b0040e103c04020a1280d60060000102040c0c1d072001a07181e50749400b140d06005003031601c490300e5104040b91941d071400380c80e896042800e00c049000d902c2288074044070001c111145500c3c001d0252441041070000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 878288660 1250 878287410 878287451
    0x10203070e0d1a10050d060e0f0f1207051e0a05060c210c0d11031f15030e0c0604081510052101110a0e030607110606012d03 55
    0x406680303800703542203156a1201e59150b8038243d8080d0782030040000351206282101ca400400c0090000410141c507400d02d0b101512240c81c640619210361101400c01c0040040c8003004042150090441000d1807400103605600c20308040d0342d82d01c11508410340e0354030400c005151001180c0c003303040e003103494606175082460090000c03160b00c02c24802c100c00075051030740c8514248015140c03079078acaa5540c0346a44e49800340d5100000400e1901200c0040c3d03800742c1c0000c602540030800c1b08501070300322111040b000540f5000d4404080c1810507002c1007140290020014020301c4403d84680348405404100e20781c00980c050540e40e802100700f82094684002c0003900715178040c20b1192210300341300c0450000f0000c18201c0e0607645810321010103501c4294401e4900c000c0da846880c0e0b60b1001c0110003002ca5011401061080c01a01f0216082a005050002c080c40d071032070260106540707820064602d149911200f80e030001c1d030418603c802020414010b8010b034100d8900040c0c0c5491a00a030841e5603 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 878289910 1250 878288660 878288687
    0xb041104090c0e1e18070c05070803341a0a061a092202030c07140c0310050606090a0305060901151a03070309020405090a0302061617180f01020307 65
    0xf840c05840720300351905000d94483c000340030300c84150052030a000c9072011030348030194450f00003180284061517500c50400165103002d0411984d82a44406107141c80744140d8881d08211201c1442c1c18101c140c0b040e20483c550b80100c050f016801040b0b8542040c5102e140004601306141d400030480000103512070100a0901440d0381284400c9500b00516640700b0100c0b010f1280414400c4126145036030451101c4003000079070195101d040110310050990400c0c41c0460f03007070008400c00040300c207002070854000d600040042240003c02e48400000b0030b405807405070088801c12940c03025444120710b09000354415401016646001180346086848200b03218181e02a00340d800c006080d00c0183e01c58411008000050b5030b5100d14005900501c0e003400025005800c290412002207070102d0200000350007074003616001d40d506610142c00b03a1040342c02c00040303010b8100c0c03000c0d10310100f103100398002c402500440b800000c5807401464206500303940e59650f03400200304150258800c00d122040d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 878291160 1250 878289910 878289917
    0xf05180d05071b12050c010e09060d0605190222060203070b0109020c03090406080604051e19110d05061b04060f0516060615110d09030b0a0b041104090c 67
    0x114454000401511409001400350036203c400c1000329015100c4190040c980040500062600c6140c2161508119850309012900c084a2603000303003081441c1d00e200343c1004005628000c0e480d6201d10040202824440c55441e00b4014664117a0042c802803a909519111000750340010303090700200040c0d01d410031411900203024000c0058000c1c111079041d90300050015032101c0d01d10014910b18001c403440107902c542401c10024004401041443c000c80c013420036100147c05a011090b80600c0d251040e451542c0610702e00f030710355603140f810555014030408001054188100000d501d59603440d406031855001542440200403042080141c004501114141414500f400242159464000400901c8000102000001040130719924480d500c0329040203c0758403049980c0c2000000300c0800081803454030342c4400200c1c00281482c2d048020f6581740300c010b00715035402d002140b000d011844c685864124440080c4d42da4000d41102c0100700c00082d4845150001c03440c1611240545c10060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 878292410 1250 878291160 878291173
    0x10b090609010818030a05040810060b04121e111305070806040e1509030301060e03070e06010509010908060915060906030606060a02070b130311150403150608010f0518 74
    0x80d46036281924448036090825a542d0f42d101103441032950042c2244410ba400006114040e83e500000980b00382c07a4007800300d0b5403042d003240f840c400300c03441d900502e034110400384001c00050220456075040a44145100e44144115420401e4183c81c01031084446214005131040181040d0102039040750294000380000e080c00c0780044d105200c09015503000e181c48103502500030310304020070000410200030408261030001300c01a00e80c0c000b0700410000800c02880703038800e4038000401009071072020031465403d803902c0d401034881742d0002c1c008505109022000003440310090064901c42c01c444070280c05c030900604040080f00000420086c0f040030f002c402c1c442e01e5100064210342c00801542c2165507030382140400d03850300f0bd084e84010301c0e802d8002a8200203400d078a4099040300e10444401d800900c1c64010014032003078040400040100501080001c5540d424501e02290000140083c500c0d8613820300c1801d5903102c11015a44a4a8074140b003031203103003403854148a80318240589403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 878293660 1250 878292410 878292427
    0x3280f021204140a1701092a09020a09210309051503270d030605091810090201050f0d14090c0609010c050115060c06060f0e01290301120b010b 63
    0x201d6001e240034103031035510b15030038982603901c6220440c4041d0a0542d41d00b0702c1500541031440c083e080202080f02c041c80d0080c85601481001c0c04000401560320103086074243c00c020b6080c00075000b25920200700720b043d00000a1311100300c0810030070044850b220121080326418054202c08003684240c0c041c0f1040060007040c000040c054a130418507940c02c210b141c2d009481c15440b150b00e850300e00d4030240906564a40000d030184d0121003220380641342c211169842592811040700a1444200340390001c84039180c0c5d000c51648a1001a441410b0107400c0110b40c0751050b44a07040321000504e0280e0f04d410b41c00004001c0f410960303000207031800404075114403c010452a01a544043e0305001c224050602000000e412135044071003200040008660f40d6100200741c80c505103016039005140000c0811400000e1b903620303050340c410003a03020b40c991074610030071221449000c0c2010384a041622100007180c01384c00840c028400003182c030a580d070990030000400f9106030701c0417405000c20041103c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 878294910 1250 878293660 878293693
    0x6010305121c0209040914010c02150606031303090905071116182d1b09080705120109140609010c05030f040602070f0c0905180f0604080a0203280f02 66
    0x81c0d80311082100940c0707138400c071004100584a400380080002c116008407150115055100245041361a42102c0444070040510b42c1d03600c0007074030740c2c98210204200041c2c0500c0f0860400f1001071092500300c141030744d100000412140e0a0f034070400014210703c0c5030010326000700314100f600d0410200385003480703250801c00030708101c48040c072207c11a100c85810319250b9901068a50000710700c20036183e445c0348c481650f001803080b24040c02034404840355081c0580e100d0052041603507400d0300104400d0b420042001749405d0502d94580c015921108840700061411650025002e6860000d0001d810010b15860a4450301c2d6078004c03c03c6428020400c29903d03c22243c1d401c150400401640c44409c1d041a03022080c18900103000104280000180358006d039000ca84990340b00022510b003903880500e03054442d403240310b84070010b500c00c00220300401e841400078450003800c0e0049a20f0503040c3e18000c00c0011035060440d02d298404c01c8100c20140d008a40608244201d1014016034001210b009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 878296160 1250 878294910 878294947
    0xc1203090d03200102040e010302010305100b1e07050a0f02030c120304050d02180c09010e040c0f0e061303030203040801050a1415180a05061206070c020103150b0301080601030512 79
    0x38081107181007102c81c19141040c98443c41d516154000e540d00c944400c40540791103000e1004a0000340307450002840940001c4c00d1f1000e40b007a1242c110318001d4012800d100c6a08801c42229806200300100000203d00300852030740e403841036010309441031f010b0040600704896520020b0040c5440c0f01c504a041401008443c1a41e60071a240340740d0710242d00210700550205040c03a0f19110003c0706010984044202805020a0990714032410640903c18030069900000700d5101140002a42c4500107009405080700c440340039000c01e04107003e034210164000380c19481070740036820004080c00b41038400e01844e40d014589440c244081c1d48100e61080302424020103150650b000712044030540e50340d00102e60803210001c1303e0807080b41440d0309041d000342015283c0c1441a8080884440a880081140340c4a039040391a46154940c2c80d40054000c2e126071b48580100142506000c120902001c024501804080c0d00608056046140485c500000301c100c0d80e40e9000d0500020198242c0181070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 878297410 1250 878296160 878296163
    0x15110405041508010507020601080c031b09040f0512040914042310110a0f02010c050d020d02070f11010206090c090403210603060b0f04060302210712050c1203090d 72
    0x180d11100c09100c0b580716900c6800403203065007000103100c0801e80c00250281aa00c0080c107031064101d0201c1003503501c00080c3d0700e88883c90164031502a95140645000d5440b0340500e2070903d800605070303101420004081408900c1a00214051001814500c00c0100c0030030007030600103030341c00e107a00d800c0c440a0180c0b010003060420746880720200c101c10300060103a101038203000c0c010441c800b00c11000c030380c002d054104001050b001455181501c140980481c0f4886902c5051074824501c0f814006903200610000056400700b105a000405114028001c5130142040300c6c40c044007440028103003840a441c18103568001051036100b903590360f017441d41155050910701184080e02108207800d80c0300c00c1150802d50b140c41400070502150b41c0100540240c00c40c0e0384d003145102041044201c620ba4040690405c0180d41d6910407030300660b0396445455108411900e00982e91050720310056610743c802c17160354100f22143c42403400d2102000440d606400c01031420050300c40c2c042494003002180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 878298660 1250 878297410 878297419
    0x709060e0a0b03040f0b0f061005180f0a0308030a05010e0c0307021207020d21020f010e030712090f03030e0a0905010305060a090311160f090203041e0804050603040b0415110405 78
    0x2c02d041049003c10160015071202c50b40700d262070801c42c003507221002210014010710000742d101c1035990ac5542101c06140400845080d5100300c40107006134050402105078200c03500700c0010005c951030070095880b0305240540405c039581449030304100350300c002d800744143d08403c0c0140300710b682e00401c02d4180160805581500c403c007600005040e4014040041c1207491008a40e094107882c0440503a000703104c54007280c400c000840d403850f08940d18030000c0030b280d4005000b000001101d50298040c07869483c946416a552111404040e1064940c800c138081032440f80c90703090a040070a070b80c0340180f03030190302002a50701d5030b11100d440b4070004002a0600b1750342c1c1c81c0312081602804a112504034900c0440307441160380060386214040078042c40c0ba444a04010000b0390802500803248521303408041c14829001c0340b50034100140c58035a049940b9a41480081190f481d42c2c001340d44128040c02e0421071a05240c01c1031100e2000c800040c8070041d0810820041ca8244d0100311001c5031000d84 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 878299910 1250 878298660 878298667
    0x3050a03081b0301030b0402010f110a030804020316080a0c0f0e04060207020d080d090606050307030c03080f0c010c1d04050c041a040b12180309180712140709060e0a0b 74
    0x8980d00040a1402c940030b036000310000c0f0901107001c03030300b6209502c00e80320b00c01d001d85150003c2d15900d849000e05903141d4000303441400028480c03002285c10074805000c8402403481030282c04018081504442c00d02d9010503004028042200840d00c001c200c0343e10414005402d04c40d60229000d0010006401d0940000c0e000d411519503044070b0044580161965844886184940000d0103520b281510b81604003200452a45404201c0400300d0394050060020145195140e5005411041100c07214980070300010020f4002030003281840500741e502c104c010002c04d1285185c080c07402190b28040c901c0d09041240c0e22010401310b400b500d0b0825102030440ca0440240c928a1040f0b401506035030b03002203441040d800139500c1c06030080c0300d20106614402c501c5410b075035813800340f000c44540c00407030003408280c8000d503220559000310040c500024400745209841e019100c16500311000d40b01c02c00e04004419038841e550308060078042c544148001408000507481c41c070240200f107503141002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 878301160 1250 878299910 878299921
    0x51b0703050d0f320705011e0f110409110403350c0d140903100e010e1506010507020d080a020a1104020405180618010807050a060309020303030f090f3403050a0308 72
    0x44c8161070300290f04c88020700205140e18007000f03040c251848110201ca04260209041c80b0307060142400c4c18074045159400c06281852120240c1030b180a44026140100300c040041041451026400550760106255181180c0c0c445104160311007415401000b041c07000e403054220100b0b6042c2100d02a142c10425000258402d103000e01c11041035590501ca41c0c8501401c8480700c0c1c000d262001c01080c02081514540490f45403141686c0f00700e050711a02c94070015400758000d40141c40400c1c0040d080e6a00b881443d42c03007910a5000707408460140c3d10a403601c0e8208105d045414015010644003942020b140c000846e04102c14a03114100031101c00000070303d00c1d22042c0d098401a070b141c8000080c0303540d6030400b03036403903620900555000b003480450128110b4068019400f00d9a40a00207500e1070b40e4a80345002c91000c0a0401c00d443d008040090b824000d081280107083c80d070700d900130044441104404128808040343d07101104250001c2000420400b164501901d9014109180c869880 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 878302410 1250 878301160 878301257
    0x30c091206150a24140d05090c0108041205070510060b27010905040e03090409080d0e060f0609090a2906030c0a0317070f0f11041b051b0703050d0f 65
    0x22002e12100307000102d1001001b12451f003000d40501081002e035500c0c24520401100d0303002d4100c801500005400c507031003100f20b104600034408540075605440b0390b1034105401b0310648e50250b204140454011035248a4494990b030425400c00c000030dc0b5808649400c00046d001c40224070410788036598070300e0358080e8000103104079088041d00400400444456207800900c5402c45070408032041c1c680207401e6525000040c0036800307a4030315100c40e0708668618042000b4a50024000c80395800307038003942000501a8000054008403a110030544903c04040c100f0354030000034030080c070030b034800c80801005031903041c81e68003669040703100008000f40320071090340144503240000f40151003e032440424440b0000060001c41d03c104021460f00550000b04015a20f5805101f08032000f054030404030700d4068801404820140c2040c5c0d041030744524a03550500c5030f140c3c001e8400e9004021000e060561003400c0300d041c0001410000c80d520030307000300410000030003621018800c24018004818045 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 878303660 1250 878302410 878302427
    0x9110607020f03060106170f01061d010e1e10090e04140a05070b180d150c121401060f05030f0103020d03050c01090c0e090304030f0602030c091206150a24 68
    0x2000f0f0100d582659481c9030091400e1810002c0080c030300c070045c010a43c03400344078172103604071500b0b51350f040c0c41900e00940c1107200340e10790f10b0443d052001c0300c034144074a91288400c0c44401144d0702049124050305209101c54045103000300001c01600310703004d000807460810041e8119820070a10400e110380a00c005141c2801102701030140d108800c800910041d90744014005001c682940c0011001c3d940180a0702c040304142c014040d5140b10350043d411001544054403020203803a212020640c182c02d120300f264551050707200d00100510040c0401900040f04a80600d51890601d00d1403a100880061854060000074810307141c101080e03003850711800503034a102e81004002c01000940e0301c0c01d003d904445200380c5c0c0c00c040100c4009000a240031090b682140e40002c048060900c56942d450020350000384680400380b014011a07106072507445a00542d040302d1801000c983c106070b01001c403400381c01c20380d41d803040c0d0b1030000a002c0808902070708401c40c017008240c4011206440c106441541 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 878304910 1250 878303660 878303689
    0x8011a151e120a0f0c0806090703022502040b06031003060b060f0307110f07050a140310020c030c010b1c030f020109050627030307080c211e0a0911060702 68
    0x1e02203500030001c005203041c14007a600c0b6900c04c1107214456200c101c180c0d2443c3ca40c00c8042170400300010f195080c003a03a201e601ca40c0034a40103145c900c15002c1280701444030080c9c401c1d06c0502c044a1401c5040038456400c070031804803002400d514007403022440c090142c0c00000c280588a11070380460352170304419100b807005c070326a00640f02d140406008144840d02e0b039102030603210b9107488406600e000b06995042da58080d08a040c00b60411b20240302d44003140e10403540600c6080b01c102c4011a04e403001e041d0700c0c403508002d507070741d51510b40c03035242506c0348030007024407030302808803200c1500603068000d01d0860f03414142482c041016141c1130307004000046000d0000d010790701c100221015883e91004920350300499400d8016007407221715580c1d00044465501040c0008003249480700d83c0b20217048031071595103d035200800303400351a204c101c0098680042007100c07462194141905011010740c400101c0a081148590035101c43d000c2040b98140c0030b01407c00002e0960540d114240c07100e4544 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 878306160 1250 878304910 878304967
    0xa05070503040914090d03060303140c120d24080705040b04090c0b0c01061a030112210525171b0a0f0209070f02060103020603180d0908011a15 63
    0x280c100751110802d00303c05c898802d458041d0a412010322402841040140ca405a84090400c8030340d48111005038056001c580040c403d120120030303011000c0c1c004004402900c040811800c189102000c021403444644000341c80d142c50f801d000c1e083d000200002200e40131900410820302c1b03480440d005043c50a005000c00c42d001d0804140311911100800605120301c008120055072010740000212006c04500303000501040100580700281c0300751450a406505404962122a41b80c9500031003a011840046040402c900700c0000000440e9190702c4200059800200c0e42641da1050060407100d8000f820000030038800f8030888124103110750a0702200840f080704032507040080b1107000c07941c0c04a22a00d51080081c0c1700342d1103050b405580403845d8004003002d03402c1d60b08100c07194100520300c0031089039461107400c1c4e0b48000c0000b111a0000ca440307003507000e41030078400c03400c0d00c020254002c038a204e080da021400d51141101070908403503a2a0031a00d5007552014450030110861464105 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 878307410 1250 878306160 878306171
    0x14031005120a0c06050f03011806180501050f06070f12031805100c0509030d050901170f101505090111030c011b1116063b041a03030a050705030409 65
    0x144000020031011460050f41004480c0f0b5031491300700c4007882807030011030203c802880104904600101c00480164644201049040d01c5008103840301780640b100c11140703034403100100a2030500c484600701813801551140d1034400c0546503040c81c50403070140104a040d868000440083c480d0703005240e0403400c8000e1044a802ca401c10542d99241204e1001440d031a082100c040d990050044418081000d000340c10030a40c185010b84158110000c050f052004071071030019080d2400c1c1d40c20b403059880c2c0500101504001034440da040c0d029800ca02d4030360380ca210a2a0600740c103d4207441401c0c03170900e0f00f0410748420150060442c007404c5543c2900d9170802c0d000802883c0c1500e00302e0240455907441440c5421004615650307081005902c540c40c11503400705220151040603410000b9007152031140c80c0318844248044000300309111045080d009a004a43c01d2505010310601140050041c80200b040e000010341c0b6446115506818080e0018040c8100042481500d00401010008001303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 878308660 1250 878307410 878307439
    0xa0314090a03091e1e050d0803190506010503060d0f06020c0331140111070e0a0b01020a110904140f010b4002070b09010f060e010614031005 62
    0x19107a10030581200400c02141c40481d20740322401d915845844148102207955103014800e0505101512207012840d0b07008501150545441282c000b04610541c41c5503946c0c41c0100c2c4a0441e00d40b03110100d05030324101030520420340c2e40304040da078000d402198160606021440d200c212205401e0008003018000b00c0d070480000008001340291460040f0181e150071003d110072148035140d42c011000b040c038604414000421004c0000d41840410b0510040c07404070340d0b56075403400b1802e030300100c59a1205c00c2001090085400b07100c8940400b8002044080444d54948480c02640d205140c0641c4481c0c0000b8240845010108026011941900c000550b1040038501800ca100c8805002d5504050011404c0040b8115503460300c44212180703040a00e0141100070445a1343c0030704004540901050b00030031908900c030b5002c1e40080c2c000140c104002c880c0790003036540b95403022140c1c8518200401049800c1407070000740300961400c1c02e03926910404c0110060383d50360000c0c2c0c0c102070480c0c100c0c02e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 878309910 1250 878308660 878308663
    0x1e0303070806090405070902090d060f0c0909150924030f030e090103030503060f030f0d0c0605061002060103031815020f0601080304051c02040633091a0a031409 71
    0x50040d44039a465035001c2d65618140b10b01d120058800601c980e02c81d075420001c0140345e501401c020840284010302886007038582c0001d603002107984146240c0d8400f905850203400001c0d550090904000c18402e881014422018022a501c9000d40365a103e03400e0007040c2500301e00b000c807840d0b032003445031350b10580341d0500c02c4062100751070850110303501e03503105451881c100080c1412240e0503910540395a03100f9040c04034030307400054035a4042c4039070f041400d00d22906001482d55450f071540d560300c2e08501420a03500380ca5019240c18003494052906011042e40851030700d0540790103041c10354003203584d40c0a0b580c03102200c0c1e01200c1c040000b550460320f4a5404542d504080580303c0c07c55610f42d82701c5000648030320451086a07030084007030310440142184011804c50706c80c002840003a045a540303082c011041082c04114000d1141c0c3c1c060302d0950b403421480e0b05540c0842d842d022401d44d041c5200ca403020714100e801d1103440400410f80007c501e20a4211a0480c103504c407039804941000d00845 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 878311160 1250 878309910 878309917
    0xc060705150606090a061b021f1d01020604030c0309030206120f18071e091109100806090604020d0f090506070201200a0309050f0102070503090a050d0317091e03 71
    0x10040030342000c02050403843c045081d104808001007402500c1c40c40d0480650b90708851104203c8011185450035004d6502c018065841406442c0a0440c8101d00750000b0800300311280034940a503a5851150103a9900080e10790344980e06003815016040141025280750b0f00580c070081d4041c5000030001d22000034054071602a13890044014925180c4511468030a050020829007a0340040320800200707603981d003072296100d85003281214094481c24010107803420300b900300361041d80014644129060440b450415603015151181c1d05d42024400151000c001030580740c455a00400c0460703400c451a400440c5220b80d1890030040c4e003541d46401ca45400c81216450007551a1000c0e8800096140440130102000c03517200b9440c10303156050590040c03882c1c001c1a1a0f40c880d000c3c0180000001b4401071130000e0058000b50703184d0b0780300340412041c614550031050203031a0b601d032010700081d048405d40869064020b0303818699a650384032079140c005921b6140701c10042900d5a4801d100022005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 878312410 1250 878311160 878311183
    0x31a060112022b090528020604080a03140406021c1101020304030f030522020913020307120b150d1103030c03040f1e0501080a0f11030406021c11040b0c0c060705 71
    0x2150f020300030f64881508903006070f003014013181c110608031500ea144040d00e10340c664010a984441c00c0105401044140e0403030382129006903c044042000c1c15080707840003600c035200210061605007042c40023919803c0c00301e61070000351600e01d0510451802030160150b90b82071071000319228038040c00e00a00380590760419001282c42c1c0303000304190552022804101e00703000103074075850601c10381c00c0c441d0495008100600e01070304000c00c4401650140b010308001c110f070810306010f844181c2046d40c6814405068800d01c3c41c0703000c2584200e912072103950354130240c0044102101c0f48151020034290302c07070303240d162419000014000c540f0b5102c0d64400802c1c1c804d03d60707004100d0408200d16000c1d040036401183d000c0350341903002600f00349241d0090010340c80100c201051015085903002040d82007907070b0883e110f980226003170300d1900c0300c2d90f03000c0180d225446003889641b500030b01088451085001c2c111040c08005030211015400304030790801090040c00c5142d4403281c81c206a601c4c1c1003240407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 878313660 1250 878312410 878312467
    0x603380907020f0d1b14070602060a0209010c0206130b0c0307030e0d0215130e01093c0f0608030d09120914060a0e031024031a06011202 60
    0x1107111648005103e100d0380b091000241564042c491082d1351000d8000707690000320b0041d0b50810001070705034000100b0808058000d01e041810302e000030382040c4000b8400c80c0d80138410301c81001075a0b44500c40341e100c03c2e01039840796500e1026400134a04000650800014200300140540319008000014401e8078001d580311210025180100030405c0ca0040f0060b52101405c0072039004005020000c11044001480007403001e80c4e40c3c214440941c00c03d0344600710036a5140c82103100c0d19589800c85140006074561101e8040c104222805488108800f00d8040356884403031070141c600c1584881e02904a900c200c03a100c030107403003010700a00f000790340c00c550301001d981c2d204c0f481e075003d411084156040c1820b8015001081024030100745c00146091081000d80124104192020b0203030350008820060003003850040091070311131407201d02c01c0240850403240010804224110b06203244480400c8428186132034040048aa040f00008903410452001400026411a019480030741103600b64 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 878314910 1250 878313660 878313679
    0x301090b091c090308091002210403060b100906030b0d050a0506061005030f0402040c120f09050606010e010c0b0405070f0b04150f1b0303021c060503070503010203040c060338 77
    0x2d1046034240243d00c001085c2030410301034541e103890608140340c5403000910441d030102d80401c40000e5040340103c4144800d0314001400c0c414002ca07401840b07a00c44c415185441c08400c004001001c6130514802c240415640700c80031101c9a94080031420b020340c03c441203484260309030600b0398840c2400d4405521841002c454100598080c00c203036803180421880007903081d0750315000d2102602d1000d03600000c21003403034417082d82c0b20303050302c0344441c0c4100e0100c3c00120880c103481c0103482c00401400c01070510100c140380140581c2d01c10300c1c0c6600c0c0c0d9480251090151075503d862032a0841031340101c4007410180708045a1016407001901c101c90814170601010544c80c102070301e4030f020005142d40010700240388140800f580b80710820030640b191074014503050007030700c0c200114186100540d0100ba00c0f4031040295103400c01c907410142c807040b4000c43c51424641c0da1814245801d1040509050301d400518400c4a8454040d08444500c0c60303c0840c0c40d0100040d00f0708000e0308010242c4100410b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 878316160 1250 878314910 878314963
    0x411040f180c0e03060f070210051612060f0b13030b090a060f06050f0402031f0b0406030b090f0402190302040f0516020d0f1d0307080a05060703110a08060301090b09 73
    0xc80f03c51031040e2019001d00541d4031070b004003032070a14000303040e0429031180d0800710700f04482c0b51107518441c2c1c5001680c0915051800d50082c0754555100c00b6a0806040440c248007444402000c0821203114000031660ba29490362001007442c01d551028101203070444c20418a81e44c00f0600030000b6101d002c0400c044051b1000c100c080f2019405220380101c02000c4905203802c0980c004e43c2c0102d010000444850304622841d101c1810781c1d000001c1007d804141003242c180c060280480d0045c0840d0000399500e000310001414480c0240040c2c4a0340e00c0394655000c104030031207200c0156401400074801180340c0c01c1240040d2a003500d03c08424402c100030800752500c08120503c003c0340310380d071b40100d01c4140c05080361100a03006c818092198440f08007081c030781d41000a40300411404003d4400c5c0302460500e81d0070310000030401c1d42414101104000141440401c6450441c82c80c00c1c03440480c0c0700c0c1070200c1d00401d21080d000b040200340105010128800040d04070300c000703070700300c08d070b00c82500702c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 878317410 1250 878316160 878316167
    0x225080301032d060e10090309080f0303190c0c060c05071a0702100b04061701090b070203040305100f0f0e06041e030e2803080c0712110411040f180c 66
    0xc1078074640e0f8491a22008001075117900302d103550240d0744003241c03104143c07919600304035403650384210007140b14a00c040140200c00c2c0300c1409143c400c00090350551406c0d400f0302846080c0180c403d800301c0d07921404c0074902401800e14448050b081901003290f82c1080c0ca028125034440c400c00c3d11440400c0c084400742d950b55026040c030039a51035001d0a4901004006840604080101554002d81b41c2401007440240b902d41c4266040f006000800c505c05581414004410b0240405045400810007800450030015000000c282201301c00512101102101001407002e400380205403810035850008240000400501450095400e4000c201e05400c80d400c00d036094581c001d021941c0621204081d1400c0c110041c480001c2407110811481307405088010506203400031100710601080b4111118001c00020014000c0d11b000894440500e0702c03090621150040b1041c40b0b19140d00903100c10341a09025240117058000804101a45500520025800c0190701a2800345408030360b0031114403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 878318660 1250 878317410 878317463
    0x2071d0903071103030405040c031e0b0a0e092d010b092e0308070b091c08040605190f06081006050d0f050f0706080105010206091f022508030103 64
    0xc4400540c60101560b540f03401048441c090907034180010301001800340c665004d115507050040d41c000411031440690000044650721502000b9844c02d00403d504d511050a0f00e000d0f40c10350f80c101100c5660310320140340391403109803400403141800710051519840d800140009844618024808100388074117004902c1021164101d2815040d1310780000415200da0041c00b5917842a4078041450320703510740d04000e5110a004882c1110340c0340400c0900e0030203200031480052000c2400e16082141f140082410b040984060002036654000c11544800301d040440c1d4042200b0041c020101194403410040c070061081da1164002c074800d0114845451007407038140c0300000c00c41144400e443e25545628145004120340070310990380f030a0101030b8100510301c0102001d07650580c0070340c1850002801c045010740f500c20158001c9903641d540390032040c01116a40b46102d40140c071602050700103541d01c032545007145003001e10042c0010030300203a5070096050300d010714031030040700c501103100414140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 878319910 1250 878318660 878318671
    0xa1a090105010f03020705071d1008120c150a0e070f12080a0c17090a05060703090e090c1503010e0108120d020904060b0d0506120307020a03120203040b0a02071d 71
    0x661000052180758000c0010b040c40c0d403118600141807800643d0780501d031036211740080545100100caa000761101114080380c0c4840100b140d96078540c900078490b07a0701d0b07401d6154103054003408504207800e48030420a9070103c06070021402440d04007000303410000d004080001015020b0400d0100b17030001109901405ca5109a4502005000e01c0e11800c120b0740041c015541000751202085010030781c40300b0a42d1a00e8401d440c2d40360303280c002108104841a20364400760150a0510541c00801d82128102c0b0480d90111080121562524071040c100701c850b40d00690300c207035441d03610304c0d5545c2c01001071410b90300b00306014041a600d0707511040c0d869044103804450345108000d641e10340f0b0860740103400d0141c4098408078440e0740324103690645070003c049d428850342c0d42d141081500d14140705003000950401016604d0802250041101c8004501000c0d0a03030148810754441984200100c074001c003c200300380b6880d1040c4080c001d40b0354103a44201003422070f04002c2c0ea521000c00c5030601d400380 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 878321160 1250 878319910 878319919
    0x105030c0a0b0f0c07030606050a0e01120212100207050601091515110a0c080c01020c01091208070516150807361e0f0e04050a022806080a1a 62
    0x651a103030100075140c2c0091440d0409203020300c032132020700c0c0042041070081d40c4a078502144642c01e103014002c0003182ca0b880b01c49a041d01e070f401040822075000040a03a00c0d010b4440302c0140c50010f004070b00d00300110b09009071052000800350103226001c14a18182c0740740c0b6800340b180d0201b03000d4417001006c0c4ae0241c40b407a12028001c0203031240c014054841481101e00507500d000d1426200c05883c60020791200340c2a82041c20701c464a581d060102a1940f2000d080200c951802c243e89a5804066102c00911001000a0440a2000030450044a0300310905140b10031522100c040351018203684101000c104c0c2c110106880740d00600002e00050b0003900050741403004105500070800740d000380f01c842040b0240002c1703034014001d10b0380c80790080c100301c60800340340c942041410058516403224030b01100100901c800250042454074526404468204652500d6910300c585400d5204001b030030400310180001c1c2c0581c2008400e403203900a56420401c1d110558902d515171050320341c4d1207910 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 878322410 1250 878321160 878321179
    0xd1d03030906061903080d05010801050604051513180f0b010605030c31060504080c04060f030b0622090308060405060306041202030d0203010b030a110a0c020f04111602090105030c 79
    0x1c44c203002400007400215410441d4903d9070325200c0c04410b5008408541c035190710340c0010f03c4885001d00529802070301c10b542c00c10661401d001c3d075028140d00d94816901c1480c565000c428084c9041e045245948807800e03562801d808946484100c04031803032404ca031015140030002400314015020b581c8201c040c03805d00740c82c003034200c4a51100c21060b0381503511401c0620a03686031141c005040f540160445444050340c8504285440b42350240c102003607845641080001d2112500490000041329804401d044464540c180047c084150061104d8803048039400503486001031500480d0505010ba1100001c0384c0307410341480300780c64044034160303015809400810300061000d00040c03808126407050300c1c10402121030810580e8000e0b80513102d40740010060004600c0c5620969000345d03401603d00780340c0000d401c0090301e101c05104000e03110301d44102070030780107840310340100009940300d41410ba560382019564050011059030181d00980c5e044002046509001074026a0a80000c000661 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 878323660 1250 878322410 878322421
    0x70e010e060409060e0303130615081e0106050d050c01031404081206030f0307050c0a050d2a0e0106031a04050c040905041e12020f0c01050f0d060b0d1d03030906 71
    0x140c480394504136941c643ea1441c80d0910141400a03501441c18004140f01e094480d0420505030703600d268900e082c0c100c468004000000c400650240300000070380090b6554490400024014002c0754081c54001c5000c00c3e42204010020480030342c4800241c0381008423200a6001c0019107808450040500e0000c0040c03040a050015020f0b81c0044002c080300d501c2c21011051a0841d00030400859265000140820070f600e014455040039140031342c1e20340c3e280312850304c0e0704081170016482c4146a5605a41d040010074a200003800903005e170f030138071000c0345d40d45007001001070030b4100b8a01c400d0309040350742c100700c0d1826000d81030280c0c0c00808128101400c0031029001001d0242045032070044a5407141903071048041c00300601405441c41e0484c250741c01030042e082000280324203030a900403003003503e243e0ba04141a650300b00004c055540d155809001d03aa0028002c5030402008900003181600d6600d0725500305030002650450400c02211502c3d013001d940b40025540c0440e2508024001039 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 878324910 1250 878323660 878323669
    0x30307050c16050f0103150b0412030e101e0507060c050a260a0f0906060303020f1203011d04080d050109021b0319031113060509010e010f140309070803040f0503070e010e06 76
    0x4020b41f10444441e41156688c4440c031220380c0180c0c050222480b00b0300c4114203154020079440b02d8100c0642d000d8510114580000301070031403c2411250b9041c0c0d02c5111500740d8031440a446c0803d9101008004100c604440038040380c04c408c800e01c00046031011240070050042d800e003001d96254090b000c205460f020131f400003070142c101283c01c0050780e81030f1010201d202c0d4050b000041d8002d030013405905030519003441c24512a600c40c1c02801000f040100f0211107905040b109644110300c09103440c1e2260300d444072681c40f845014004c09400c140c004242c2c101540d00501c000c09030303134114400c290340d402006034590061124140e031107141121400395017802900280100d49c11800c402d8680b14450008142c0d11026400c2280080d0000c82c83c1032443d600102c402018020900b081451201c3d0b4440051102d01c41c94a6402c4442000c0007144190744104a0b01c1d010b09402c0d41607903200ca86454031201158100e1003070034400d02c1079080000707110f10364170f064505981d800300d0101c0c2159141420700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 878326160 1250 878324910 878324921
    0x5070b0a0b0301020f120f07080f161125050a030302100507020106120c0e0f0c0a0e0a09090302030d1b020d0309030e13050f06041e0902040608030307050c16050f0103 73
    0x10342c15540800c610000781c00d040c0e0080002080841207030200e0704000d80008902c4500600c650184000001400b4800a480424582c05a030b90003c6454a82100c0e500f103413030000e00740c3c4da508170b031052a0355014100481686400d008ae03450348003418680c0e0325000c028107000188009009a0890501580561481c1c2c0100358003000c2030001081159540da80a1080d40f000003040d100c2100042062207202c1c1c0c040035040d0440004060341c10306061039980c5c00d0462003410811000d1100c01030508a0545824052b00010048001c003006552294213010b9181c0c0e0004e210044c480385080e02c0d80c1911101c25007480803210310f41d801001c001c40b8003d0160020860300a0076810320280c0d400d030704c00941c1c80701003880c40400b19003004070709410100b4048081c050007510083c0700da0f08112444e0f1880300341800314440341c08644030100e003442e6980003240040c103083e0820003490100004111401d074014004200c0a1350100458105040c60500e00c0c0c1e90402c107001d5241d0018500740703c00300d150300c130380c201 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 878327410 1250 878326160 878326181
    0xc0f06090108130f05030a020c0a030b010e040309091a0301050f071e02150a0c0f020d020d120e10020a0809070501140d0b1f020d0e0604270507090f0605070b0a 70
    0x40201c00029038444d0004880e8a040071542c0354000206104c1c0a83d06220b2003010407815942410703514203681d01c400c40a0300501544039416405030001d02498810400c190043c15448000c000390380034000c5a600c0340a2188140f400f030360a1002140d607101c5490042c41c46041c10303688004444200030303204041c00303001c0c200c040c045228a9010b221029070702c080560103104070344400191a0110040508608001460b500039500b008071446031b425004102101000b4407480c01c801000345800502008080c000c8840340188910040040c004d040d030341c000c10010034a034039a00495170b00c00d088075540d81d6050040f60b0002c2c0d820300181080340000c10190170010105000840c00c4511100070480b2800f080182030080c900044448521030380500c084c010640c500c0c42d140c9410420710011031082e03c191f11401c00c0c2908074807180c180310f2120f030528010032100d030b071001c0c002810200b0000b0074840a038007480c400c2c0c1041c03100002d505801881111360329a4030042e0440e403a40c82c100450300402201d01c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 878328660 1250 878327410 878327431
    0x406050d0b011412010c0c141f200706050f1807051e09070c200f0f040915150e040b0a05180a0507090c030506131a040615020c0f06090108 61
    0x60240d0089801c0c011109201d8055403444c0b031010441c2004070141c400e644001441d17402100140750600c21040ea44444903040c149c001c10036030004000b0306002d80183d110f034002508003080500801c10213400550080c10400d81c00d0046480d00324607119485151409099581e002210400050400001081c8003a102819841c3e400c2c0d50000415040a022604000010360900d4564200304101300c451100181c0f05410b218002c48820118100c490070301407e5104514000848030681e41d1604040c1ca4a40e00c480034480050303817400380e1000b41c4440c00c1c03d508040c00801c8041103415411984911075504203007460016110400c403080200030282c40400100c42d6504001550750003041101c03601489400100b4580b0300e0301004204550103145c6200800d0b040005100c507940c1c075444040740150122030f0010f01a00104092150b00100189840c4c0050a088001800400d100c4409588076496000d0710719050f80c410400160034010944207078480f000384444074555100d2110703650310580700003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 878329910 1250 878328660 878328679
    0x60a050c040b04032105040602120d0e0111030a0f0c090b28051b0105090a1b0e0406020a020d08100b0703050721110607020d080c070c090b0406050d0b0114 68
    0x4056002d950140e08180c640c0000c00418450a4070807640c404007407010740c176285051a04003003009444000f0031b88401d01f00304000c00c0361701c81780c5041c2d884044103008030402004030703c02d50151300500303030400c0752304c4c04090b8030b855401000c001190042010f510f010340e542684007814030b0580603003504a00500700005040107941d001e0130340007515407840508191552504c80000c06c10303104030000718a16088499040c0000d0110001c000a846000107a0201209200c1401d02084000c44400c0341c0c0082c1003a800507007400103201035a402800304912641c01c0e510f5045080905035900700040d00c0800851040900030010503080030041c056551091030070320316008180d110480519007500804110079810091065103682040c0f07a0608450648080e00175440c10030400f03510754070081411030070720001000040340080400100c0f180a5032000c0303140d80f000c1d2100b840e64002d22081d21001e029520701103000c40e05141c0020300741e40d43c030b51001c6040604ea00381407500f00c4005019900c55080010b11 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 878331160 1250 878329910 878329919
    0x6160503010530030d060b0415140c010513021f0207050609010207180e150405030a1d190f0803180f03071205030706051509040210112506020102040503060a050c04 72
    0x42505400c0f441d44200110345813a0782081140031255183e000c0d0078801000c02041140c80115210702034a00b510307040002a05030300611001c0070740300b0010b074074155520707040030801a001d4015261a644e8025200c0000d000c1108803090340d00c0e00b0400c907080150b80803c40c104106c0c03401e00001c03e004801031061310a4507550751078400d10407800b0142c54034015100c4114520583d4100301005441c240f00900d08070b9428203841e010344a20905981104106802004211100c070070715400d44103200c098100704e62600450f2039030401030601e004403030310401858070004030181c000068444440e14690304254a456020400c41c0a4141c0c2c1c018a40600909400294400001d2010010107000e14055540c8008a1411004540005140904e0710070400c0d00482241c440d030084030b42c030070380c162004261400828000e440401e8122540074052042d240d0a01101c078041c1d50310003031340030301d08841c9034460b0f15030405234242d004600903143c1650140002650740c1540e80c10942d00850204249071406031034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 878332410 1250 878331160 878331229
    0xb07050f0d0b0f0303030408041a2b0524010c2112060e0709090c022a0a0503060105150a030b04060f060806150a051c05010f08061605030105 62
    0xa20540e1071242c0d580555003140c0c144034405440b01d11044000e9895450155900c0e23226020318003a100103c012003480101e07c2c591141143c020500c2c00d1480004000007907141a058015295034000c0c00b400d060100740c00346003109460322060043d14030f1085208401c0c00444031003c4820302031b22850030200011941080c49101b60500c008030f47d650048050003604001c1c00d0b41e034690b03c07080c1421201d90800c40c1080d4400d090703c060781c80c02c81c1d001c143c5000c800f03805c81c5024450409024081d1000b41c3c80d02c0c1d05c01e504062403c1200b41520201e0259540703070100f40d210341e401d204680d00021843d4404149107055001000d0109490800240180c400d201040440381c0ca500b24194915070b46c00b0900290390007136400d542c0608102d40c5a01010700d44074498885004a50942080c400003050740110720780003e03210504904440c008020315a904c00c1c08440040441c40758800740e0154501207401d520546001c20310040807a10b42a196928000a0080c0781c00000c040d501012032060080715041e24 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 878333660 1250 878332410 878332417
    0x60f01120501060807110c060301060f020312240901031106070c0e0412121509022a030d0c05130e040c0503100b01020123060d060e1f05060f0d0b07050f 67
    0x3c0c940d80c40f031040c90201405801c2015408031a8490741c00700b449440e26598540840341983e2541c47c244a2540e1058000e07469400703021001c140c8404000108118460004400f29012003002c00610300e5082003414410507103420302003c1d00300500f411403502142003030001032145911034800c59503c02d549291015100c007055070f045411001d41c0350754030b0402d07a2000f04110801c1d0400c3c4208525501d10103030f58004080351080c0c0d2040b94000c142e0079001c01c0a034281140801c061045280b0443c24a8280d5849038403001a01800528080725100c007188180c041c0c4081d1045510200105410522281c1425000800494145c880600081407688043c000000102d00d99100855244098070029080d17542c1003c0e040d000210144c409002d0428003442aa0170000960b8005d081d4121070410300081d00a001944155119000491080402c80b032000c005540343c20f03400300000d07203401080112405031b207007103079a000c5085e006038804902140c0805c1d40228240c24514a800c6151070060260b41 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 878334910 1250 878333660 878333669
    0xf030c10030504020102010f0c0f14090d0302030d050115050d0f110c0319180b030a110a0503010e10050f0919051e0c07051203070c0c26010b0108060f01120501 70
    0xd46070b5040c807003107503024091213009107040380c401d014100ca2400700901c200300181e822020001000210849420f412b0115022024090104004044982400703556903020901030000c1528110000410100c0340001440f012015602e0358a046030b0510190058100316420480c056550b5038901c01040105004040e4404941c0246480b101e80080c0d49074010040301601c424403002405c0c1c6c404a103400308019040e00d440742c8500781c07607072583c8090030020812991100820600040c2105002d0b8008019504960301380018140c02e50710030091420314176481c440c0c160401540140f100b0140703881041c15a0150700407004030720740e00e4084028415118280c504080510401885a104800d06800f55600001c50f00c0382e9481d2805540c0d039643e4407201c240551000300000b0000c02c0c1d600d44540c0d400300140b508200101070f0113032603460003001c0174000c00c549012059400320045000106001c0c0717080c0c145050311120001d6459005101d400003455092504010a010721071003407000500c942c03800380 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 878336160 1250 878334910 878334917
    0x90f0a080f1c140709080d110a0510060e01140d0209040501021e0d06060302090d020d0201020f030406030507031a01020d050306060f13031b12033b101107050f030c10 73
    0x55040d590081078000043c2c03100c030402c05e443d581400303140da0000c3e05400380074039071800352001c0f801884100c0c1496200000208140201c82d042d20051b0307080d0700400c098520144100555907a148046e50f480b8860201c0f203904010651200c5015243c51031000d58820b0107040003502c0c0c10010b01c440c4512070994281c4443c0400c1c04240c42c03040427198441d0a000d0a101c4c01c1c01c42c80c00007000700181c006c40151100a100780c080e030f074400c004c591080c0070000e00340300804101c9480b0380d102d12014010380b000722a00d1000914142c0120f4a01d0300041585072008010707000703082e80312100c0c90102c442390310042420740c00200810140808155520081080710b50742c813802c2c0e12090462900b40d048600c14810900801040c1c8001d1010300603249018003090340c18180104041880340a1451044601440309030a101003190949030705c40c0704130000ea095034109d618142510400b1403d031a400441450035610350310204060120781442c0c1c129404010b40182202c10325280c8000007071041c0781c0203c211000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 878337410 1250 878336160 878336171
    0x2120703210c030608150a091e0b0403020c0f091f233a030e04090f020a0504200d0230011d060409060605040c0e09090f0a080f1c 57
    0x40b0359043c0308120143c0000d0000d8030940c0308a60621002480203452012074941d80c002410070003ea40340c880389420310f0b450001007079101504100440580807130f01940540a0641c080f0440d150070001e141e40c07508000d10100c110f80742d0740240840000c00300c0640b8641481e803403011440b021044000c0c203a4100c0181380701d10140d403071028801680394102500500b141d9000300410411060942402460140c0c0c0351846101c1250800f01c498001490140350072503c3c3c502d0300006c0c40591104503c10718001d0b00d090b00c00075a0340c410300048503441600110303000ca445803040314403040b840c001c141e0300703200d0701c000350821014020404007007105000f42e54001049501c054154030392505401c1c0141140d4020005903c020420100c041000808003486241c0c0d0720880c80070403500c0d910080103840098400c0015070f000400c0034001c008040402c901c41c00e50500040c10303490000840740746007071500b400307424001c0d5541e4030461181c00014006640c0c0c85e041c441034040c83c0f0fa01a040e4a00010310802107803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 878338660 1250 878337410 878337431
    0x12010e010b06180d0c120f14060f0117120c030a0f0905010503010b1c0c1d0409020d080913110d1d12130909080307031b0212070321 58
    0x21110450186809002c0c140160162104412200e81418405488512201e03c4c245020710702c59500e50050303d00105090302c1e51040c88600b0441414107071007a40c1e08a00e401c600e03100b01d5600e010840d900c0b180180c4070001800040c0d0074400c2d41c0d2901c900c60048400484a4100035121508135032030083c0c1c190b10104044500326404031840441080e9400c03c00c200b17a003004002011803005005101d020346000459005262110007021a25400b040c000c0110780c640302402001525013507402c00d03030888a0180707400304d407410740b150080b00c1d94001c0004040440603074509089410a1070034a510010088180405080c80d0048011a04003031311201c1c1c0e0303441e440070590101c0301210041e1500384130b10241d0641c802e6000444c05d5145140045680d1680ca242ca0303010541003451300a08840b030308010100080100050195000c1d183c0c1c1d480a000130707600044003504420840100c0c0005a210f00e20a5203a500c52b0300003041040d000740ba004201d07006160080ca8000c00c00e2143d100c501c0d03030b20280c910 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 878339910 1250 878338660 878338663
    0xe0a02061c0b0a0810051522061e1202040b0303030f01030308011203051b030915030402130507090605030702071a0d050c040f0b0927040506061807030c02010b12010e 73
    0x316421001c41d01000b243d410311010036036070003000c1101c0c140595240040b82514011504000601e08008c0141400040300040c0c00700201c103a03d03003020705a00342900860309101400c0243e18580d41c1980125906144c40001e0b1983c03181da22041c0d03040b50703588041607250b803400c2c8001c501c6101201c0c514074182d45189402000d50360141e10082c2c0106c9508031a00c0081d60000481d1f11540c2c08005881c046000784103240e04502c60104a01c1d8000c0b5031480082ea1444540d01851003a4022a081807015020411201c20748004681800c0021041c00d0305008450040014580046a500c105c90001c1e490743c20b01300c1c1d02050010500002d0700702003018402c0130130138002c103548917860300300c664201403501030000010301e20780c09120422880403540040544883d120710340200b6145440030054440d0120f40c80c80080d0a58040d102400341100040940c188564020f540c1880c0c2c64480320169140b0900720014202c8101c82811552509544a550f0b07540b003142110403076482d800011400005900705 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 878341160 1250 878339910 878339921
    0x40f0909030e01260118060909080426010504060501180b01020c011209051903170f070804020d06110901170402030606061b010221010801020702130e0a02061c 70
    0x1648003800c05940800207039000030700c880102028202420f11110001c0100d65200044aa5242c0060800000502e0f1003c030750140e0710360040e0307903800c2100030340342c0300c0c203030107840c401007019010140810040111201c00700f201c0a019607800d0201800d41d50400056094850a030740035144981c4850040c8031181112045000c0b801c80d00004111766250800081e4480e441d0343c00035810b0106201c0d40301c164250030b400c10040542d004043d102d00102d04415190310324252841900010642e0416100700100001070324001c001c8000b10414550399004110303081180280220f81010803500c2d80c0c1c000415500500c04942c0410321358030340342c2340c0d01e038001441c10840d100580b09814101c0144400b503100402d2b10b50b040781d800d80b4465a0f4030a1000301c003070380706809400f40060350700c0000d0590035203e00e800d14041e9031118002c02401c0d66030700c4114a00345c0c002c560010f0f40c0000704841500003402d02d03a2001c642c8105240c11760f1090300160700041c403180c1000d0121890403d0b104280001c85019100d20b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 878342410 1250 878341160 878341169
    0x709090213021603110118060921050d05060111060f010513111c0920100f0815010306080a0f0b0610020307030f09031e050c040509030702040926040f 66
    0x114100681d801c0ba861500398441805000c2c0100000da180f501c9a087d0000b107000121240e8a814004071417501c00c0040803500e1095440d103c46035610003c41c41040d411551408440d03440d02c0c14a081019180c00419024100300e0601c0090f82c42c00c03002041c1400110f1048481c1c642d20380d065890041407001d4a0240b00c011410986000e03009510541140305a030201003206e50141d0095002c894208001c01c01e80c0c0d0081c002a0800e00f000b074000d02600c0038a450080152005505112200d0040e00c01c01400c618100214400000055011441900d6145108030514010400540d41c050417400c011943d0b10984001e45160303034070b4041c0174060b4000340d000fa034181c1c0c0580c401c001c441d000a4881c00383c040c001f420000342242d050310062203221144042c40c0c00840c8010980e00184a10083c1c41c6003400407142030058261004c4145010b206a9105120650186140404581c00c10000342540312080351040745a100003804102c6802582d807085245500c2540c3d11410403101501014a5601 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 878343660 1250 878342410 878342449
    0x1050a0e0f1005060604030204140108102a20010b04060b040b030712020712080a05090a02010f11010f0510030b0903070f080304051009061a1804080307050c07090902 73
    0x180181c20a40c0000e889030040105440042c0d182c80d158002420340c4039592001c3d40c040d04003220440c0040d0032912050480d91640c044901c40c0200d039490ba406d071080c00f40c00300070070b0460700d50080d40d0180000e5078101840c0306142200e0410f5040c600c184420007090030504180e9036070540043c45080c0351040001a001603609142414a4040c44403110702c4002c0083e01040f0054100702c00b1000e40e90199044190b10111b550070b15403d001c8000e10103541101c47c00001800c0001044001c0030100e41d40310099010382d551080c181000303005981e202042da01201071503685e6061503400203800c0c03207164001c0345050610380c555407460421455007079002d408440b15030010000c035000038001d1030700058090b40c8a6441516992542080782c1440161003000080d1400d0074022810085603500c2201e054000c0c08011103080c0040c014071045052501900d03a00c220000041004907014001071a4420810300d00540380903841c210250401141d5480100c1564071000d40c4011450916480c801944102c034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 878344910 1250 878343660 878343673
    0x2041a101806050a0c0b0f0a1a01020d05090a050a0e09210403020409030e03060a1d0a0201080f04050f070621020f0d0908090406031a0c09010c2a0801050a0e 69
    0x100a4050a0031601c19041481000525a2400b1780181841404c482c0c00008100003858014507040c0409011510f01c455140741c1042d020840c40340c00300f09209890181c2c020300c1d5580100005440607405080c2e920b80c0414050b1000425681e005d000c5d90140841000c48100c42c241240720901c0d001e01c081d030b206050070151b40603404104100c01601d0840340c0441d03000c00d440f045d500f019518108491134150f014002e100411002d4010f98200d03010952892903054568100070500c030303031a81c109481c000e000a0000021070340351b1002d600101e0b0401c0c09481a940075409032241d051500c465a0f201002084404c00d6492013407042d0b030224818038084035825445d001c041d11544001e0300c035104140708481e5a840800c007d1085032419a03041400140007088101c0e1281490a411640107030505140384020000900450801e002d4407203c00c0c0c10f03110311141c0c40503552045d182000d200394103000f070f806a0079041c4000400402d04001081ea2100004040c10b0032528142030300c2c0c01090402d43e650010703 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 878346160 1250 878344910 878344937
    0x515011d01031409030304050715210204050301020c0d080f04150903020c0405010b041404150e042a0602011503050d03020a11011103191a0d0f02041a10 67
    0x3802055100c2918051008480d44a401a0010055120b42d0012451110108458100000002d40c05031340210f080b2403c0958401c1c070101030001c0070391000f0000d6030401420414172503401c2c019090507810400541000e0301c0e42c1c00b03e400ca070801c1c403126582d0b5004005810301d03545c0144030303242c120040c0d2100007480d2800c0c1e00d0b001011303106881e200820640c2c2d9070044040c03610034001004c0b4072a00410902c40d5503502c240c5d420030743d0068001c4c611100145403030b2051500d480c0c4601c200450700010b02c074020a00e000307901284410003d00a807442d852400d0b607030381045900c40310f0403040b04c000f4a00b200d101c1d06084009084070b1a00707500c00421084010240b003c600009200c070701da000f26180260385da1101c010203c407514900710070040c043d800c083c0000d503002c0840c0b0180d1302c100c85616005007004014054031007030790441c2071921900c8a108030103451505010001500050140381d5420200b16980e0114085400c004291012200391078810421450300e040d00c141c020f40d451619084840c1079 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 878347410 1250 878346160 878346167
    0x1e040308130501091704060908010510050d02060d020a03050406050105120c0609010207180f051b0f130314060114031f05041103070b030106142104141f051501 70
    0x5802007805414404150041007425002441d038668410b0501031426003030290301035640c005009800c0407804850000c9410b80c414416144205a0070900d043d49501d400d0602c6168404030030140e030002e41c10403400761003d5403400100000030890f600060b040c9403505200d011940b0607044a03100e04000602c0060758240010240c03902c610803203d40340e582a040006038984a287e5001000542d10040c451400742c025034003442404c401100d003400f807540c032a2074441410b04408026501c03e0b07000e000c50410b0420203009414039040405206507000e840703032600c0300130300c80070742042100354000c600601001c8200701c441d1461420036002840c41050740c00d918482c0240030024160705568503000a414010101d034111000000038003540e604544500030054141d00c00d00030000403031007840d00700540c0000013045442c07030f52010b007607207090080c5c401c0002240f10018105544002c6018411540603000b44072026a86c030916507600c0312030b000c046c0b05c10160354000f0318210402507880d5244420785d81 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 878348660 1250 878347410 878347427
    0x309010f0309050d2d02030702130c0801060c03050f04080102090a0b0414060310151205010621051312020c13020906040506030702031201031208060306011a0d0905151e0403 76
    0xca05141038144c025600b00e1416120310071780b00002a68198040079115008002001d04600954039803206a00d150050f505035044440132800103404640100a5984a81d20762041203102c0d14142d80383c2998482c9108480d00907401050fa5a54002010b01482c5403090090001741021a043d03402c0c01d1a00745102d03428551440078a0044c0c10000003d18021031300e803994006002103020903484001c1e5007000614404c0054564040705182500104144d8000c90140322001d80071200024070a03054440000500b078080d0490400d8a194030061000800b0b0342400b890300320096004002c08440c80041012b04c103014040f049565204124003140d540f00c903021281502d00c19107040741d982d20b0307010742249184281d0040f00c0c006003804001008202010984560501240d5500c8103a0717242c18041540b5aa0300388146010042c9500244a61041071006030140c41c03901d0300002101c0d04c0d2602d50f14100301c03207521100404041c040802810b03000c0c2ca880b5480342e43c00c0444005051038a0794002c0d14810 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 878349910 1250 878348660 878348683
    0xc0905030d08360d05040e09060103020904140f1c090f03020a03030804080f1303030e04050709061d03070305060609390f0a08040203011a030a02060310030b01080309010f030905 78
    0x20701e034581030840c4000a9468103040007280111100800341c002e00514940081c001c441e020a220800300703606048c0028203606803a0024100016070b19150361f1900c0b036480020040085001d420580100d10300244a140f682c0e800d141d81c2c00c0004068618020000032290700501c00702820b500f000d1003d2389400a0340000c1da60305080940300b076103c0f41028440307070080c000807041c0288006400710100d109841d103403040780d200c3e03202e40500c5a02c3c002001f041e26401c0340c00c4400039120f66410482d1500c18604051484240ea0041d140078085a001c80d080512540003a14039511250a00c07249040c031800080c0d1110100c9803502d00383ea111002540410a1303605c14407041c202c8810140d4100c4034000803290084085608240e032001d1180380a02014000c0706c06a100e5443c0031089181ca20706000d880b1601c0390014050103031801c6503420061182c002926540032619010804000036526604460180044400542c0ca0b84549000140a0501c401b940400c00d03041000210019800091442010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 878351160 1250 878349910 878349961
    0x602071208030a06170a02090a180219090f05160903050d03050a020d0f0e010c1d0108090a021221120a02090d0b070e040b100c0b07050d0c0905030d08 66
    0x94481e603c11401601c12900800c2d981507101140701680c2d071000840400e41c0d0710a07501ca020701c2d43c030050301600708c1c0d10b00300d42c18070301c0c04052000000501d80a04001201803000c42400c0106407034010074402c40f200071141704502c5589074140512500c9040901c132142c00786250078942d09042d90b0301d058450b4222098241030603256004910a90481d405407840000160010440e901e60100c002d005080908110402c65280c00c0c5a809140c0c80764485400d010f0000d64004011840b10f4011035180d0030040c0300441900440c5044001a0b507410f9030381d170070214003c000704044d8402145000444401001c40307200c40000700007035001c0c10921a03c00d58801110140141c940d21030101103540c09880340f0000b08211900401c2110440c0c10400c0c0c4500c0701c4041d103041103035180c4071040c0440c41340d81c441032a02140e884a000000243c2143d4980c5e4003403c41d04e0300070305210791903141600366100c0ea00d04801091081c00207001d141420000c0000d981440c0c0b50010060a19690180d90100c0070301680004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 878352410 1250 878351160 878351167
    0x20d1d040f1806110711090a09051903080a11040506130b0d060819020d02040b1225230907091a09090c0304020901210c120201031503080f031b0a0c05070602071208 72
    0x310354043d800301409542020a072800cbe031608000d102000036100808401103500c84d4040380c0505500d11500e00503ca41026203403606040c10304201d259040301c00004400381c603e20010848201e0341d0080c04a8030034080001c40d0150030800d4580c1003811030700400c0580c650003550100940d454940052109405031000a48500c0321000304040b65180ca044040034818ac0d010708a5000c181d401c2820610012140864003549601401100041001d0066600820b002401d0168545120966000103141c02c160f200389070740e0210322818000080c840d456880c0003042049a500b01215050707805444450000c0c61494071f07600140a50030b040c020380c1c049050490041c0c0360134003144260165a60018000080207540d150b15520b00c0355045000c1f80028113141c2690f00314040d01000c1d106490303000c80000d080c002100c0c5504655000100317200d204045081240070300308074a4005191406059660b80801c04d070341d0074050b01e070460603408101198400c0104100d201e114020b10b15200e9446543c1c91394 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 878353660 1250 878352410 878352421
    0x11b0f020d080310031b030201020a061a131a0a03120c110a0e0612060f1f030c080d080903030c04050d02030a170703020d020d1d040f180611071109 65
    0x10011804000c02d4460300000f80540840c00c0310380482180d124607040503444200154082d0703240d1447c0b1009016901099500001800e00d8002030780c03138955140210b015420810010b80402e01c1ea01c0c209040c0e5640714400c0e0041840143c01421000f4161000b2540614580c2c40078041020705800038100825a03100004101040c000c895120000501030300d0210f0715400c0c0c100403c04251555403140e003180807080d81d4101c021403e2882900300c411000c0d125940c801008085202c40b0b0000c900146401401100040400001c6070151040b01c005081c0359011710f002400c11000a00600c0d51603006008006003442ca020031a02664420395a4a4200c1c1040c800f103440c204e00d80100808a10084401803012030b681009415181d01030303800c9030903d000c41d40043c2e0f203500428203c0c0e030000d0300400030a80e0b0685c50307920000008402900010b10f010701c14507400d003103c03c0e02104001d046100c2000364240f0a6500501541c5032106040d0380c81e1000550303034400c0d803180c03046080d0f014000d00c0300090b6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 878354910 1250 878353660 878353669
    0x103050c091215090c04050a09030f0f050702220b010905060327071215051005013002030601020c06030609040b10080105090c0109081f0f0b1f030b011b0f02 69
    0x10422000c803a420780303c509003010419110400034134964040c91038800003c2541205004007000207406440707904403102d01c0c0c031040307801000005c0a8402c1c000104003680050319519005225070000c04806115040111300d50005d403140924050704102c100442405039549220890f0742090501000b02d080c030b2600c0d840c0d070141e44000d8903c40c0907070159000004001501e44000307403840d0f1141180c0034810a80f1204a4102c4105444103012004180028402035000e0358010400d1a0221900400a102d50494011007400305131580071003a004818094a540c0401103158040d1044815609514001c1c0c0070402104004102405100e11040815103a20140100e280500858002030010703150008109984031190400c1030b0024490400024540e040480e04451507141c0c00e07015042101144583c601400110a82c0c9104640c1d40e0b814500565900c0d20b0603003103110507003030000001c0102a02504599a000140c1c1c14494014610300084808000740c96005511200c41c40a10070303c0e00119 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 878356160 1250 878354910 878354923
    0x120f0621030807050f0304020103050604020d1b09080d21021603021b090f0f07050903010e061006020105010b03180c0d140c01050a05091c080a120b0103050c0912 71
    0x91024031091448003015418296945015000b51915049511018404c899500c64880480c0800b41c040c008200158800e80043e904110003d10150400b03808122400403203191030809607031401c6140d40b0000454000300c401004200e5039001d00b2110200c0c2c000900420b180e4104a880300c1c03da41d032002c240729000d82c1516541c0401c00c0340c3d0b0b4560f18087c40c029617203003034580c10002c07140226141350801e86807800303d4074880c880740109042c1d0360b107412003010b41641014140c0c0052080038011209262000d100d40301c42c0403011001071255040007401d01104d12055008001103904110050200842050403690400c1450b4a4081c6440e4405a02030424460f00c0c0c0199024000c1900b09042c004e4030060f034040f900c02d45050b950005d00c4203005498611400360108003050044c0444a00c2d8548140640b1aa00da500d04880d809107581d50307060001da2080340020302184000040a402c51307018403580a088a0a0904100340e003441c208404917406088480c6105060960800d00c1c0c904060161 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 878357410 1250 878356160 878356169
    0xa0c05030c150132040c091a0a030e032503030e01060605090315010608010501030b030a020301090b090f0a1703040302160803091005030c0706091e030302040e0f040201120f06 77
    0x81ea60012980009100d001d41d080c8960f0443d5110309680b0000e6000c41e104c00020031640c4c403a030000310380d4484203000c080c01196446000f400500000000c4003481003400c40602400808a41c0e1f44000350030000d0704441003401178200075072040c8081042511079183c01840e50995100030b40813070303100d403404901901c0c01100c0e0030415428940c002a2558006000d0030070281c045040c2d44000b80e0304030198601c0b000900ca5140059071807401080300b54002d80c00540e80c0c000c081c0039240e400d0800d40209003074540384402100d80f540340302b0410a424800b40148003c3c640c820740a45441215611408034120b50066100101400040403c0416000300103140c00b603041072000311100b40da980d83c440d4507070f0010b00c90345014a03031207a101664244500100d034400c500e010819400c1c403c05449aa0040c008044111140c0c130207490021300340c155030070175500b0b024441d40d8050780d1241082c013220807007400a0030003802c4c0c002d000140b00060303800060108280c03c02100004149500b00701c9600a090190310 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 878358660 1250 878357410 878357413
    0x708070c0609150c050c0103020c010f091b0e0f0609151207030201090902040506190201090b13051b060d0b031e0303091204030f0305030a02040f18060e0c0a0c05030c 73
    0xc0019050350881880740032111020755081220b60741e140103407050340b000b00c0018003a80200300304402c1d940c002c0d4040d240074039418000040c01c3c0c0040006004903010080141d80b0a2220000030015150102000c00a0664240c52142a080042420807e40130180a05100e4010f0100080006922200898030418018032844002181e00c032110f4a407419070006030300291009602056031400c40c001c481c01c030380300507120501c1d1404451000c0e214070f5070410014119526100f45401040d08103503072764016030040807401c4507000f50389031071450300038005c0051141d42c502c002812100e40c2c07104d054480710501c5040100303002043d0400a8200000008900e050390b40f801d1403000a8800040618407520080c0b0403039800c0c0b043c00b40c0320040740c0120300c80180781e00246138003080060301c244003950f000b449881c1e02504242c4c175015080845006600079110000c018a40114807541038080c1000502284441e04104e081c2000c22941d20311420b952070051000103580c1004000b07040044902e802c45110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 878359910 1250 878358660 878358683
    0x60903030c0f120305180c0a0303080a151e08150403111203090a020f04050f0c0705070b030a020702090f0103200a0801020315030d020d0c1202010e0706020105061504050f0402070807 80
    0x10060f00808007130f1440980004400800203007040001060b00c00710100501464440d4552ba80494103288000d00201100741c5441e889550455036400d003c0183c15603450800c00c41f15424039084440d410340d84580c2c81c690003148001c0b015075440503410f420a40503d4049004690034006601e00703000407006072900400001004290400441c070780c07030030510803511079290041c004100015500300341e44500101c5150400304816101c5c04000f450101d204d0b000b40d1340030701d50f6000c6141d0781d500203e6601003000c3e00003803504114a0140c144a620030031420300d085c12541151079240400c80700d00e0703080c2484090005d80180f150307216040c440041c114040255981d05d40095164494658041c1d100d01030310644030600f88090011072070200c03540140d0b90f111502a41c0d91101c0107000c0c0000702c801c1c159560f440004034900d030700340003d001a09643c5c001140c1ea051000c1400321020a9030344610790504240820b000560f10544000340c208022180544c07102494241f071000d510600400910711403c51 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 878361160 1250 878359910 878359943
    0x70803011802280914060d09031709060f0106050313020418051b0906030a0302030a031505281509031115031303080c160209090709020a02160f060903030c0f 69
    0x3c07034801500074040d590807441e6070341c4641d5904400d41d2540e201c0c0c1c1c040c4060000b4442e41c00713544e200d10000c90080c54006c075648001c0c0c03010200b071102502c081c0c2254100f80208200c0199010750b140c01802075150141c0f540c5840074461400220002000f841980c07689445115041c00840c400d060756089000c3d203100e038403009060030098040f1560705000f000001d002800d240f80c04107202009a815401075860b012001c141240100300751199803030112103840c4d0105160b2110038500001d00030180d00d0001e05083d9000785801d441050388014900c0308256000d1101d10341c009088022254054072804c0024040da0008041d0300c003080d0b400d01110800310801007080e441d10340402e182303402512481003944800065800c0d1b1310601c445405001740082040c0014201880b526500610940c20340300b50070b131186291002c0e684190380150060340461810001841c604051000406801008016462404801505003070380c621015090214000c0c242c6c052040419111800c2544451042c4110642 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 878362410 1250 878361160 878361217
    0x111210d0f11070807021807020a02132304140a15050f061c0302070504110a031107051e0319050a0e0d02130b120303131502070803011802 61
    0x840038504034a040c00c050420505461181280940c210342209180000d19100d10190380c0c003000c2c00703d80100450001c9402450f0004142d40202d0060f8090420801d45004010044044c5140007482500d80030854114104500d10009511052085800c4980da60b08109001c80311340001000c403406070741303424010010000f81c403061102c00c0325010402c5444085200c00c050404546040d04817038201d8840e10410307000d031095020903101c3d104642c20341c2e0301c401c0840c040e589404400510854081203d07200f16416000e40c01e05070306029030b01800c04200c1d841c0c1d29910218000104021030311045030489040042c41100c04654840854881c2c20311065002882a8000302c15640010140003c0301d0007850584040d000854008006036040340480c3d01401c0103002d038100c0c05500084014052000000500145108180c0445032000e0203c030f90419542000210000001241c810060390b030010320381c9803e43c3d05440d41845480b1000c0100f52401c8024403038079a030302c100c0290004043e8032400d030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 878363660 1250 878362410 878362417
    0x714150705070b04032d110f0a17010e010b0907081b0f070c15021e011401030b18120414010c0f0c08010f0204230609100201060812030403020606011121 67
    0x103d00543d106404000d21807422810b4204150184242c9a1b11041c0c040b52088000d4084400010050306c030f10380024001480504050b40302c00c0d01d030345c2c070391200900c001400e124600400700d07554000c1c0b24044900e000901c00400042c000c0040c480020040b5010040c0c0d50343c510480306c90390044a40d12038080034087c5098216100c00c50300a01020808111045413039401d99003650241c00401445514011844d00042c0d000c01c0c2c1d5540d50340e591400310181072940b07030480c000c5000305030040d210b003069270a03c04184443e02c500032003540b140c400040095110002c0754200c40102c080728010380304c0540102c9014a00302409071001084003982000e005610300e403a000c41d02c851008004041030074140c0d505038060341c451060300400c6401041310010b201c0e5401609a68003d0000d40341c038070500c001803030440317115074140c0060f0340d603040034003040318204001c0000003080c8003203038103516050390000d5503510028800c070f040001800c2a048051010800a038080840701d80c28007242c60005c00e801000d42 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 878364910 1250 878363660 878363663
    0x412031206060c0f0204240b07021302040f090902220e070e0c1c02070816030e09011809140f0f06060d0b01061d031c0e030714150705070b0403 63
    0x510345400003646070300600c01035542c154007107a04c0030404c03415000c01004160a002d01401c0b18086401001814031140e41240034203040152640c8074001401030002006a1801c420f0715a841004248880c10b240300200003114001280401c03503904030310200b048880d030764040f13801884910945000d904802d40044c40d042101008403032601d559501c1800150f54240d41c00352044104120400f421403101600404e20740c0891000f40c40c2c4042d903510a4069404843c040c403030030718110411810190700055013540400c007141c41404c55410300e0809800b81217401c54252505540d0703201e0710b007049200780e40c10035101c07000f005581032801d443d21030903110b10f4449124a190301404c00040d5140ca06521080107040c3c220074602a946e00700300c0161503681000340e40c58020359401010b00761030ba80c200011621003414144525407905050b80c090080449040000d119170400441440304020340c008002046604840384219a1701030900540c061042c49405800c1c1e028600c03020904400400080080303a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 878366160 1250 878364910 878364947
    0xb0703030204051305010e06060a022119020d0e040c18080c01020d02010e0d110a0f030e0103050702030703020a030302030c070209010305252301110d080121050c1302041203 76
    0x4281c0c03041d1038040705c60901582113015008004140b131810804044d0001002a0044036512040b45807081083c030015030003100c1d0140c000481107411440c1b003141d140c88407154001001001c0e035009018050008105d04240200e80d21321096804070711900b030540741440119560300d01c05448911258440569001c41c501510907002c419000901c14451449611120005040c030b000f0030388030854120b04400c608600c0d07131041d03040060102e88520307818003405200b40c075030f008081d1100700090140c9000510001c195042070140b100070035000300750802d146506250040c0d41e9956a0210040c502401030041e412112400011040160026040c4080c04049900b000e0f11040d41e444002e915080e030103007132104003480c103241c805402a103006c5818a0b03014100442c0e1843c00c250700306e03d00701d205040302c000107001e800100500b12603103002c4643c64408450b06200e000c150340340c02c1ea80e40c80b0020010b0240d9a01074144504041c1541030f030340500a02c400003400380031503081c01401c0e43c0100101d20941d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 878367410 1250 878366160 878366179
    0x7090501030b0a050121020712090501020d05034602030f0f0108031b100c021b15120903070b0126070e010e040c081608100e060118060b070303020405 66
    0x20f107015107021046480503540c80d4114540906509000e41e200400314560303175002d00150000525640f08010048950703a545881c6500e0700000903d0150000c11001c2400001c109201d803184086c2c601c42d04442d41c20418901c21954100092800b01c1d410380c03190200072421410b92440303003440e0000e50040a00100781d404503150b050200440305400c1c07040001711b030310070000001d4942d10300342c0f80c0040d10030450035200b2900300c15542c0d8082d00c0d10fa400100060304018000303400100145031050708440140d845c141140c0103905004420322880b0f01018a070040c0c1000031300300c20710810072a80510703801041180726507500d0341840001c1034190329814101c04032181510110000007600c4e0200ca610440221060b442c00030301c203a2100c00039000b6100d00c0b808200101d0790010821003c103218800001101e021480c01492504102410100d445402c0c10400b560680001c0000c140f410350b2061480c40440d080c2d05520317900140000d46c03140c00144d201140460038590581c1c0600216002071301d030b0030035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 878368660 1250 878367410 878367431
    0x60c1d041503081c0515010e09040f060f0b01020105150a05150403060606230c0d0503040206090a03050714040e07030b07050d0f0b0406090209150f04080307050a11010207031505040312050709050103 87
    0x948031a003500318001501080c0001c140c1c509409d020307030000e00402c0d0010100ca00c9482e004251483c0b11400303003219840724000d81e200d50b424410158801042520340c40c41940000005001690500c2001c0c89081c0b0040d9030a001d00905003241e00640c1d11031010004075948010182290040b0304c00741100c0d60032510507523601d5030407a0403034111807136030809404415802e11041d1100e40000d030040e03800c00c0040c0405e40c2e2544074469188040d50280008002072454030000761010f165114045004e1402c00005803d11000005e4034425258400071000c020340c0c4084c012141170060904414501d0301389000e07250240e001e58804d62242106640034048262610f441101340d1082c0d03410117411070345c208140c5d5036225030400035202240020301021701d004d0b41c80702031703511355048004240c50580208844e20108880b68030140c820150a0002e803215900e940c9030390300b042c821102c07902030705622040041c0405208116801c0c1c0801c01360410086802c2c11301c07004215594500031140444d05e000d000702c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 878369910 1250 878368660 878368681
    0x914010f050a0f03061503020607060605130212042006070f03020c0402030c030f0417040f0f1208030a0c0e090403080901050c031501140d090f060c1d041503081c05 72
    0x4094a401148802c0d1640c13441d40d82200030283d90342c4001c291450b8110100c0140c0ea034000074460180252004a246400c0c482002010340c0036088640c1d8140c41040b80900d00108500c0466200e0342040188651029a1070112100d01010000c41d13804000003501c03404100114101c0030030280a0390868024003c4036040c84200d00c03050303900c0c22116506100090102e000464841c2d8810b1003502250403c04000d17000482070340150b0024035000480785014050554003803c040c1c0244108050180440c010b80c548110610003c1c1403850900e889846c0604194040c3c500382c10b0080001e00320003080d14060400078024081034900c54250b508210105000204040969010341ca40054810860352090b0042d6040e1400c0050803422081c1803100d49405000744c441d0414072402801c20246000b001e24115003202c03203034214032040c043c8000c2035044401c1c1c1241039000607441501c0015595131695044c407a40c00c10f42d80010710031040091f41a40560194444114011404100b445a40c90f02e15000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 878371160 1250 878369910 878369929
    0x150305070b1204330f180f030f0507020319060b011e0c0f0b1614030103080421020a03030e033003180307050304060e010e0d06050c040914010f05 64
    0x62810010b44000b09011540c810b0a040703140715036001c140f01c050346160b00f68030043c0c90192980d04560ba101a09486580103001340c00030a10342180300c003013204003581c5500300707101e801001504000d955200684650f000300200d8800315002000c0f00c2c00d4640f00340250b000d06001500444400341400040c021550217074600112816140d4806825480302d60300403118004542401d0314040341c1d00c002d03c13001c02c0143e04041e00881c2408041d0740c0900d05010b026000051412041542900c1000104007041b03d01e002d80c3d054032020328100110351a426806031061410700c0c0040e521440c80300002080517000b0701d41801461043c2c003600c600460785148c1e03141d032031203e00e040401c0e4241c1d14490066103810000440c1d00405602d52a891070902644851842c0c1007032104451507400042d05000190300700c1241e000d210000d2800010440c410404280001084070300200040c0c0c80f400499000981c01081d50041d1580c172100300701000b565807100c03007080c00078483d20a241240c14030216003407c280200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 878372410 1250 878371160 878371177
    0x15030f140a1a13150306141902030f01053a1a070f030b1f0c02090603030705070302040507020f06010815010f0501021c020c13051501020609030a0815061b0607020606010e0121150305070b 82
    0x4c10500e03843d0200f03008075a00140051105190ed46820f03d04040001d00b840441084103004185040f20526014501d80b00340900032180d14008020003140b5580b04a5880c40c800e110314000c541d01a1001c04110b0b50b481c00300d00c007a038110410020300c0c04117a0260803903000e00d008071020b815944a400516499205000b00540301c5e80140390b050015060a81041750884410310403030781444000e5040c02d05040080e00700005c039800485107a8070b000d10403003201d8050259090300580d043d02d003400207595440c585450854002040341f00c481028000d000d0003a248902500180e010954080c0303007001040100d0762002c00c1c1c0c686290003200e80d40700066103403082c80751400542c030300250400281c5659000070940300c14001c6000e0301c0c0034140c4800703020b400c540003d482024000c0d03c0f81ca90383c038203001c0001c01c107204560102040240c3c6a03404030000f100e0b00c40a003011140313920358400a81045250320100503005080c088000000346d1403100c0384049900032415202a1030b100c12000e4568031500f002c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 878373660 1250 878372410 878372431
    0x1c0c090302040203061801030c08060a05130b06030a0b01060f14040e13052d010b10022a0a0b19051315030f140a1a1315030614190203 59
    0x814401410140d00954000d24000e080c9a216030b0b80d18058400e600702608111903282e007035038041220030410400c040e04030408080604c0710340f4282e41c2da281c0b0342c0d03080203000c2d0001030040c0c085022030b03c0c02d01840c2599604288203951a6031502000b9240c04d0101401a0004807041e040c00380022007202941c0660741d0002100300c89031600300c0310103844c018003a4182d840f40200344003c1e00001c0e9103459883c149492168540711030051310381d25401c40d426918030b00c0c0079000d100ba81d115225800f01d040c812210484078001012603804d925644191050311205401c241005004218a6403c10140038210791090b0316000c0e20000d0a0200c0303442c01041001580c1d100b04000507c44101d40c1c2c0705442c0031000601d00040e0400b000388a035010b880010715030142c81c4100e10180483e441d03490040c1100b21407844032940c1184401c1002c2039880c07402e04202c3d0003503651084001201901e800d00c400081d42c2001e000e1007005032080c010070b1100d5003038a0b8a080702e640d02c01d1385881c200782e9009603449804000c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 878374910 1250 878373660 878373677
    0xa050103110406111006080a02011103090306040303022208030c01061a16140a030908010f0c02030d18050f06150a082113031505070e03030430081c0c 66
    0x983c00e0303070325201d5031100c05107501501c3d40c9100c20705502d1044c6801000944020503100c01c00d800050444218006540d4441e0030400c00700314681c40014120340c0242d0715290050303030740c055410302428101c44100d18070001070b001d0900003810300c0000040c01d010050903008002207651481a00d148069000c85003e050000780700c2400d2101440d03082c44940c034010790b00280e941601c0383e01c0b2420444841012070102d6154401400040824070440c2d116100d8a42d080124100c00340b4069900d026640c0c0341e2074003039124015104201c030322a61a488095000c000c448000c030300c017000c058944000f211f0300444e080080ca01c800075450a02e085201300c03503030300020742240282c0481c1450100d4080c149200401c0c4100100a2101e40d0240c0503001140507848109000c0a13441d082c1c001d549001d0055401c0200030f40004400e1b640110860b0300f201c2c105041c844105541420403002d5a030091242c2c000000390104007028420f1100007003810a611100c1006400d6115035054121034080081900050528 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 878376160 1250 878374910 878374919
    0x3060c091c081b03070c050f0f0f2b060510060c030309051f0b01020705040b090117120d1a220b0d020604030c050a0608090c09040f0209150a0501031104 67
    0x40c0d650319080c50003540b069180501c540d0914450703c0350840c1e6406507510000d00c2c0c000344105154070030003a2600b01e90f1a5100721401b0001441c04892010140c4500701d84500c4c074000380d135074070684c0410281500000c8545c404a81e07850168244204050320041e06120010f0702c041c0c80b40c40c0c400c060b2842c40d110001040042d840031030081261070401c035818420714507190304905608250010404520b40d000c07c10403009070009013004015807101d40520b0800394a0402951a036800b1415100c08040302903130060307000200b600d40011719084c01000302002602a00001194000c5902d0031441c20341c5514031003500b014404121b0180d11340348101203c48030b840c54200030071f0708440c4c20250001c0080a1038a001c0d000214503030302590003111000750300d100030040703800c0011440d0010315890034074a000c0d183c00318040340c0710408200b80303038031654001d000241082041543d1025154001d003a25849151a40e044d000c000e0801c903e4500c28008030714001036030740c40303406101d0010074840862420705250 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 878377410 1250 878376160 878376199
    0x1020601090c0203130816090e03040b0703021504030816080f0609060a0503160e070809071202040f14101539060b0429010f090807030c0503060c09 65
    0x10780d0340842c21804200b013140398030019408100d0152081c0c80103803c00c14081c00c10a00360740c3e01031f804000418148803401c11402d1012081c1e03001c4030150020713540d40e01c007130307140880c14107000038401180544810184010303d5405645580b01d048100c0c0305a5060160f01c0d41942d50b09022540c910303d4180c0031002a030f441c20000c0e00781c2d401c03a0015140b180c1654483e80002d017000f2641000d5840c605280e10304118030210060400e070041c0d81802c08100b00d0030224042612040103005511244200320302d500119200d99000300101e44011004011604404d840b10800110a98070821100d90b110000304960744100004100840c484d107a41103d00c410480366084003203510030801880781345481701c0d51010510304a629009103d1200000c514001008000840d00154a00085103204250000c0d0007084012111050002403d00c2141d1840c1c8a20450703400e821600800002e02607920b0020400041b102017070b098400c100c0550b200c0f580c410060740c2040c01084843c5910402c41d1054600300000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 878378660 1250 878377410 878377421
    0x1d09090a060b0a080a0b0901060501090b0d0c05040b03011214062701090605090609210a05090409120c0c050d1a1f0e06090702010504030801092304060c110c0102060109 74
    0x1003d44241e004942e0782d80180c2c14820f0202c016a05a0301035020403203114420310481c1c028001c00d003402c811140c02d280048007180201c0c102080f540f641c03089000d07a05030007042903c0c02001c00c40f181658070f685610107012502d0320050100c400b80400c3c008002440008104103100b20f80d60310359076203100c0c80508a0b071102c00001c03c0c1004913558618540d000f03d0781900550748605a8000207000a08000100c580350490683c1e882005058840c00c43ca8000b030500c1c01c07075040e890240741040d202e06827000041e0081c0301040707005024100c0d00283d1854107030806a4840c0140c000e104180d4502d9480c403e01020054601005110100c5444d41052502c051881d090700a8600025145428510300c0002003029050300308140c200c1c245820001c0914144444990041042c4002d1005042c40e40d40134013800010302461034080c3d101e101c3c9800d0090303403d01018809004603100d06250802d800c03d0350040c80520707844000251384620b024840380c00043c082e4a401030690060050760b1a05274030200420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 878379910 1250 878378660 878378681
    0x303110d0807020c0d151103180c0108131b0905011502031305240f0d0c020c0d02011103071a01090c021603020607080405033427060b03071d09090a06 66
    0x3482e40131b10001c02d021600c01c4041024403504900c0d40e0342440049402c070300359a40f035003460300e40c003e0401000c1640d0005005400c0b102e00300c43c041d40565649801b1049941201510040d503842e00000100083d0940001e0304031032844561181100c4c41a0040303840b4458600b01c00d034130400c815000c11441c20240c400e6006102c41c88100744101c0310080880c01c80350705c17200402c03200410102c0c141c121001c45d40f040640007100ca0004064180c107080104041c1e040000c1c0c080e0501204c100d218110107002d0049408403075000300200c1c090006420403e280102c00e004080d0306601d024584001d507400058048000120a074100001c585180d0030056903901c44582224601018040020b142d1010000c031040c00e000c0d8400c8103a078100c40c40c40d002208003800880700c041c1d008260100a03268417190140d52003240c83c004a00440b80e0640c5190183c100307a400819405000002c04c031200d5446805a841c0701040d480321004007007490100403030080d0a0f5200281a00600501c10008140303510007074404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 878381160 1250 878379910 878379923
    0x3070206071a040f0b060402160b0c0c030f120115080114060f0408100b0f0a05040504020d050d200307031428031d03030c071e0605010303110d0807020c0d 68
    0x20386241401c040910b0141c4044504000341181c007000c001c00003520700c0c2e200d107080d5411410300d07034141c03000c101250060102a00045071032000c25291140794044885190351401200d54a5150030810311190303001105441480015100102c0c5106c040174820300603851a644901d032507403c3c0440d88459410065204d980aa0b08000ea060030203c810042e00c01008031901620303901c4a1400b10300c00359605007031042c1c031681841000b21050341e22000740d4030659000f5a0001299905d43c40402d0071084108400b5103140b03d490050344e01260b028981c191052001d07400d20029220303041c0490b070340c0d00680b40d0003070129290f0322001145090150241c15506c2240a40348040d6224581d11501001d00f05525400680c45a001800f110800f01070003809800140041d4030354074010120b40b0490044120082070807820f620b02b20f010682588414894a0b00184100460f5039603280103030071650140c03a8011070780540920050501c0c010411984071b91140c0e0060000004d5900400102d82113599049508 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 878382410 1250 878381160 878381183
    0x6020310170303070822120f120b0120150c0304052a0409020112050c090111301e090114090f01081018020408010608120d0914011802120c01020307020607 68
    0x41103950800c7c2c00c044c58035440f03038550040d01c0781008000100301c04202400c141031611216003030360f0200b40131110003140c035005c1c2c400c0c05c3d002410900b01407880302d00882080d003d03401d01c00c440c0c281000131801148117404591045100c500b900012000310b901e40103020a0241000d100340c24203400c0b02c075642e80b0500d0301803690000c10400c0c0b011204251840101c01c0e2021a6a070405d580000c981d0101d881d14200030201d80d42012840000d0b200001c0c4803c8403907000c0c1400c40d5040b0300398015102180400300c03056541011009203004560096241140003581a17030300e4900807082d001c1194030885010304040707040c0304848010b44810002801c01141c0100c05075000600b01018808207540d00f1000d0000740e50755280000403420751359981c10000d02a002040c501a21079030b0542150b042040f00030000c111650b06060481c1c6c0700320305031401d2030294240b005446880903868480140d580c800c548003a00c40d41d40e101407a6484040c0c0280502503841000f81e1f0f405840c124015004080c032504e0505803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 878383660 1250 878382410 878382413
    0x2030408041205070311010903170a05071a0906280c050f04091505060c1b0406030602040806041b1d0c09030a12020f0111042106020310170303070822 66
    0x90b080b1507007002e42d041e0300251028001c000740e82440100f41d000900e42210b031581140c8582404940c1221031400384840050300809260203030040d10f186035003019401103807420000e01c072045460101e4008126004402c0000c0c1c0101101c140c11280e00c8110240c4409094000c0b400001011850304000a0100038002c0b28030700300304000100081c01ca400c80108554610350035107030b405061a000244590414469000c408000103500300103a00c403900251401d00030100490018605030308040c0c0114000a00864004000500c0600491262840c0c00e50210b003241c03044103401c018003030003450003408840981341601441815401c09044011513207018044d50000b4500310300368004441802e449080c084100e86c0501513a00f0000c5602c0007442050100e0b50101510700c2036001d1b000c00d040c40304020031385440c1d503280c2c400405d95208600715524180301203c0e448103106d5118a030b202080d188820110307440c000c001c0d03034003d10b815142d89202e0707128100a40c0200104109003812480e18009910 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 878384910 1250 878383660 878383679
    0x307170a020702090c0705030a0c0c0302060d020a0806010306050a09020d0f09060903020609061b071505010605190c080406030b1f031401060206090c09070e03060a020a0e0d0b0103060203040804 85
    0x14000d261440005a5880c82841804000a030040801c1d504200901003c00822000f004448880d0418a01508123083c50718008e09000701580019420420103c6c5500700b072011139000b8070142000c1e0321900215510703180114242c2e015030007100d0300644811f20800c001601900a00400c6058210108400708070f000e00000b1211742d84c40a40b81e558640319560281a01480342a400c02c0070b034005440c140c900b01c1c401c050900d1041d400307000d202c0c4000500c002070196407040c800080c24050414065075a45580080154001c011380d14013a400e11034881c0c0700d190047c1c80e038a4a5541c8041181d06192500c0030981c002c2c41149a0941c221401c0c101c907443c10964810710070620081502c0014241140030b600008010b030581141042d50311203030511006982c0000d80f45a51582201c2040450380e580804488066075214203d07014807074003081c00b021301605e401074049078030390b6a103202016080c0c1c0100304407080308840241450a60100610100c1d8641d001140c0c054000c89000f80740c16607030300c09603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 878386160 1250 878384910 878384957
    0x50319150501080106050f07080307050f070b060114070b15010e0a18050114031905010f15081612030c081204080309070807050f0409060b0a03050a0303052a0307 71
    0x110045008010a1120390b03040f48145014000918015041c10b00c00e244222807032042c141e000c0e0040c4030200005200a22400840384a5001c00c0c4a090b200d85491034641540b800c1511a0341c0450314241d845060003080c00c056804040d04048050403d841d80b42c8405120303251509600e04205461640305055280c1030380351300007055807039170083c640503503180818103c81041e0001880c190404410501503a0300083d0081c810001c0350600700800310754509903004094640180501508044009031465044c0c40c2e0343c011035a003403040d0b0700c030105c44080c4100a124180a900d04000091100c0c4021900c0348242d540c285214070002813500800d0300041a1541040b58202d81240d00042048138521050140030300903d0301400802800c0c0c03c150000d590300444013000c500450f0385845040910010341c200c0340d04801c01074aa0202d541d12418020349400400034184e001c6410403001c101c8003030780c0c4000040c1101805603202da0181803c0070b62704180d13002405640800c4034090003460038217091400b5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 878387410 1250 878386160 878386181
    0x31050108030c01200322121d030d200a2003150601020c010e0f2e080c030604110c060709060f1b1b08010903020601050a170706050319 59
    0xe64a0b050388501040c04e40c0c00c140b9521305480d12180d030319000641c0050641303800c028410407414085a0750f120012140500380000790035281d41036010312082d0341040a024840c0c40030410080c4104e441003c0c181c0c0c614001c2c0c1c0810000d44407810001d01c4c0312504c440114855088030555010708603649030855460340f00042d110b010420f803040481c00340707010071107004140c0368801c41c42c01c02e1800e480083d440740c06010501c1c0c14030070000c00612a2359510090030032902d070000c0c820146130344121701100c18010402c03401e440036001c003458002c0c0540500c82d00b9103c3c40400007100d1460b51200240b0024003030074240d641c00407000b840094201201840041d00c82c054540d9400080b502c0c0c440001c0c071041c01d5401b99818007040c2480d00540c030380405004188a80c1010700300050210009003222801c1d202d600c00c403415460b150340c0808060303000c5401412950100c46640c04140c544440f640c4e0904010b507180f0707180e0b101c02001c001450281025507404031030301c441400c10300c400364001403c0d52040c000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 878388660 1250 878387410 878387413
    0xa08121503010e150618010b180312370e0a06050405090c090d0807060e06070807050307080a0b0a0602031e1309050a02040f140102010e0c31050108 65
    0x40002010800340000c000003411402840040c81ca1a00342d521640c0080a0010b11214440000c070749840d124085000e8040c0810a000190780d940c1d42801a6040202030150003110300707220b404c10385030000703181d10042c49802c0d0041c64031003e86c10034520140f0b48020508401c01c1c140321400000e49a184030303480c04505d40c13621f07017501c4101c1003007080700c0d04541c200300300b409018042402952134501c40c29500c00b000c4050607580311803e90000e010313045102c00c0140301000024200003040000c0c0c2200b505011198200c886503240c0c058151134900c030442d04000001d00902c00070307404511540145070401c02e04100054240000004030b01d1000c06d542019016910000725085405448201010041468002e10741801c0700091902c851820314418005e03501d8a03800440d503204a03617411a0014920000c052141c02d0743c0d17025a190101007286005d026510701000c1c030000751404a142501e10500401ca0020100d07807450020300325802010110010000d03920140e80800244030340b07800b1f000c0550 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 878389910 1250 878388660 878388697
    0xf33030702031b071208221e0518070e040902030d0f091508071d130b03101e0e010b06180901060c03020d050904090609060203010816050d0303020a020a08 68
    0xc0400f4031001d4411903400326a019074800c0008551000403080d8850b0700c58945070380c85441003036281200c180c03c04c0c030783e4003440601c80000e030109407802401d02160540d800003091954481c204542010302c1c8011800c1da00200e000a0340e524484c00300b0070540c140040c0000390b003c0c09a004a0700d40740c0c045a10b0030200e100c900040c4d2006400204040051600114086001c0c58805c002011361202914540030300141341d80420b00b030020503010800070303040038154003500c0c051200b00c0405170488200580c0240211102e50000d45014020b2241102a8801001d1942400c3e07038620010001c40d01c1784900c035561800555a155600700c000d2114561200b0b10811404102d0100410070314103900400a11400f01c0b40c28000903000310340541005903d080142d100d010080125000d4041242d00808091a0510300350403c1850b43c007079070503107081600311009440e40c7c00071100120090f000700c550000f554092600045c1c840d030001c00032101c840c8160b581e18291951203060366004151030145065004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 878391160 1250 878389910 878389927
    0xc0718060b1206031f021b0703080906070201020f0d050702041109030a0206160516031a1e0406060305030c06150102030f07020913020603090a03030f02090d030c020a170106140f3303070203 83
    0x40d01a140300907c0040d194051840e03440f40b602c0e00c940d1103902d00602001c1103240075607000780120b90088980b84140c07001c420800d90018190750120700c1c102e01c11403405c85c403410055491400c0d12105400600145140070490f020050250080103124968620b130711788100010304140b101e02150000515000e20890541c50280c158044410403004e28011200400c003801800d12a0070b40c08080362440b02c00d4517111410300d4009000581c001a10901c0300003811303040100005002403192030f291a0560441c140e110049032280704000700d02d401b9032001c3c4202c7c0c0141c5418000315400a1020180071031001423039000c5a9260022210510035810442c42c8001f41a05405a404c20201d1040c04525241c01c6200155841040c540301504000b00c02501d18119220500380ca00a80a6402000c12444002e11502d0180c00c0344c1c09424200b6014226002845c10f0000a00c0c1e4840e41c028992400c00b408000304861078410aa805040c001448031441c981c9002500154081e611036809542c0c2c44124 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 878392410 1250 878391160 878391187
    0xb1b0d1409150c04060e060d1a030c0102060712020c070503010e210a05251b090624050d1b1e0903080d09060f020c0718060b1206031f02 60
    0x450070300c00c2c807050110208600a56188219815211642000c42901d0380070400b2030386d42e0041e82c1204050f0342c82c0080e4150303400400d221041d40001c040b4225000131445100480e1503070f1060f50868003007041c0034440518500079030041d000c80c82146c4111181203550304000b03820360b52090f007030103004d40140c400d01c00d60151032542c03441011102c0940720315000d0001ca005105205644003000300142c40301d00d203200c58810840e99001da50304a881052050401c1031040c4c84008984a080c0b495898044009108000d03841c020100d100014044103086c15040d0059800c0d900982c000f000e92603032010320003a21040350310313400c000000981d500c01d95094030300329100c0d018039070131200340034003141d2a170400004440404456203040f1002e4080740c502054a40940074020840c820a80b503400482c0c030074030f08a00000c00004850000310164501035158100c1c1c2c044030340341e004a1580c40800c004d9203201c0d4070441c140e1b0307030401c2c40607040724542d02002003046d580c0031320390b400303400020f4001542c1800c4c40030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 878393660 1250 878392410 878392423
    0x60e010e07080105010207140414040309050a080a0f0602160803010f0306050c0c070911120109090c0b0a1e17041a09030a02071a09090117010c09030b1b0d1409 70
    0x718185256994100070020759158198401c11180401c0c01007054800e485580051b4580c0000000800280c1020314000c0d161940e20b009140c025441c1c42d00000301000d0028110a80342d40190005090300d140d500d40c80d01030740c070058a0743c100004440c1c0030310014600c00011402003000c0c00360044440d003140341040030740b03130007420080c4007500502c06002d40c3c80b804584041240e20450b00081d102102c003440c120240500c090f482c041d80521000041c0380c1c0322607042125414030811000900d29260300040a00340144134014002940c2900c030700105c41e1a01d150981d0801e0b00382420103030b000142c8501c2c01ca080b003c580446501ca0700c040300c04090742503480b40d01e421403480d0b4055800e1245000009580d200c00340310380c4600c56106000f169800c1a07403403c039521011b02815080c115a143c440c080212241710f4020f55481d0f20706502408801e1182d0b038a9010b80354002d010480c1038488a80c4100e4000301c040c0c03200c50b09070f001c12810402a00c60310031760070741e0a1000c140415034600a85610b00703150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 878394910 1250 878393660 878393671
    0x10905010b090c0913110a030e011103041e0f081b07050906061e0d0207030203070309141003050910051303090e07170403111902041b091404020904060e010e 69
    0x50b4450140030f41c001007402a1034800d01d054602c10101c409101121014000180240d50388840c001074003510f1960641045400800c240001e119140796940b10341513034481110060000140ca116240c08002c100a41d11000c0d809201558403421081e01d90f0400355001c400c2d01d01c0d1218000300040d00026090089200a000c00c84071004245070600214041c1d100c1c481d03007031030b40c43e14488600c09000c84070340580317a4004444a04640711102450080e58a074400e100a60214400c3e85000641c2000340301c2440c001c00b0090008404504007183c00d50141c80040c3c0022214000c001211204520511560788540c00c4105100e48180b4213040250000440c0d4010b000d680350860700300b0103c4d603040011188030f920f40b000260304039511800c0494181200300b21801480c0100d040e4609401003254070002c0b014000c44041280000140503101700c0840c001482000c0b40008000700500c0e2010f00b1010700041c8050805850040410002030884215401542c1f000c00c2c0d0f0001800503004240307040c0d5112 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 878396160 1250 878394910 878394919
    0x5041d010315020702150403030f11030a0f030b0607140105060a0b18010f02150406020301051507020306010527010b220e060f0a15020606010210090f02120f030705010905010b 77
    0x65041d912101140942202c2d0b012a80b030300024440119180c580304010307030440c903407091a1220b480303183c02091001c1484441d0001080024505102080802128412031450300c8500764182494000d90140c00d480040940c043c2d014000f8101007000079203141a9a41103500026240c0f4020080201da00c01c1c90700803080d403140c188084920502000e40805018000f400c01071034112440404902d08444880c8240742041d50009010820040741c01641c140c810894400c10041c41c880c0242135180100f00010791315900070030040085003420303450b01261028140c082000d90046144041c1403260a83c0100451500080c8500d01d40d8080c1044618228200c100220700c0c0389050400c040030803001e044c0c5481402c40e40c5845143d603490342c01410041046800c400801000d900c13010b501c450003100c0860140c045e485402440b00314920409488540c0900c5d40307001b12030113800340708842d103040250040701c2c4220f10200e08100410006808814403801c00030078583e0180c0b80941c01d4138035280320386014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 878397410 1250 878396160 878396219
    0x190b0d120f020c400203220201082a07050312011208180112050a0c082a0d0603050f06250909050603161827170d05070504 54
    0x30707a44810f2441a500d5031014a03801c0950040442e0550b04464400f544c8680c00020543c0c09000c003c0c1c000e1031056240c1c0406440030401c40d00516880d961580c0001d001542403000650b401c0c822504040d0101d20005c084107000c458490100500d0b40580800d5405900201300d41d000075880002c564007500350040c803a0f042440c10750b0783c5a02c138090343c00018204901d826540d12141d1140304445a2510181c3e42800700341404c40412004003416804c080000ba1900000b130a8000012240c207a00c8502c262703145682c14004954440d02d40160501d00781450b1100d42c0000400c0003044a20941c000f41c01c05003a20382842c08003c81030050a282c01d03c1107080342e0a002e449140c001d6032a1040344c81c02c0d2004103450b80c40d0000203080054080c0c0728502d9442400b000304011403841046458050041003c110400c0518035015140840114810141810b002004001810031540d81c00c012181e4052504003940364164009a4004481440000e040810200001e00003085003058210002030210700 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 878398660 1250 878397410 878397433
    0x42a020106080607020106173904020d06090b2b08120106020303010609090614010c030c0b04150b0f0306060f130513020a05010f0206010e100b0403081b060906190b0d120f02 76
    0x449c090181c503500c0f00001041c3e2254604448240d4103005d15100034800c541c0c1c0c00409649000614184c090000f00502e0110110041c1c1000040d4038070484405000c1020515000c0b81400b009110324000c449004081c400c00c107150003681f00d110302074031854000c0c0d600c0b581016801803540307190b9404100a03a00744541001810f44440325103152200078a480d01c0c62480c20306060301c0306c500d0402c009000300c541c40200301c2400740015402002c0c100301d9805000b038a0091302084848030039914441c1d0b140c2c1081c0c01180d80c600e007801c4542013181c1c0c060720f81c40440c0d40305010300c012108101c502c140a01c1d240c1c1c1c1c240d400c615250030703c08090802405c011110300791040c0029521403050081d81e0702d221110b0089071554098002c05002883c4a0740d03a1551140c491a0001e0703160889100e54060301240100041030301404100740780b040950300004c0c83c080d030707030103201d010944e000c0081d003043e26640d120400074940310250b260300654050103d0103c03920000d00c0003420019a4070340401103400601a912 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 878399910 1250 878398660 878398693
    0x105030c0426103e0c160312300f110c03091309030f0305130c06200303010b0414130c1d042a02010608060702010617 52
    0x80c00d450402c2541510910301a1140d440c1d00e620300d500c4400c5124203522414034898642040200303031600005964610102c0480c0004682c01e0000c0c3c1d40c4502e580c18881015008a41c050402080c2c3c42d01251141d541d4069041c1c0c20201681060311141c004400c070313010b0f06400803020300e480207804a5442802a4102e0503400560307000b03014909168a41781c0d8000800c50035008801c504101e26440b503980e40b05070041596039402621068013a1001c50701c88900b40e56580b08917a5003d4050f121a141c008041070220b008110040041c2c4080d0410711004c800726001c4441100036203119100c41c1000d141ca1200c4030100b102108074034075a1780c8200014030521005000b91411500440f0303040124491040010341240c580729440803c1034907043c1000b918a034043c000c007102000540400c101017400c01c050105a07800811070010b0003d4003241d030304022002e401e000c40344030f0241c400042da40307485d02c41c524240002941c003030b40145e46604042c4815840980d20a103070100000c01808482c07030b00c0800d0b4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 878401160 1250 878399910 878399917
    0xe060712110709020c01060f080307050a081309020a0c033b280303090b071e02040213031b052407031116030b281e020d06080c0105030c 60
    0x38000c0041d41d4a01d105240750410000700601640d040a6403903441d40f002e1240208200c4c484c8a511003841500060402c50200845501c103400c00090481350140f502c070030503507601185400c119020b02420004151f6502c1c40900601812955130600c801c00390305004001d2075044041c0d0000c100d81280c45500b1001c0b0346a10700794489505d0040d1100090f0400103001c481c00104000a90690301c42030b1900c045504a02c4810307684039480e0040c0300790b15171400ca0500c1c02641001410f460b80b8020b00820460611101c031140c6200074405403400314441500c40c1c808132a980100c0e100c0001c05400542d600f50820301901403c001d032032030b40c1f600f5600c1e6426000b03400502d40341085107038002282002e06202e8121810844000070803074550f08119001c1c2442c0b400144011303940710503500042850342c0c0b8508800a070f00e600d8903c03044031018003039504400800c01d1782031040c01001107520803100134030540007030000030030b00810009030300380351850341820982007401550400c2010020070003031500c04810b5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 878402410 1250 878401160 878401193
    0x30e0613030b0c0d05011707081b04051003020d0302012f0301090e1e0c031501140f01032903011d0a29041202010b010801061713060213060e0607 64
    0x742880d1119115601d440c4509030b610503c550a05c400400c960040f541c1e080c05070f0001200301d071812503550306803a407204050345100c809000d20030041e414600d01604100d07000b00350880d0755604943d8941c0000c41024007014110003607510b8110314000100646641c1842d00070300c0d007a20b080301044130301c1900644414040d0103541170f641c02d020469008104130310241c41c4120841e4043c4800324110295407040d040851610a2143d80001814170840428090403a449401c0e102c0c0c031091558204038130001d44d40340707640c10507958500c3e454042d10030003004151441850b899440c0502008281070959400880070103400b4002280a1042c3d400010040c4817250490015440e49080c0b001001c166184507009450910140c81408240424901207044c58100f80e00200301c128505001960703004024481c00c03010413101c540455500766100c5905a0200e000380700140038500c1640c8010490b0004074640303040c035420644c01d00050f0340010110411090440d00307181050419070b20301c080d07600f81d000d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 878403660 1250 878402410 878402423
    0x160918080f090d03170603031303082b0209030106050d0203060f0c070b0717131112100c05040314010908071e05150601020c01080108030f0322030804030e061303 71
    0x9910000d06461425142d40c900000c00c100c503400d8042c18010a04500400d0b0000007200400c08a40607140000c221620403003800f2120f4205803640e00c4039140f6801c0b1001071031030300c1c650b010810000301e851420313001e510b00b5107080180ca88041605040c2120284c0c0c218500980c0b24100c802d025980c0020700300d40c0a03c01d850040304550360300c1e00c0700d0340c680070301200208100100414030610036041921003110740d0056100c402a5a100005540070385e0407404003034040113400d002860766061543c3c03101c3c0c0c2400c901d0b0440d1f030001c1645003054100e6200c01003c10000e00c010500f44100110011002c9643c8001030084c42101c61544074014180300c0d0040c0241020400300b01c501001140b050705900b0ba9800405440c800d200e25081020380075001c950407170040c0140f50036017105e076000380c0c1481c1c181c485820040d0708044580000880c19400a0503403625000c100ca02141030403120400306905501ca66980b403104e007000d15001c0c25098080da8981d219403030503c001803441c4002ca108008481e0041c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 878404910 1250 878403660 878403667
    0x906270f05011715090c301018031202031305060c0306041d0318010c06050f0a05090106030b1807030209040303020403030906110c010c061104170c030606060403032601060216091808 80
    0x2a02000b03c987e1a68082d10200c5008001100a24020549070f284c1170100009002c00c1c0d031108048080c0c040d8051004010981d242070450a0180c940d000d1984412020004604005241c031001d02d0b100080780e007003100380400002c02282c2e0030a80501b000d070a00e075900d20410001d004814a440b0300400d030945410407070114140d003d0380c3c071a03809818410b03042042040035040807038004d00403e8088076000452402c240110b56440d41c14824074084982112034503229458a02c010082c00c211011814440d200300840030001d681c41e42d0340340f400340b4402c0d14016a02d903d14900604442d0455001d01c0c00e01c103046140301c036440ca01003902000c005091074050320001c268031f443c00c024044284a0400d5000116010030b5164016644214a80c500011600104824401c1658852040b5a9a07030002c40a1204200090107035161480080c01001e4815513170300001501059920260f0207200140d10010016401084104405000e040319100500c017110400c250741000c0d1003410001880d292001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 878406160 1250 878404910 878404939
    0x14180c0307031b0911030402041505030a060e010e070602030712020a08030f1b0a0e0a0e011a0a140a080115090b19140a02030a02070906270f05011715090c 68
    0x1143d5640a046007030b8040108070385401d00a042d40d0400c440403405545400c1c110280c59102d09480c00c1201d1000f00200010b4400795203050240070080ca100320b00c0d64849c059002c0d181e106102c020080d1907540e00540d00c0740c006c0d041006401e80000c0140c2c1c10b64100e100a4070109100f03004aa40c403405100c0c0030761103910b5100d46650001c064050688071250040b80800100ea80201c10301090f00c5d086030000c048545400040d501880d00b031140700074100d0203010ba00032140310803000d0320085030503003050004c0c0140386c83c1402240d80910000000503503420014040340b1311400407940411814600707840e0050900423124540c0c072415500e41f086074203243c0581074092140700b010043c2040c9100031a1500e1080030080c0d540c1d0002c1031000d015010717244011500d642140328090481d845408603080b4a80302b80c0d40011480100d0140c0c03040562034281820300300003d405994000c14203142208805000342d4000c60a0072080b000611b11212003c1c207024003540300203030a0381081000c4800040d0403850 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 878407410 1250 878406160 878406203
    0xe0403030b1f0f17060622030606091506050a020c0105310e0f090d0e0607064101051207050307240912060b0609030114180c030703 58
    0x2d458101e2610031110031080d4240342d000341d00405440198440e080d0861084030f0300401c54000315850340d04503400f48a03815210001c0004400d28111035010000110b8898954005903090364119441c4181c030f0740d10220020821b0b00010008041350315009040c800c90000080d110031710402c4a5041200c04903040d500000c0c41300c01c030080364010b200108140784403c0134880310383c0098450440b1203c00c0c9800100204110215144103a10910107400342c004070150030384211b0800d142d0950004000d01451001507024841c02c540d520100e404100b0503452036020001402c1d0100b2000c200d802c402142416044684d45c880d819600100c94150030019040300c510b14041403035012a5052141070703c0081c5002214454592500c4020a500d4103007000c95010f2314455110300c40c1160204540c101d1001080441e4481e40b0151801000b01d0316201120001070b080d150303140c1800d0043c42e981e1041c8140b42c20f070007032a400b130010280c0c054684020b02760000398888846100280030501407e0808a06c03000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 878408660 1250 878407410 878407429
    0x10b0913020d090b041104092a0504050c0d0506041a0f1c211704060b0a051504080709062907150504030f110601060c050309030604030203090a0b03010e0403030b 71
    0x30303a04000c21250300a03003000340c0b6000d0255802d88902c41034410320074450905000ba00f030101d410264030a48527220307810201c02d08280360032041050761956004901981da6010b454010803840c2440c540300c0340c1e0f9111040840f03501524481c8540e15101090701076151005003c00301c0d00e400c230f5100040d4044540407a40c7d682000124900340d9031440e03510b00411001c42c41d0440001096600c804080071829001e44140120040c00d201c031601000019001030403d8101c081024000340401121035580c1012441100011000d00d402e000c000c141402038041c2089544000c20400c00281f200a18040f1741402c518103408589000500d00c0500002034901c850440b00910b038404007840000d52110740400041c081681c041b00081d504840700b5024501c242e1407216041001409048541d00e807140030b075410b9a1109017140e0500051140e0115582c082c401144902e000c1d4014543da01d490200304015070810b5086880380c60014030060140c01d801e0f407230490b8030540c541000100740343d418001502a56 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 878409910 1250 878408660 878408677
    0xa0f0b0a200a05043503031e1f09061e0f0e0618040f0c050d0c15090308040e1015020a0204020f0d0c03290312090a08061617010b091302 60
    0xb1a803c40c2a05500e90b014050750784010340c0b40407220305c41d4100c0c86403a8403040c0c50000101d40001000707603120000902c110b030040320a84401d048600300141d0310b211806591f0000140682c0c5040c10040a60080c50002044501602d1500194103021844142c22800e008251000c524100006d0441d151a0b01c40e0f088180004041c21a070b14003443c2200c2c0823022082c0850711805c4e51500020381c4d041514102c24810b07070040004086071300b040d0302420101c180221001c200080c1d014000301050114001300302602503450704e6072513480c100a8800c1d0440643d800f042d04101e1200605240550100d045084a9411503000d42c4c0c0343d2000d00700d241030b4016082d60400c2285000c240c2106190144e1150300320211000310000b85c4240810481240c400c030590164150700580c0e090981c4821800061020303110007052022410340304e045251401200312a6a1030b00605400b001c0035003030304400c0185254072041c4044c0d02540c140848d42c1e86500488200b940607001554040c04070100743d4041e220030f003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 878411160 1250 878409910 878409929
    0x30b0916021f020702040c090b1b0102041205010509010501060804020114090a030221060a020408030a050f0d050414070f0f060c26040906050f060702210a0f0b0a200a0504 75
    0x40002c0308802c4004d41c06880d0403803096141521407030780381d4000c04000d070445003110403d13410014402c6820f40d030404030782054411075500308000f103070141c0740245184845020b00c000042034a0480c1c038403421100c043e00600c0074040410204401070b0380c003210a1100402c2c87c6200d07038032001c0300f42c0451b11010841e0402940301c0b0401800c03544407402d4145181407000ea400846160f41c580c4403080c81288201e009140e0150070412240c066107006500611070007421140072071408a50a400100310b8000355003c0324100d00c01305403a0345c0014100718103000ba01e0140340da0078a81e80fa268207068002c001e8440c44088c44030066a00f024400a00541c1d80c00c4805840c00c04110720b000c81030341200350702c98003662907507914050010800b400d002503d00d12010010b040b444c6090055000c0058040c4c030b0300103000b4070944050307031140c11900900c40340e94124480c039030088044c40d0380d02d041d071401c1c44001c041c4169189009107110106400341400482c004c00040b031655201c1a101c030403034151003a90002c505e01d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 878412410 1250 878411160 878411203
    0x20906060d0e0619381504030f1a0f070813020301150501020d05040305030d180501021201140f030a17070b010b18090c0a0806300607030b091602 64
    0x13401002c8103030400c0c030fa203410003c01001010707030310440b6a14003a00c0210000a030814080e60030307a0305901c650010b000c0090080906000000d03454016600c2a04203c56030341075881803400300070306100c10150303060044214200c1c42c9065005050641d8008000c00100f100140208106c07440000e148403a164014009005a54110b6100c0405084a108a600511400c40700171720b981d01c50307802d49058030780c81009945444200120321000e03001001240f03503405859008030b0b000403024030003003080072800c4c1e007004400d40c501400d400202a6980603035008200d0404e0381e201603136011400000040e4400c1041c000c3e0751084207020741a001d4484018072405407880007041021603000a030441035540400070318a00d6680040c40234180d010b9a0034100c2c010f050210500720340c01076650740e511402c0900030040744952100001414090910034a10b072640e201881c0001c60418091154840c0003814107000c030b5140c0e1000305418090003000c490301440c05801c02ca8416100340182c0510701d03024010840d6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 878413660 1250 878412410 878412421
    0x2090607050706080105010c1a0705040f0e040614060d30090305060c040b042d060507030908010b1005090f0301050c040f06031506030c142208030403020906060d0e06 73
    0xa9a400b14010342001c611500000511517100d009610300c1164491101c0c010303500c007400031090181c40940180d0600005110210740140784071150b400511030056410554105810401d0840d1118246d1542711141d100420115444072001c00f01410b6020704418040840f050b40300040500c14241072068004610780600c026921443c04400e9a000780180ca0064030f515100c03801c0e521a600c40c1502d03615040c401000000000d05440700900c0e02c200c6007280e42584544d17001030614294010101180001c18000103255000140d20003030000c060007000003c0c00000017400b0071903d0904a410458005801841a22040c1c004075440c8409402032043d4100383c9032003095500540a207444044070110300017006803280c000c1240c103184c902843c5140f81d051080c00c80107000100d010500340290ba42c51005900c14200040c4412641410022523155134011848682c40c2694030503e840d50041c841031015a9683c0d190ba0307000501250310b5650b03000c15000400c0602032032a8002494040c0ca000c004c07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 878414910 1250 878413660 878413663
    0x910030b130209060f100f0c0f0c0602060601112512061416080f132001030c05040b040b13080102030403020604030806010816050f0c0a11031504080f0a030209060705 73
    0x20702180c42180d840c08682e0f2040140484207180090350303980702c1c021200f4020f03094019024a105c48a50345070070682c4142c9501c0c0c3c4020300005140443d041410b072081046410360510486800090034039000081743c140b11001c0b559555001c4400e01000b40446000d40105428070441005003002c1080156840c014285a00142494161400c1110340c00f00000c003640441d00c0c4010017100d00d51180c02c2d090712820040e11082034000c1a040d40f9107400006500402c4000162400000d03e84110300c101c80054000102994101c0341d420007070007400e020034010030b020117003580c0580b04c12400c16a00c0d0b91060703160303070344617012a40f140c0388a5100000f804281903000ca10f2030701c903501944078282180c40360401103c07041c10850301003924012080000140601c544018901c0c4080844400c0c20032035080c01c00c07410246030f894101c92514500d14264401d060034405440108100d10703600d0407910301600c958145202e4005403000c80c031000507070751700d0140c041d5040c3d52100401030b10f620b844407064501075 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 878416160 1250 878414910 878414941
    0x40b0d12030509010f0f0509151308091c0609050d110619110f0a0e06090609010f0207080f0a05121606022b0b18070c02010302090d1a071710050910030b 67
    0x10034015260024031610040e040702b801400903150b006003486254445c90441d8000034801640000403400c248868980420200c003610f0055000085070301c05854501d21301000c0c25008801d0081854a2503030603900810440c1e481100440548280d40480f90240d004100801581a0240010030103590014188000d00900081519840d980c680d070760080090a0040444090380240100582d14165116150501401125004a502c40d03a25142d4a50403c040c8034002c02140e408a900801480010880c0e01000c070080000c0c9450308803c480d203038000a0242d203020b040386d40c001908400d601c0e0726081141e480d5000b4000070030008039a8405101801200d001503201c0d1340d031010658007940b4070900c498002c840b661260388006645074015000303504200029a4000d080c040c0b070300082110a074030300c0c2080513646600092403030034800140801580d82c0a040300072445408000c2e0861100c0c1c0080103680e42100c4411203582c6001e03040c00c1004140c1c000400a207040340501c240e60240c62140c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 878417266 1106 878416160 878416171
    0xf030f0207020a0b1e0d021218060105010c14010f060311100203091302070c0303080601091703070308090f011a03070501021b100c05060f06040b0d12030509010f0f05 73
    0x340091b030001c04003203510b00c0d0005444410003600044541d0f10002d0010303002c08003290034100580e100740500949040c058080140410300100e8100c800342400094001d101c18403140d030b490005001e480c03001300c4d0180c4030100030075003601d032046008a01d103001d640214100b940c6003040040306e1001c407080c031424503802c128601c0031072480c5200001075802903c4050803414508001030035440c1300da001e90a804064040350a003100c010007214181d40e01480d054055480c0e41601a05010392240c3c2c1200c50741c64143c5140e400550303801c0202c09410110103a40d44a982e800042e80c45048550010140410308500000c003450110311082c01c095072403401c06021000c9644887c03805100344c4040760800080401c110f4940b4141c0a42c0b405540c00703417048900c07100c0f00c2d0358401e140100c012000082c541c4030000901c6d4048254407035000c1e14490142401811403803e501b40040809842 = true := by decide +kernel

theorem cover : BRFrame.Cov 878237410 878417266 := by
  have h0 := BRFrame.cov_init 878237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 878237410 ≤ n) (h2 : n < 878417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
