-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1485
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:12:20.527271+00:00
-- url     : https://prove2.me/submissions/fac0f53d-831a-413d-b76b-04d943231bf8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 266906474 ≤ n < 267086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 266907724 1250 266906474 266906483
    0x13f02070516080604170906040308120a021309110412030f0f170c09040905010c020a0302060c0c150c07080a0c120201061a0a11010c0f173d03 63
    0xc0d40e00050501038105501c04041980b000c1c0d26400c1081000300c0020790b40d8005412540445031841c0c55481410b6500c107440f60b20b500010040340010a206080d0040e000c001e04440842004c1d07034070849c8180481c411090081e49482034050248580c4256600043c946030003505a2440e26441d880c082c00760201c80f4074201c00090741d209808082c180c1c071028503070030000d850a1881c40000000d030034000410004019100b1030201158440c181d5642d50488402c140c0c001000300b003210034944000392a00c0b1003560503030246c0720b0200490608101c09080b03e44001d0700201501b403520a44040814802d00a4441480c4502c28480034000c00c00f1040280f981105940303a2200300c61207841c214181040040d0b0b40019a4501901044010b580d0051000c408480003042d81e80c030184004182c4040020a11401d641d41c60030070580121a0403104184840b1055210b9010b010030031036540003000d00444600321940a150403609502c03113201d6160f0919245496010740114049045000400c1c013030380300740c030b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 266908974 1250 266907724 266907727
    0x30b031f020304150504030509061813020408070b0301050a05091905150a0e04150c020f0f010501140307060905092503090b09070e06060c070e0a050a0c090302013f02 73
    0xc20444040403413100b2510308502407083d4501920058050b0040360035050040000244028200401944242103150014a602e041c50403800204000390454003440301e852040500c0410f0820284081e40e040b030701c000b000050083d08010038000b400202605969000d002190421520f0085000d61845041c805405400d9075421004202d00314810b54405055150f0303007418003012842d03081d01c03444101151040480c064103440001c13441c106203a4040c85017405645004080b049040d000107040754004040404a060031101301070b2140e80e42d21035040800c00844080040307080c03881000380c4c00101402400082c0c080c401c00620400c00202d001c00000c0d07520b0b01c0d2001002001514180c1255900005082c004e04104134011504005030030070740305983c04503003282241c004214a10140c080211141140d0134052401c10160509440c0482400e0403c0381c015010743c82000158203c94050390780c808840c801c200000810340d00070701e8039074400b100c54440e202e0b02d185141c40200543c03840b8a006 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 266910224 1250 266908974 266908981
    0xa0306051011070906052422031419030e060f0c06040303060b0c03070609140109050708061e0a090c0503030f04031401050702030340060509010b010f030b031f0203 72
    0x1035041c03c0d502e800009110340703000002c4c8016203440309010080a01c40c038072103041030302008510700356000e000741294900322600c01c001c1c1d11688000520044038898a05004408000c41d1229150305001340503503085003460403040003003449422900307403d040c05082c052815141079881134165020400740c003043d5003d117080c801013583c184950001803240306d00c0d00f03003014a000a80c03600da204501d0060082c68031030b4800b5041c070072a07a040c1c00840d00064020440c951646c80c0241e21941c0c0c40c8110717003160042100141c0202d40c0009412980d090f000c90341e10351075071090540c400400c680c01080c0c5003107500e00804245c58504000810500007a80c1005031641d18620706a90104000201600350b81d0402d024071062070380000660b608040b80c041790381042d01c00f84130320124645803807440800e0403450060f00d0360f404660580b0060241d010701010300c002c1d55109402c2e070030303128164029400200204070303240c2128826400829800c01c01000e85081c8103030248400300d080544032540075581d03400010f2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 266911474 1250 266910224 266910257
    0x1b062e050a030b0114190501030b06040b0403060605130b10030519050108100b061c0b150703050316020303060d082b02090a050109030b0604110c0a0f0606051509060a03060510 77
    0x4142030400304580c02145114070b0740006c0c1c0d0751580e0344651414140c03640c1d002280e07075842c502954003410260b80300070344807507aa050038030150400b40328441c010510207802040c0160305006040071110040c202c1403060b00e001104074000e081c01460b40c82641e0303e070424401c3c138903030500803a0700034018000140144042946420111a40d440c00e1500c40d000800c03503411090724041102854503801440000d048001c0000315210300c1d0003110070a201c0c200010500201234112025500a10103113080c00e1844000c000c0070fa80d42d1000391111980810420303035000c0041d05070f10080c000c6080344e0012082d1201c40e6118181c2c85000b80c241242441d8010035a03400707a0030006c206a009000034030308004154038646820303030641c0b4007800d16400703248c80c0c3c544500c0020700304044500c1d4070b902200300c9507079803c282449803a240000104440e4103007050f500048614000c800c803a030000d2800c8020307160075800380404c609a402600200c041c1501e4403c001081c0d900c000c001c0c1c0c0d5a1245890b4484452074a4a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 266912724 1250 266911474 266911499
    0x4020306090a0201021509010204210506100b070b0c0c0a0501050f0705070b0c0c0312040f020901080601140409020d0c24021b0609011809021b062e050a030b01 70
    0x1c09005a0141c040400540e900040c45240b501490128441c940c540d82001806403149401040c0c0840ca60404a58601d000013084191607000ba02030b02c846840b0341801c4400020a4402c01c500304d041402000007003032400300d006810001c0492424a0483d0040d005030418a800105a0342655a07c04110442c40250103003030b4012122f1419500d0b109960f511036800750f10184c01c0c0d0f05c28080201c1c0ba00284c81040085520360300212204181078500703071910703006001e507a4000324010070f2044000221b006000902034162012800c4018500e0020720500c00100750701762080c0d07444800003101001180a65030b4600c061f242c0f5409514220341c1001c2072008a80b450a1007804640c0519141620f404d010220140d14000c2221000c2d62144440e0040745c1c41512035628241200005500040080141d8001d06610035000c108110780c002c2607050a864801c2160040070304c0b0b011000701602200d108030815080424500b581c00701c41d4442c00811a609201d0f0403c980750440040103012110b5580c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 266913974 1250 266912724 266912731
    0x13050915130903081b0d0501170f0c0303030a240b09100203030f01060f05070b0c030106030c0c050304030201030917120403030b12070608151c030908160e04140d030504020306 77
    0x400030300101416540050070b00301300409040f1042135076400d05010101110407140300c0313014424140001d507160a240403190224944080141c8581e1020b80c0c3c40c01d0000c6080b15080e40b002f406542180d80d03540c0a08068020b0001144402c12038038620000c87d64684641c5000d80310540c81d090b1918110028042d404199400d14800d542c418020880041442c10020b419a021460401200c1c1010981035034240100003004080305d441c0010820840104030145040742e295550601c041480600150703211105c1d004003a003072b40c20411040c00554003d40241105903c40ca880004500c450b0011007200e810082c0c01c80ca185040b1400d100034150b0500412182420403600b020042110007800c654420051082c0c0c02404540d00000360b0303100000e6250b540000780606021424400320b0a07072005894075400842c04201c0e0400081851040020444006811003250f40c1c800303410800d01a258050003841182c1425001080e0789a41c0c400784090962007026450204181c1072502c1010708009004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 266915224 1250 266913974 266914009
    0x30708010b151305040f0906020706050f0601050f1803150403020105040201181206050402030c04140f0f090307030c06022106101b0206030a0905070314010606030606120213050915 79
    0x2400a030b80204941c208840403504c0845001800000000200b800b074142d500010b04924808920f4009019490300030340c0c482c241040c81144150b0721030005403414003070f840100000041c184954031985400c01103501940400500315134040702500000002c4030b0b0100c41c1200140d440303809200031944c02030350744081c3c1248440c890b19402d05203101c946146921a4003d0034290b241d03004101951001e000c04010110054818004035281d1408000c030100c0a0b22026030300c1403c0000210540b52403c10b5a000c1e00303032a0061447c03d4096101140c6501c003003001034030459402c20000c03400700192401e40464a40700c0303042030481c2c9040300410200c005400480014066031a2503211440c0b00300202c3c0d01c0c150b504076581902e076111b40700f06600030f0050701e10040240c400c2d07000101c00d00c09c0c107420100141d00700348003d000e00340c0c480d80110161100380c441c80010a40580c003500810946030043e003d0800b210310540040e603034581c0050300c103400a40700c45410300009010140705003014404042460580d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 266916474 1250 266915224 266915227
    0x40503041a0a05370309030e090906040201200d0801080c0f030c01030f02040807060c050601171f0f0501091d03250302030c01020d0b0916020706050f0405030708010b15 74
    0x105018119114041001e02c44182e21040040c0345100001410300e6414825811303510340304650b002400070441200243d0114858050f8010103252a0303140360f01c524007200141c07649460395801500c481c3c8104003101c43c403800c032040c0050f60900400003621001e2050b540c203495545000140c6051900a48249000d0505960803441545000904030b0301c0503c00c4c60001140c1800801c454024002d58001d15054010390900240080d80400c031003034001c0c003c50035990351f81d990f00140b00742022a1800705900740c00000e02d041f4422004580d040001600c02008075807900c02a210b00104d400907003014960aa4600104400307240403402c0300c02ea41d0013a0010751030710f404544203070207020641000010f066031809500d0304040c402d0054402044071103000b5074440945082d880b01034424203820900a007a214005038030949903c050414018080c0c01410b13895003004811606940140b041914403242000001019141048900010410000000368109000d010403846030781c000441d120441c230 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 266917724 1250 266916474 266916487
    0x1906050403080901093206010b09040e060906061009051f030e030903060a0207061103010902071b180e011508100b0118060c061d030a0905010201050907170a0803040503041a 76
    0xa1b4401c0c01806001b440d030401c103180390900e8011044418440245030240500c2d4000140e06030b44101400e68000112000d01407001200344841e900d83e0210351a503c940c2c171620104806082c41a400d0340f0035007142c40c2204015481d000480d2400d1400300e41044910b126004100681d42d2510030044010040e4010f1464401440d0000e940c4010140403080c00319400607400c1c0400204d42d0240c000d0400080d101612580d407080104001d400401040d10401c01c200b00703040444040b0340104e0185c80000c0c50400100f58204001d01c0100020505c40d610341d9619081402d081000fa00d031030b07004044640061000105481c00d0506844041d5a203505000c1e03042103144202017008100000d0301d140340740c820401703060f03070a08402a1113043e6545500465a5082480308080480103180f10344103511090111381d5100012070032903804a6200000e03411492040c49800c0c1c640c00c0c0001000b2030642251007017034194a441d080c070340c0240d074110351a50001034200004e15041c4055800101e51071002400c102 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 266918974 1250 266917724 266917733
    0x411120612250312090303140f030a0b0d020402160c0504090503031b12040c060e030d1e02030903030d020309150702060114030109150f063302190605040308090109 72
    0x1c01d941080701004060407009051980d1512480019a001541030440b1a45602c010341405020700040e000501480310230401070140304112070410711805211855a61180103850040070074062041d0702420240d0540701596560016051080c10904024005252880c240358035400f02e0740454019420301447d80003180010041e254025515207038842d44008070317441c030421340c03207a2017800844500384810f00c030600a10621020036614907480b00d10003160308100f010750b568003800e80c03800001c506040982d807003208441240400803150046904182440700020700b550803c11000d80342c0c590200030800d1144003004000d0b440c031141407042c4014144114000c1d1108014002c880100b50014a4107030703192800d61001c1c0310183c112112034041c100082e05070300035200c491303442c864035400c003507000c2141d1020103001c2181c14401524044c81c2040b1054524441e800039120500354019a4603052644072001c4081003814494003000429240c94600a400701c68060401c9480ba8588840a00040c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 266920224 1250 266918974 266918983
    0x5040b04061503020a110615090a02030f07030b0a0f090e070e1308030601210507140c0c09060105120c040f0b090f0f0f03070303020105060f060901050421020411120612 74
    0x4842c1481c3c050b9481032088803d80d940066085c1c0c807001c62080c0c00402419508519443c08003440444038445c49458441e00d4405034041500d500060082030804900c036540a036003c6421488043c029528069540701001003030800c0c1d81c40040001c0c0c07501c0c1c001410060510a0701c0107044211044407407801c1080e8a0403c0b480d0064005000800010210703140341c0c050b050781542c1052406c145071000c0d0b84c140300c08000d84030030f444c51004120179000b500310a0b99800305841401220b14001c05180b200310042110a96002e0505c80c14410200705401d074881e0380c03d500610030a4490003160f66180ba11103022110491580510b030180c0051205030186c4d958082c000034101c1c812949081c000140c440000c030308030610060241c3c54451810000f04060301900981c0c41488100d40c030303442c2e601c290001e0250511075441202c0c0040c40800051204c1404402c02030022000707107640b8660030180ba03010030f044a42d24040d400316000041002d441d6220214420795102c03c0c29541800c0441c5241c1132103544 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 266921474 1250 266920224 266920259
    0x130e0a0b04020a0e090a02040c02071202062203120f0f14130504050712061505032e030602091c0c05120c0307060f08100e01060305040305090d03020705040b0406 71
    0x3540e0a480c085001d42d51050044809400d01c40749001d06410f29030803540d9107164101c2e0882c0100e00749920a1645400840c1c451f080b86d2003000c080d40204201d60803c11180d001c2c40031011610307140780910b02106030a01c080d00c055803040c000e11402da0100d6801800300e520a6030079008210b110b28000c1c0d51141d016803450001c80049503100d8a0312407640541071070070200c1e0070035908a482c00e001c12258030351064901c144403c8990040140688800c10200042c01240b4880007003001040491045128240f0200c00c1e0350a001420320a0000031104002c400032550040d1030303040d0040b401707455a00d00b00d2040960038100c036409088030b0800355a001c20342003480c420301d4403c80d200c50a0708111007045c403a0204655004080d01c100c2c54495401070260000d00742d5540010310240c2c000f4010203154540d4105481242d40c0303040e916071070180102d024040042007103041100c1030060101a480301486410b402e0700c2038010b0100203003420248400c45200c00a2144a90304102d410002c82c01310400368180c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 266922724 1250 266921474 266921483
    0x6140607060f0c05090a0b03160503100f0608010311030d0e0909100905060115110c040b060c0d1709010b18070c0b0103030e0306161e090b120105130e0a 67
    0x2292651030400c01d000780201c9450012007810070300ca0b072903015800760060004000444c1d0380788031241c442181507214002103540c4007070708074800c1107005404d01560207550701111590501d0469238131400103400a4030a5801100454130100050041040c261510200300e00103800a140004018034020600701803240e001e80225550004258944002e100f4549220030381c0c0d40c1480111b420785003095440509105400d03482c58401c1070a414030b031013140007020750303000c010040581e44065002c01c002444914503040d44a1001c100c03280d60700105008030b51aa07115500c4081c8404c2030514910300002c0010080c030348a924125a0064568542c2c82c260a03403242514415003690b505003090b01d000c4c145107005403440900b40000020160300004901e09800250300b82e4400780c803002d18045002105410150101d41d007414096080308140d813a402c28140646400c807070031a2760300d503044040d51104608504400701d03d0010300c15400c0c0340d04411343d01484a202080301848039240c0f07945480490b24010b2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 266923974 1250 266922724 266922727
    0x306040905010b061b0c04050112060e100504050a1110140c1e0714010503060a05060309010b130902120303070203090d03030f0f0603061a011209080c06010303180801061406 76
    0x1d004095100b00d8080c01c018002070340d90f10364110000c084c99220f69000b680e910805000f074602d410540a500d04941448603084e841504590342c2c071001e4200c00b6240c0c00e01c0d20500e03031700c050104a03501070580900d00030805410283e5050422556092000002c0780c0540c44080348200002c0e4442c10b07210306490160262505c600152000c2420412041d44002101100d501c212030304000104500044400785034011083e0001c1030015100d81c041210120340c00184403908100030f040000055510084800c000180190500c00141c0100c03517200c80d24203c0d594a40c0b40200b103042462030746010450043c019410b500c0d09401c001c0d940d114210b1080e003d0240036000c1420140290015100300e0030310b600602203070450441d400010b00c4184002d42d01281410b221800107240443c3d580d02848060356061380c491540301e0904064840c102003200c011000700581c611150042c80b600340694402e03510448c1441d118000d8450b0501c154000c081030342d14000c010041203000c007000c450460b800b5518107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 266925224 1250 266923974 266923991
    0x1801060806062109010606022a091e010e0702120708160f08030406021c0b0a05012610060806060412030c02130f0903090605041a07170d0f060e0606030604 68
    0x64460780f5100800582074151106101071590190829000c3d204250b00b00c841c50850b14480a2081312800411045010740c82e82d16049030621514042d407007401880002c0d40c9540641180403010400d0340a40545070889003030003456503050142175100d404c04c206c140d06010740f94881c07100d41c0c8683c9000e61484420040e68a040183e80814042104c0d004440c1685a251a0400e003020390b01c680c1000c1c05160310480000809052480b4411000c2130291208510740d0800c0b005550f10030100350a203002c619050f0319480060b0a503d41203100c0d8511442950303115142138000f804007080640a036100c1c400600c0284190800021005c06103a014030708414000d902e8004a8409100c040e5294100350810505030b1203411690440000e42c0c4c841d64803041007035078504044440340210b0090803240040d5072400c000201d8407101800f10940100c0c0e010070001240491254180c2c00340890303408842e181e001c1d21000c5000b91250300c00401403076008075001d02e48100003881520000300340511a5503100c210 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 266926474 1250 266925224 266925247
    0x51e0f04062705060c12040b09030c100f06172a100e09090d020304140f040603051605060405060415091a0702120d091211040207060b180106080606 65
    0x182c0071500d01d0142d640c1d003000c01e419407803035003107040e00060f035951107040e02260150702e02e5003c030b4241c0800c03082841456143c50396034250031100a450a0042d21050180601018050240080840b410480099400390442400080d15151b610020041400501e55502d1110101d00142400c507154561009031245d030700c113001000c8c4002c0101d50860b840105242400c0e030025404003403c1803c4854480d04d03542c07100e400d0368606014a90304d0042c0c0040c00b04000b0441d41c1044440b0429005100b00040c00c2c04801090840d40c0c0d50b8000c0e94254402c0d62401148400302c010340010300810780e0180d02e01824140890203038465031042802c01140010042201803003212078001800148281c018000e06d0700101036031070b40000e80182d1165803520500210700c1c90004400d03a048001743c80d03d05155182820610840c000c020b0141c0e072141d02180c4140c2c031503840e480101591481000e0009140c10090240a1051741c0070b407240030741000708030050201a0300451801d500241c211029692140002c16 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 266927724 1250 266926474 266926481
    0xf080c070f090f051f12051207030206010e070539160602010c080108120901021204061d0609150c0106081f270b0703140a06050103051e0f0406 63
    0x360201e058810000c941d011554003c00c0350129109010b00507030300c50301c10b203071210a61140016141e00074804c0400c5240100400d12603131707034002d00c15550400342500740c40005c2c0c0d001d034000b100103030800c6006008080c240786500e60845014a0500c6c10141109210501d4801c2c0d4050721001d914090090240c042c0320f00e01d140d45854100b4140ca040300d402d000134002d000765030300480c1d0142d424202050f21080c0704804040c100d42060000304001d042d06e4240e107440360f1080c8800c038118025400988608060b601c01000100840e54510114199a482c400800b6205100c01d41c4250000c0100c01c0d880d035203010026070880030100300030f03a54054031000c407801014242e02c03c40f8203004003941e001900040c80145c07448002c2d000070a00c240b040d0700034001c0750101a2071204e400c1ca500004101c003c22100c480c050740c00b4182e400c000541c0000e41003441c114507012100040040d464282c203000384c1d603150192642050441440000d942003c80405001070f5009040100d41001c010003d010b201840c1c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 266928974 1250 266927724 266927729
    0x120307121b0206160516170708070c0602060705040303022e0c02150a090507031707020a08030310060801061407081306080f011d0f0402180109090b01050406030f080c07 74
    0x4030201c4186149603020b5201c01c011201c1030104100d15055808040c0608100d6401301c1800da00e0840099059071002c0860507000300340c00d20701c0010700c041800a80980010a0b149000740d014412251602c00020b161490003854841001002d020400c0020703000220b255041440c14074a11140d01c48049580145061104d49541d060804000c0103040c3e80204003c0c2003101200080c00840e40d8400325407040d183c0020000b4510b83c4081000c10204070f14405400320100484005842d000d0b03913400045030241c00e500f0030b0384d840d040001445240345040000e04000c2206d0f041507851903241a00c0a4010030b0b1030003058100580c005400d004112104044030501c280d40240b9409494035410020410b130f0301101c1044015003c03800204003900c1907006d20000701340401d1000110b5031010302c0018204030150040380c01c40034200a8110300b030758010307004e8003802e0b40301e100150703018507030810780c2c20304006030b0213039003d5841d040041c0007046041490010707507a0001c4840e0383e81c50100707501c1c914000c03059 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 266930224 1250 266928974 266929001
    0x706050405122116020c0d140a0c1d0106141c020d020304022409060711121b01080f06010302030c1201030606090c02031804051e1f060212030712 64
    0x16403401080340744101c07030038240403106440c446a03455440400e030f12441d1206901c096803050507505014070341242d10361f00c014801c410755500c16054519645c940304030048104c5003184c1903441849114400041c072584000c404030400002c1d41741140c00740215400c034002003416403000030f00d03175013401301c3d020010290340d4030403030443d40d982c03d00c07186000a401c140c400320320550801d040b030024003103401c00c114005612543d100d450004c440003003142a40c071102c1c0032a0b8250f00d48601d00c00644e54081d010307058458080181603c00b840c4c1840d030702c1c2e040f25842540d050005400038407c50928945000e54040c03c02c2c00d00603640d48560414000d280521090101e0130345480c3c002208220844e0007c034103c44006006000c480203128080c1d8032401801c48030304510740104011011841d094215503005203450360a000c841c1112120003400e14030450b040c5c90610b2090894002141040d030b0070038020a140d102404101a856000b0446484064400410410140d68604640f10300342d0188100001c031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 266931474 1250 266930224 266930227
    0x925020c030604060501050f01050301140f041d250b0306100504120305040906170a0f030302041802130b090d0311010b09130b010603020a05070f050a0b10090c02010b06070605040512 80
    0x1131030103130090320003402840d004d64a810480d00807940a40c05807416a4103400f4029004a20750082c04044903107440f0752580076480d4001085034140d02d60342048500d85840251060341d43c4000084003031003502071507009118085a04101c1600764400703480d0000c030100c581100380e45684004588034087c13504031840001030454201c04140d0881c00030022a4404c0c50103010556a0b50380b0503212000d850200081c1c0d4200b100035800051045001c00740c0c55109060042c00c050715a54202d5818600301c1c41d0728a11580010040c60300c07103124420600405040e10400d01d00042c280201c2c485000e61000107040c00391b000b0200810b48420f4004001e0808040e1510308145400070741c440710751100c11001d07a8200c60801c0042550382c8640202d0b41d003105035441c1c8916001d070b03a0303440307542403e4490300958803405003400300070018501c644203d004581110f40c4804450400c1d410b00200c4000c0c16005055a01d0851100c00c0d03511490165408950000e600086136a0780b42070180c2070001504103036288980 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 266932724 1250 266931474 266931481
    0x60a0b03010e2d04150912110c040b030316050c0d12180501050a05071403031e0a0203040f120c021906090503060103080d0510030f110f0925020c0306 66
    0x80c2c0da10490310030660b02102d071070800c030000c43d10031188120841866102c40e4003000100440e0399084400050038140740300065100c4c0760b40310403101e00002d00311100007981c00b800c8003814030401c0260015444007141c04106800030400080e5681c401c0f4581500241048030b1a0350601205205100e00034802600e0a030100c48903140c80712080c2c102c0c01050020418640e000000c0c094003c09507429220103031943d9143c1080f000c4280e0310790f046440200c0302e500da95641980b682c0410b0000d18051610020b0b44401c844080d80001d04411005100402c0e0920500c00c000100d1020111000400e40220340e010003240c201d02d00700d074803e0b4102c0d000794008000c10081c5010f000c1070b0401c40210790701c965a060a061300d540c20952100e20070311025025140a008101080c8074541c401c81e0003900070b0034a05416a0b40390746517a40c0c1403011a050b250001c080c400003410b420010141109448100c1e185d454a142922400000d009248000c00104142c030120f441c8940c000c004107291400300400f01c802030324 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 266933974 1250 266932724 266932739
    0x92202030f25090c0f05030c04080f060a0617060412110a150501121109060a0302030a05060a050709180b13090501020316050a050a111005040303051506160209060a0b0301 75
    0x95400700154840401030000045550180c402c9104c0c80300305656002d5142d0080e0021665a00044d00c088400c1108020005601da01045800c15003100c0750041d020130b04e4001480000c4840c03c0d07000c0c08808450315440401c044010403150341c800d81c09254a02c6059004004451441c0f4041e496202403040d001c1c10410311190901c4040c288043d100284066a00c40d940c034591400030503001000d0015000c04d10b10b05113004030a00b03a004001504041c2016541c1e00081d140002d003250036200341d0042010b00c40076142a0107007a0f480116402c0c084400c0b4980041a01c1b911481014000110b0391081800382a654101e00c86025a8046409012860950910302d000350b100f41d0f154006800c0c0f418030b9100f00c600a5080c1c900c00704e901d03180c45052a04030542600c0c855140c120502e901e006004007034030b103004c04e8030540f4051802960001007516000741344070700b0320000085a40c40f6440074480300740910010015220100d5041d40c41a9454031031b500894103450194000099020000c0004034558 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 266935224 1250 266933974 266934013
    0x1e18030c06020c130b030c06070602070203010618050f011202041505100f1d0105120403030e060a0903030515060f09040204080703050c150f0f0307021f0e0c092202030f 74
    0x103001310f4005601d4444107502400300c503004024250540c001d03004114461509101500b0224020300e400340c903101e02580041e084a1b20303908074840d94542c040400c1d40d4560359214081d4050300b0001000345550400c1030b2240307d0318400301e00034403a0352a106208010b0340c41408410040c1030150a14030000310f22840a46111210541540000d48148400e03001003003c42e1224030355481a15120301d40200d1500380c07503030308030010000d6041c1a11103d0410502e9010050b282c442c1c1401d00002a8601c89450000c003600c034058800540684490003c45041e070741c09007210300071808403010701d40d12410240864060302079584107260500422000109009012070101074049044400054451000080c0d02d6640101810381c0409003040c00000c5074150041c00643d000030141c0101e0740c0922103010001c1044140007103040b03029441d411407401b401c0b42000352a50507002155540d2140c544048810740e030402c08445410f0a0b0600901d03d81551024806500d504030300e07405a03200f400c9a5031002810 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 266936474 1250 266935224 266935243
    0x11010c2c090426040e041e050304060e0f271f0f08060601080c0405060a090509100503100908070f020a0e04030302030f0109060617060406050a12060c1e18030c0602 72
    0x5441c850303100003e44040b0042150140d8000c220b003450705480d51344509211140c9050301d025500c815019003800710714200041c00c000c101950b51103405109034403c1c002d90801d000c18941c09078440007401550000c0c0b100013005442d032108240d460544e24515284a007800d41100c401c640d0034281000314800114081c2101615110400c0700d59030b4441c0001190818821500f50082d03000030b010901851524100500041001d46460888180ca400008000078002d07502c2007202040380404102c1800c00b4421166500d11942c4100050307000c0c0d4035030310075600c0780001c02055803001003862021503840300c1d0780001074119200303151001d10b081d1402070002d501c240d860000b07840200340009811003580c010041a2440d50b40e0b5010025000c0722401034500c1c4c090503050703001d9201d4601240d140c8415a4035002409425107458001200d4140401143e42e1040d85030208800020350700e4000603450403802e8461a02e24251220070850345200001c804181c0009040b0941c9034000502c859000490b59207 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 266937724 1250 266936474 266936513
    0x4020a121b0503060702061305033a2706061d04140a0f0303020307020109060e030a0815090c0a0e0418051009170f1903020a11010c2c0904 61
    0x440740d40795010980d554900300e540720011785c0414000b41d0007103210854807200500c620100d80c10035000c40c10300c0b01c1d01d0414044600002201887c0184100c960842540b601041010200070610700c4503d0341c081c0740d803108512087d130f00b0320070b02c034208010701c0c3d9001000410340e4540c200c0010361030007241c41a00205031410781d07101802141aa00d42c25002c501d145185d64403072201078207890b042e0b0303058001e900000d040100359580d0300242008201907000307410201c1c10b420090b40d994007000d40042d0410001419080009030458561a000e498440061303400481d8910026140c00d1000000c8810401c42d8114540260502800111001c0002d454060350f0f4071400544900c1d0f8401402c140446202039030141013404010981426020400c009110b05c00480f10384904d403030404602c403851180c08100c0b54000130740c00035000da10941d202c10f445000c5124400280722400300040002c0110742c2455403961402074610f072502c401604282410340d01040980314408601c1d00341015144480200421003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 266938974 1250 266937724 266937773
    0x9010c021305010312050406020d0815120303090f07080307061806020c1506060309071401090e0f090c011704170c01090605010e0901090c0311030102131503110c0d0804020a12 77
    0x38005800741d82958262566603000300405024403d082fa075002c40508903000d412045108541241c855641174061101703520300560b52402c10100315868040312503022103c1d80c00c2860f0600036070102000b11008950000310210b0504501a410842c85840003401032500d40700045001d405040807811110070b9000c45000c01855070761409100d03492200311400f90054016410900c08074504104103401090107141a101c411389860109444840581c3d01e10b0300040c1d0760742000b000700410000000400405e107004000680440626010100081e100030301455002509145080703001c8240c03070105a45500903c040070641c00c24900500003030165000c40e81102e4001246c0d4441409000d401c00e5100c0280040c803032554641c0000801d482005075450b540030004100c1091000c500d600140040090480c1a640344038030107011100400d011601b0070b4000d1003510210702c0e0100318802d0020701814020441e0f5100d200144100200d9001300c200d0300c452035450030074800028034110251001c8076141 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 266940224 1250 266938974 266939003
    0xd05041a10090f090201122007142e020a0201021c0203090714030a0204051509040507150801030c120309090c021005100b0a0f02010b040603120215091209010c0213050103 75
    0x100c0030b60b40d00c25000b0f804108049601c40110740c450303000303980d0551341c000b54148a60244403011b0880c1e01550060303410441c0e51002e00040c01c2c0a001d01e0380000c4245c1140310b002f00b8000c00c0c00c3c4140e262a01d11814030390340840d001c6242c81c001e404032402c2c0c0c48014240100d140410000074000e420903540c001c801d2080f42c002180c1085031031740710130261000800a02003030140307500700f00152074010502407250684603940030582d12900d40c028092840b8102030030303010b800c00040d45007001200240008000ca1040101f0111b4203c6443c2030a552080150300d80c40d440703d007016180580e043c5d100204451610300c0551030a5808038140352040250202403220780c580c03030035100e2100124018404107080420140e60964001c1c085106146000e00000c41d5409190740041c04445a95206030395182c008031400c1c01550b41805103091009690b0402d4490b41002042d00d170f92034981e85509600c000300010050081d030f0060ba281210030358000c04a814440c0380040a101030003003840110307050305048660 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 266941474 1250 266940224 266940251
    0x71205010b1021020f1204051218041107020904080a030b0105190305060a080712060c260c3906040b04060b04020d1b0908070b0d05041a1009 62
    0x221003200c2c80355074641640c1203200b14034580c0e22425000d22041c0b554200400d004985003031300174211540c0c01da54440394519040c24980e082003030288400381a00c0081117114002500c9150307241182500faa400920721001109c042a540302c1e505000c2d501000b485c01300b0040100c001c00030581d40f10703190740502840641b41c0040d281d0b4010750090202c01010b2451006c0f26600c240d00c0140c1c050b4004003042a02580d0b000e980d82010140d800c8404610000032044047c40050f0244940440051a052460250f01e00c02140320310302004540d86440180c101060031030303081c24241d039207801014507403000c0304005212803907002c029500301520540002d02e2201e410340011481500c120b400040b035902c15600c65032460020494861903550040d424441e40326494158401e00214804082900c1484403900301d0140484102d584080401d601c45402888440310500c1a0340358400b0002c800304594507946410030381540c1e048080003105103c030007002004544402400204d5041000812400c0302e065413 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 266942724 1250 266941474 266941489
    0x90605071103040e0a051005060a03020403060c210908130608162102070611070809190503070504091511040303031a0a1202010915030204030c0906150c050f071205010b 74
    0x10f01d44c4141005002400000c116040140e00000480702010501d850300b000680700d4000c40d05a500003540401c0900802495110350502d026035420000c1010045400c01030a50141101000c004d644803c044810018071605441c04030814001d030403081620f42d9001003814004503030f00500140a21880e9044070b00800c82d22102140e41011a001c102144a044002e540089000c45405607900c0c0094900a0a40040e1034402e11500c02140e89144041c00c1188051f03030440700107060700d0030403000c22603a6800600c0c0c1c000c540c401d48021030005a01d051205500303910513990b541d070310b0504610000b0003400034020710950b8400d4030208004000a034039150b9106d1a440e14580015098100740030030342e200700d20421614030500d0000700241c3c407209941c10310040c0c061a240400d4020406100300b0000300495400f0b040640003c00c0100e01c3d0890034950300703201a0094042c0020580507400740a8207110000d5041b982d0000c84220b00e5440c4504a000c041d100f400340c034075510f40410306a0030b107003a61 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 266943974 1250 266942724 266942729
    0xf050c070b06010807020c1e01020f0c03030a031802100804021504140f04020d0c260c040306110c03030403020a121805210106080f061f14120109060507110304 70
    0x81d0300000e10380c0e0303000043d030f0040c2025100809600c1412155201075550700303070b403c000700c61f082480541c008043c40060310300102046403c6040c1c120440011443c0c030004140c0b4401d0109150114119560510310940c1c4040d0b404040d40003134090410b403800755042202103009610030b450541c0c160a01000a11050040b03000b0840c2030800e00722414034510301031140c0d01c04801c0052005241900303000c04442140c122440d18404621200d110191564040412410b405807016041002d85000f401e60070b042c1c40f59000003050540d80b080c00750b40d90240403081c0c60028080000f2641e59041c1400c02956605070400d040728141201c0d0380441e01c0922441c0b20716401d07212441701000d50703410402001328031307142c11000f03103440c0152804191256009024050091180d040980141030b6102c3c81c0e0790820f14003c0000408079100c2a01000400c1055451011030f07100010701c881c5d0300c0d0001c00044003902410300f4404030798208503540052084030b92015000e05115202d8040200002d00c0542c1c0307074012403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 266945224 1250 266943974 266943983
    0x6050403050c0103020d0b0301050901060315060b041a0702100c020a0b0f0304030804031b140609071203050c0c0904110a060908100b040e0d0507030e06030c0403060903031e0f050c07 80
    0x28603000300b1540290042d210840c0e5506011405a001c040442d007142c1c012541d0409070b80d1108403c0040c00700507001041d114506820901c041c0d818401c0f854000d02c96446410603a4030b00110700060084a50700351440c0560091134210302d120710341002800310101d0903003070b032081c0410b40e00040c0300040241107600c02d420b012215401c541e100d0f101a14031950082081d4103008070340100a04c3d1a040c03038100840c807031140d100f181c241c8400a4006282043c01000d902d002d5000e00e00c14442071911565500c115607140c41c08070382d2150b11419450400740c200e115907800c085484240701c1003055400c0031030f0001c40140ca030560020f0740c540c0e00719407040c440d120340c0140340c1000003c0c08140d842600302900c0b0b410003801c00304030b900d5141101442c2c4a0660075001c00104049900703401c240d400a59900400401c450349030031810903940d8a00903100e1484001c002c15a1140c0400c10035000b80c0043c50020751740709020b0880a88001e1020241940412100006203004c00017031010a00c54191049642c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 266946474 1250 266945224 266945233
    0xc060311090907050a120203130b09010b0102071a13150e090105010e011d030616020d0905060d091401050a02090f09012102031f0c0e06161209091d06010605040305 72
    0xf0542c0c01d42c0c1d29808800702c0c01c20420745400e41c2104481c4c40c00118041ca141c1500e91007617404909002d2840703403000c0c041c032500303904290020362241e0303002079240c040da44c8030208140c00496040090117a88240d00c440340d10034000400001d01180c00792102c0c001040680c54100c1c0651145017003000100090140902180c00386801034040d51044241c0b41e55100030071050f4482d00540c00000e45824822a1200d0582407070100070290251b0501041085200c0d608102c5501381c105400160107001d12600c140d1041d40c0d403400c1c6028081e1003c2a440c05142604c020041030400f091740101070342c0400c0c8002e004100b82d10180190b0704141c03c07030604980511206000d21491403c0c65008184600402d0740d042c4614281e00c40317482684465a0744460070355000080c00443c5c56000340011640f806030a108076024030a44a4040c040140320307d68950203040803450140300c0f82c059991040035001695403600c0c0030040059600301c010102e0120000340308440040ea655003003114140701c0c03808020f010303811 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 266947724 1250 266946474 266946481
    0xc0b070305010617280906090b01030201030e0303090c010503041109100e16050904023105030105060409050c01030b030f0f0f0c0a030c0b0705030d050406051e0c07030e1c0c0603110909 81
    0x80c2c4200c0008509581713021540c0b094540f9880c09603030a03054141ca0b1000c0d8171004000715038140c42841c0203031708002d0207503003149071186001e5112980140714505200001000030200190780214031108200106020799070304100384c4801000345d89004038066101c1a00c003080d140c60000403800c0b0026440d039960f41c5084a5202400045e42103141800f90f00c4041c0405080c0428206400300c91003000d02101c003012a25001c100b509441e000380c0154019403601d00d1400c0456404280700e40095804e080200324841c800020074541852401e0300301203400382009000c01e050703020a601e1050b2001e10704407071410b04560308118034000d01d44002080f400303281300c0c10000c000c46580641700e140d009070185c0741440b91502021342590011581141d4480e5030348100304840240300049000065460b91710029440c2950150842c3d12440704d001e014403d2104800c03140341e47e8141160400403520110801c005000d240181500c00f0500860b0301180c00c3c03616000c03c1c0038120040d560031070001032000c1d04584 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 266948974 1250 266947724 266947771
    0xc0f1d0a0b210106091103070e0a0308070204051003080f09181e0a0e030712020105090c01091403010b1f0813020109032a03050606010201060e06030607030c0c0b070305010617 77
    0x1100c1c02c2c4010082d500c0e1240051009480e1180380d62a107050103840b5070764900200000c10b1004070441c0144101c03502751080c408103081c8015290036a9040c0d60001d559125084080703040f5801d90b00c001e22450000a5403d0f008000002420852000ba02c50080996540b143d2000e0300208840c0c0c03585078800b00c00c00541a8041700c0c0c8603904800454400541c482030503030078504641c0010320a83d02e102031009041b2696038241f04043d407114410b0041c1242c00309803c0001d01c03180b220b102c0e1a8000a0700030003094140c2d0f00798064900d51200901858540d00001d142c0444841034080b00b902040e00c10780050310344600c40303181402803941652610303145825950342d160304090070291540c1040050414501e0f034155142001c000e540144010022450034100082c02d55001d6042045090034400034022544c50000f0700b15000510b9040c0845c00d58500d8804454400b898034000d0518150441400440754240c0d1106060b10003a64981c0726118210044040c140c000b40c2c0c064030340040001a000154 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 266950224 1250 266948974 266949019
    0x1801030803281418030a080106050901120911040b0307031e030912030206090c0307030503040506070503120f090c0603090d140903010204080304090c030b01020d0c0c0f1d0a0b 77
    0x300142c400340c05100840c0140070045404503851800d00c02c10090134031013102c0105212a405036000350055241c0700300d591000b00009018481c01003485804205110140e01907201d40d24040110f54080004c01e032582441c0c81d4084030719003403502880c41c142e5150031609020071404240c98020032040d1101070b0090580d40785030680e000580030001150b0740890130140000c20041d1040c020390043c00c09062820483d0f04082c55007248510a0703010001c10000104080300351412541c00321940d58035919a814410704621a410103400284200c404002902e02d101405d0350150a5420494090b54080010b10030680700c15603900120b580304044000010788501001d002c6c40c000d40c2c400904150455000c00d0a90b00103030860212a0408103092140000e244240d141420782031409220200000300042d4403801c0c60a1038008000ca861480401d02c0804c511040c010030700c240d40c0c4c4070629503440725403200944002d20340040c40711644c0810603503000b6008840f541803004007100c1091451101d0341c00c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 266951474 1250 266950224 266950261
    0x150203130b09030a060504050c0405060f181b0a020a0b0604110301030f020102100e0a051b060f1e072018010603020a1209390e040f120504051801030803 67
    0x5881091342d203c001034004e0040a001728482d0008090040000e006c10043c1c802c02000305005125010620320140e651940f0f00140141d842c4200c069901d03030009044031000460300543c50305500003400c3e81150760000f140001103000c5d102c4521684c0f620780801003520f4008a060804001c00c1c001030020030585503243d150f40d44140101c640f080d160b02c4066007034072200000301030544c02042c010018080700380714005981e00501c94251292000b200021160700842c42840301808000c644c080480d103844000501c59190040843d48551540ca050040e04d00040c7d5008840c007200440d1400508080c1c08041c00000f11182c0c0c4007042c3e0a000b400c400035041030004008020000045c0382c81c4c2c946034441d10f41d5040c044d1000e180c103000b000031949001d0400c9107180c610000300d00c80780c071504046540c020081d91060840a402519641003c0e07284520821010f41408003480e1203040054000004100300d94080d59000c0b008003901691825000092001400c0803000f080018858140c0c01004c2c0003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 266952724 1250 266951474 266951479
    0x6070311010b03160f06140d050907030f05011e05040c150c0c030c030b0105012a0c03021807091703040b03060103020423011806020d0f02120a0306150203130b09 71
    0xe4110320030380041c4c40d00128040440404060603014002c05407103c4860000e028181010020051707209103c1c24944140018019003603074400114120b0740701404194003c0d030f040f8030031450700708031824214000c118082c51001844070f04845207800c001c440c040c442c400c0703803c416100e2080e46800c0303560103000c0380100035a08205441007500001140440c542d0061402250000b052a086250203264500182c102d14144404080c084035001900c5803010b03d0b4054500c83d5094000c0030b8030b4021040c101ca504002c0d8000300c0f280280c00700c01c5582945c0c61040800da52104041a070300d40b4070103a845500800c14802c3e8004100501011100a000b036030030034010303d801032402e5901c10030f102e07500051400c400803a4034400340c1c903a52581d2000c60011103001655225240754900701c0c000c2e5403035250542005c00e003d00d50b507400410300c1c024000201c0b20b0303d000c00013039a01d84501c48004c2c001c0040c1d0080014210791140900c2c2030a200000780c40010407040c0b61500400d0030102c90a103581c210322110380c0d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 266953974 1250 266952724 266952731
    0x209071803060b0406050405061e03030910080703110901270503012307032d0905030c01060303021c1b060204030c0e0106032a0c05010e0106080a0b09010b0607031101 73
    0x420492a80303404002103018000005007400400e08010680700280d0005200e1400c190030f004841d40c4c1c1d55040344050900074912403480548001090a41c0200c02e1001c1d07201100c4d90300620595042416144118000d41d0204804c614100d402d4040340214040b1500003510302400c07440e070610000c00d000415001c80b4510401d5039071000000d094070b2140204603001c071500b00381d282428040e85201c0b070300f1803c0380c04c0034030500c0031a1801700c0c1c108168800344041c900264051003154442640a800d055400c0802e4039610f2100680b41c034082d210340e120480c014458590308041c0302a81c000340c0c03900f41c0300581d10440b0000d00b0a0313140020116801c41540c200342d08001c0000043d50b510304c071400400e058200d510180d894800040e088030380c01985c1c9085901078018200441020321016a1000c5103410111254915402c1c41401031003071841421543d8a00392020071b8000c0006030400c203051041d10b0b8013a60b655103403421426128034444184c2c210509106400c0002d000c1c1c134251111030001c50001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 266955224 1250 266953974 266953997
    0x603060e011a041512050f1b0f0402071e2904020d1103070801021201180c020a02090712050c07060c090e15040908120103020102120426012003190605030a020907 71
    0x200030048240303004407419403040250b070741044801e08c00103080410264154070720002540208103c28142c400403445590300184010030407604007442d4123605c0c01c04241d208000d141d49461074110b0030107102010100c14541c1d08201030381d101c08101d0720541c2d001c3c0c01c40e6030312030455541110410b048421175515028011010811080034809004401201c030701c00704083d45000c04440c0130082c80140516100e05110f08507503620703000980ca0030204d41c182c0340410f0075540c516003110b102001c901c115402c9070803e4284004581c0c0c0101404c1100c1c02984108900e840001050342d0b102c68501c14140401000d0001545d200e00160004000030805000418030142640d61000d035513118540345d40728009800014030a55904015011503502d40d02c5082d0719050400446501b000d001d07030781c00300c1e040540410030181404290040290b210040072058100c68507400301440c690000c8800d20240400480c11042c446141d014503011240c000e0090312194a2940034082e444600804200074401c02c160342 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 266956474 1250 266955224 266955239
    0xb0702010c1e0803150405061f1d03010e010f0506010c05060103151407030e0d05040f050607020325090e010513080703020705100c0308010803181207030204020d0603060e011a0415 79
    0xc600c03030310317041c0440080b280c444010082214400b807c450702440c49080c0c113500e40c007000000304401c030400e0300b4107440c5445485022140311000d08082c9400d9428203544850007801500700940c440b106410034401c3e640c070381c0011240040142405441a030064004101044100250008051940c1d401103a0014450359020a250040c4d500c00d0000c1c0e502d060340700d00c000c2e040c0f107048074041d0285001c3d441c043c548036204040c83c006001c1d50b4402e54001404508558080126034079100206968a92500c031405116899117800d104008102c0d00740044003400c0341040c41a203100c0c07604034102c85161509521403040a820400084080d4802d034070740131a080d44c0e441e00955106a4540d40c94101c05003034070b001403480d01c041e0321619255000380408900311140301e500000303502080e80c010705c1e0780700111115483c04c0e00750b40c0301a420a02c006005001d4824581018065034068041400f810683d00c030020b00321405403085900c40c1003003107d2014189090f030000740d944110030204801580d201c441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 266957724 1250 266956474 266956477
    0x1407030609080a1b020307060f120c0503090d0e091902120405010b120f0d111e0a02150a020c0f041508010c020715050d050415180308010b0702010c1e08 67
    0x201500c02d840041586506543c1c0300c105400c0c22010242c0355000410554042541c0c2d100c980101814040c018800082c01c5105048094a842c584102070000350164a805011a407081d14403081031f000d001e81d0841c1c002d000b0b000200c40800084d1045041e95a001415280c4146550b40788100390b800b00040542c0e4481c50003010300a41c05580001801261541001070160f40003440045941010681c2c0309240b60118071003882c00658113100c16109803c0b481682004002e43ca1030b00e50405c3e902d01c2c01c15041000501c0541d00b8801c2da19500c00724484048a1024001c2d6069440168480303000c041e0141005040601e400d500a000070400384008204001d20812a4104100e0344c1c0d900d0420004007a07041182c0f00040400c10f01414018560303d00040035031144003003d2a41989841c0814104012220001040910541e01b04080c44003d162190758521851b82500012050030005c180b003003c032800c890030542e0503140c0d03084802003507450003d40c00c03107800c0d4110049180021180071904030300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 266958974 1250 266957724 266957741
    0x120b0409031116050a0b0906120109050603070501080108191e0305030a0b0a06051e13060f0f0306180b0f0414090115030308150f061306020712020d14070306 69
    0x711081d04422260720041d03c3c0450001e4000c0a144031900d00704a1600c60780c0f00c100c140c0d1100300da11a40d850044000c655581b0680002500f0036021000018000446038001030080104a0540300c0c0e81e0f076184c0044846400030700506c4500d4000c40c185140c0a141d13044441003680c4180d0161b0002011404280070212044e00d0944c0492000020400e80e00018402c8030316210084600b107042c24102034008101b4062140c00c10f1444960707401e0b84984110b61000d407000461656603080035551200320040c40201c0c0b1500050110759498242c2550714064003401003070341d42200d03008502200030085079001d088040d4903113410000b42841e03984c2170307125409441c4841402c44074a60050405a4049084810040043c4580d40c121502800002c0d40a25500e0b000f01c0b566803813031b2045000c02c00040f07400b02c1d03d11840c0d41c8481300117114008403201207000f2003214400d40aa4542641d60a0007101da0780d60124020741c48000300c1d81d0758001440850400d82e110f001041101e500c00c0d200d80c0c440088403c450f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 266960224 1250 266958974 266958977
    0x3030c07050f0a060f0f0512040c181a011b060e03070c091b0c08270406061701031403041a13051c14030c1905010507170106120b040903 60
    0x80c0d0051006042035041c85058402c280c6600100c1c40c0783c8180140f01e621025050410004964000d840e11031181c019980214600e01c6208a01e040c5883c102c1d00307804d282c2c403d12250b09038101c1d43c0184116a480f0705c400b803010b80606d2820f0b85110b04011600199050070307484022083c2c901e40000700380c0358841d0300890721140300256940c000d581040014a003082d8011200c2d2030401910181c1825071600711103603c6400d0418203406481351400190386d0240164a40c41c89074109665030341ea20a5400c01c02d081c0b042914100715240c0c0b68141110400000303400b40800744d04a200400c0058411038052000d100030a050382c0c140741d01c440c074004203a64003c188511490340400e40a50000300c0b44003400041c501118850b045408501030340c2e20105440401820280003124002c5410b281441102e080007c02d405503484052144001030035000e1600c0281c4241d2f20b0540016511070085962801c1c82e8030380c40354480c090786418811201c405519509644280d2255014070054035240200c1103034612030f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 266961474 1250 266960224 266960233
    0x51513030c0e06061810050705061314010b0105070b090c09010e06150405032512080c07120314070203070f090c0f020c01050904180804180c140a03180203030c 70
    0x109115261216409441c041c401e0300100000c0403015a50645e01c503078600162030390125180d242c001540d26005100d0b0140850003a003007041061014040c2d410715161084113207442e07005859074414202d030900540f090210b80c007002040085143d22000961044080c01125802030400011440c0d440c0e00303a01086090f4880c4042c480c0700d2800341c24604280721094013082c1050710306070000303a40b400c01c50480d4900001c10441c904010142140400140a06044c030038103801052512145c03903480301d00400d400d402800b1707010404201140030500d905402d9501c0000c0300c0c8078044208034a50110318102d07414413400078000360400c6400403040c000e05a5010000e00d091180d500984013140300c00a007021508201c808198a0385c200c002e5403140001a58001a11769540c5201208212002c2c0050480000441e0000e8071862020082c01007100900b018045041c80386410303541c00784140d4103104864018080c030300340c4920a6000640e14001b1340642002c81e0711680100b802d5500031000c00325107401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 266962724 1250 266961474 266961479
    0x130b0a0519060e19060e04060305010510030507050a030203120c01150b09010f020d02061602010b03030d060501110102071a070203070f150b0114031807090606021b060c07051513030c 80
    0x400001e61410f10320141c81043c28101c07460f1588840c040c2c2070040e04284003d480450030180c4031940700d840915031003c02000142030040ca00c0e401c0400c2e920080b1068485c120010809013040301c030342422241c0c080c0c024070207825424540d448c2604951100700c3c4640d03071010303000705a100d2610024024808a0210350f40c038580308000401c15a00c60301998195480740d14101006540018429844030480309e03441d60b040500041280505000324605a25110115040d1840f00240d40003900711042602c03402e031043c44200040c0d00741d01030482c2c041c00c806c80f510f0150885034014041c0c40c3e4010030b9481520700d000706990b03810700344101204094440c10000c500820410380c40d403051310020b03d02400d24600310000d54414800c1484028001214041da00450311207107501009030a028151198080c1b0029440d035030b0003552150480100390041c03100e4000c11844e030820b2000c0754811381700e880151402c2802d020910851444c4d5040c0c084402c202008000080d0380e0101340040070310b2081d86005400751 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 266963974 1250 266962724 266962727
    0xa06020a11060f0c030901020912070f210201050a1407060b04051317070c15030e0c01030507051b101503050f01020306090103030c0f060207230c130b0a051906 70
    0x882050350104582c840010301660081d008085a4031140e4100d030255079540300341d000c601901484100b01e80100c148440308411850100d80390050b02d04182c0b02d82c0e6130a070740c0c80242174060543e0f000b5a003000d2445c1d06140242d40304030020181001582410064007000c442d1115096100c00c0c0c4c2500d20b81d03594084803880c0d203003600805400210401d0054070b181d0b15a01d0321495400c058081032420180010300d2020011510985001031000072000b850a406004010307000c1c05c01c58111130058000e422140c0025800b0384510390007069036a490342d041c000701100e82c0c418809001c0343e06000e4440c101c40905114154015005820101031410040d1499890064030b8118141444030310740e4014000c00c5842d4a1741c00b0042d04503605450240c21804250030444031002c2000781c041c0a0030300015155007440110b8545156a143e20140501c0550040002d07d85400394810b000c0d5005042d480141c000c006c03030b600700d40219000140040100b03540c80c800141001c800105441004040040c00c010b080d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 266965224 1250 266963974 266963987
    0x203071208060d0c0e330f0d0c0b070b100f05210d0c0b06180606030403090911030402030c0a03240609020726091809160806220c09020a110a06020a 65
    0x110b0f8180504008241c007444204481e1005441c2e20380034107029100e40c030180c1d0708c43c0d00604c0711582024401e0703803132070312003005807000d41c850203041c1c2c1c11840d4000442d42d040e0004140500720b8404810110800b4100070401c41200390100501d20100f0b80941d00c003500729010300c40c1c0034072004a916078191803101c505c0c0c0792622a0b0300400035031160030b104115460407509c03c1d4480f6441002201e035169699500c1c502560040840c1d0418072100703150034044248900e81c00c0055006a00803400c5404c458111002c02000c08014040104076401c0750310140c551480307100b40441800341580e0b000c95050344030105041283c21445054501503613a00302c40304025000c240302012420b0300c4504c14034103d8580082201c01c00110044080e1a1981c00040c1c040c560a00c49519858088010310350b03407507681c511041d56140d003540c0f485140c100c00800c00c11500890140d003680c0d940c0c031140c5481d081d45881c2c4050001c1d00070007540340074025902400e40d0400c40030f110481e00c2c0e038482c200058a660306440c00078090b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 266966474 1250 266965224 266965261
    0x70e100e06070311030403081206040518150907031b06030c020f0c06030c040e0a0605040509030903070e0601020c03060403030606030b060a0e0f010504050607080d05070203071208060d0c0e 83
    0x90003031210a980068030380c0d1049591840d01070402088280420111900e588502d9001030f00c2c80350085540404440302102407809460115814481e54031803008605e516215100794641540c81340802c0310107180200c21065101c02e5000540f400c0503902c0c3c4450303900d50b0840c40d441c20070580c405428400070b40c0ad13100d941401070071071004140c0c40e01041c0c40c03e5951840510054030514000c00040c500c140e4410494000d00f0300c56103003010740d0400c402c1032801740c101e03401024403440c100000240c80326000003d4030110b400040092054510341070481c0b0f61000041c0c505811401107000070306441e103007000042e000d80d1080d1360000c0c4151415000078103e40600c4a4075124510811121900d542e001c0148903c00000312503001c03202c1032283c010380e82340c03049501640c0c02040205000050100c86409000003180d116024081c59480b400220707140d110710003004044075450902500c065104100d05a4045000741c0300d00c8a00d0041d40302c2075014400c640c002880e000800b0100302c41c1c5180310f5000d543c1d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 266967724 1250 266966474 266966477
    0xb03070e150c0a050706080c0715020d09080703030c050310170c040e03030906070e13181509030e0406030215070f0803010e150d0b01050d060f090b1b0f04030803090c09070e10 77
    0x400b230500c031200d40b44501c10790b0000303401e00c04010f03140031582010350f040300c035101400d81e030400543c50b2038a82a40315802403801500030901c1e20307a8200d8158001e10803a4460b0901061001c0081d0030105940c51118080815038214804c0d100c04c010662110710441c001c0304040c900940d12498400c010f540380c100000d10420410001c0c001280464680400b0f01614a600400101d903524400040d1440c00c40040e801070804502c01c1c4040c002c2c003038290f010302550350080e034429203030841100500c000c0c1d5106100c020f40040c40100184150b008081c0a0142944a0341050b42d0b40200c1b40c079200c0168000707810840e000f8062109200c203003003410380c81200c101c0043d03e40029044050f1106d24040405204440c0035421380d107650401c00500c1d60081e51000c3e80c0c090100540005410300002c4440c0c00c56503849040ba03100c020341c0b81c180802060f0707820b4034280500940340034115940d00780e15400c050404045441020000c0513603039101441c680c4201a5650340d1f680214400007006018001c66001c0030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 266968974 1250 266967724 266967737
    0xc0f031116060b0a06090e0c0307110d08070f05040308040b070c09090804061e2003040e04050309010908070e0a0b010c0b0a0b0f010f0905061b030c0f12040b03070e150c0a050706 78
    0xf050702c0c00100340b00d501c10032350136140d0703125a100c4a05899464180d2101c00882c01860b80981c400c41c0c0080003a8080c55056480c00014204030760140c865200394000585403000a00c03003000f14490b204010a4028818a500f014440e40c5141d100700341c0d04820802ca803130101c046410b000c8544d225084d100c5061580b2107110320002c0030301020742405441c45102c40521050002e482200404004840051030b84207055000380c42c040c240252a500426000d6002804020000800002c0016503400780e590703085900c00c084c0c541603d690000d01880d8182d906119916a4030008075602c6030302648540f402c2034000c94074070752100401c04c40100389811036050014034051000340b15404020201524403d0342c2c0b4a5884049081c40a01c440b03d6046611503880005102e0448401c0495650b20840048040318410998050070031010300460060151900c0d0503c0003031007141c03103460000e00b0b81001801c40c600c8076090180e980c009602420701d05030981c1c001c0340d0402c104041040303850000c12807813600340b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 266970224 1250 266968974 266968979
    0x9030d1b06050c0f0f090306090c030601060809070f090e0705040510030308041109011d090307030e040b011e0314061207030803150301230a0c0f031116060b0a0609 72
    0x25211180200c00141065541d0030000c3d040844070801c94440ea08001c1d800d580719004c002211031303070f40d01200002e400381c054000402d22001c0300144064038031070001e014000a0b801d1410481f110030740103001e2407031880760703600008400010302661405061303041c0001c910f03449801c0405241c000543c4c0300f2400ba5240400300030102c2d47c8203241d003040d60b0345880e0000305625107082845480c0803415001c1c1d8410f0202000040203415408100c0ca80b480300c4070036560907655208410f40741c1c060103070043c01007146203015882502d880d600c03640c200801410f142419040d0584003640d07400030800c400000c030f40e0b101c2107030701e004540031324055200c0c3d001c03113039204041c5519510607101c0e45c20744001010314001101051645011007214190008058000c0113070b04500d14024504908902080400c04a04004141c04103650f003c1d01c10584886c1c0c0b203c02039207100c81022001002407440880d5101020312000743c0d04100b0b0515800c05038041d10300801d1650000c801c101c4080010b6000d01c09001400c0c008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 266971474 1250 266970224 266970257
    0x190207030c123807030b01020c090711010f05190603150c09091103040b0c09240403060513030906170402040f0605030102190e0a030206121b070809030d 67
    0x41e0801d40d0041800c190181100c0d02d885a140394104420391100b0fa100076412102038591090b000c046400461608078603290240b040d001c9640700c0b00f1140c0181c101e491490014141046001d030043e45a2505000c1300c0c2c60309000d9402c5810081072151070b03135195414055605486803000da0350b215088010070001e4515540c01c0303c01d00081011015058a80c2e0b4060555030154003008010500c1140500c000e0380d07080000141503100f00c1d41101c6500b0040d010075900551041650012240030b404e105942c01141c002141c210304240e826041a941000084002009405000c1c00740c00c0040708042d0750b20041c0307005010066190059010003030041400315038018006085500716805440c00034070310503021300c1100500000e4210640541c0002441c3c2d2807403001d80001c900c03a85140e900c0780c444008460802186813450b20010758421400c0c0010002120910035058110401d90f40503000100286499a4550021401981c0b40303240030030301c004a0b0406001c950300c0c5149500d03000140c40c101411 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 266972724 1250 266971474 266971493
    0xf050108180c0307030b061c051506031e0a11010f090e06030a0c03030e01031d030d0e071d04030207060212180a08010617071d0408220b19020703 64
    0x5070420588000010446641d0510841c84070107005000d0f0b072510343d02c070300304890580800d131a5107000d0518120300010701e00c0c0c0a40b0068506a00c034014005250300c0c00c80e44060700d40d01070310380e9a07d030080d04c2d40304150044039030070170301030120309005404040d03102d0502e1040d8902074824103040c404040f006040d4298400880000d03121818000500c4e034a40c0303000b10340b0f0b103000920020010305010310003100b4107400c03606054101400b41d07814082800301403940085010407050112455209102d00103a8170300941103005864a10400c803102c040c0d480c0807005802900c01840e03604600048248001e05a050000c07001608040c0001d103ca07a1501d2880d500c24820560800c03510102d824040d40c80b5503a224941c0002c0507804024090644c90b03a070000f10350384014600403110711454000180c0c85100e01c1a8401340b0006d0f00000e201c0f85e450303450f000219400101c10344454075000e01d41e211000a40440710025040c51103100f511540740980540c07041d50b421801d0415944800010400034003c01c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 266973974 1250 266972724 266972731
    0x9020a0303081009140a050703200f271203090d030e0402131401110a02100305190f0b01111f0c05090301050a1401050a030b0a021614060f010f050108 66
    0x2d815a582c1d40d079034a0802c2c0c141403980100701d0b16420003c4405000100f03e280c2d038010001c5080030444c84e200d500c0300340e00f03c48181c1410400d07120b0050000d003203403000d1009482807a0500c0c01c134520b000400c10f525800c0303100c806000040c9050681050045d402d1410860085148840040d0b180c15484000030f80801c005070303030040800c09880120221921603405890160003032400301e808461711481d0031920203050031000750028040400d954104540060140708464019100d4203c0c04080c0c1d008401a290040140c101c00c940181c1c2804001d120788034030031280c08540c1c000128401c10ba0b00040c020000c100c40f5040a80c404a4100d41e124a09000180504050840001c9204007003009540a0080006442d495441e040400c203d1f603029400c00d00801902c0030b6003171060ba80720420054ac68000b404090314a42c99040095044006075000f1f01c031410b44005041102990f540d43c1c40b8644001000400c40ca1b001402805043d80c50b402c0b4040c050b150903445c07015483c0c10072000170040c00004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 266975224 1250 266973974 266973977
    0x19060501060c0528020301020a2307030e1e03070e0406150501021b01110f07080715050d0f090209180c0406080c19030b2a0702010e1012150905090109020a0303 70
    0xc810301045054079560004c0440d03011b0000c0d51604140c050107000c0c401052821031840342014207101e94005044d007110f070001d506896102c0c040b00329500303104825030040c0302c10014880c04007015180c2e580c00c0012a00600408180c03444030300d41803422030240e0741c448082d0103d42581e01d10900240c0e030003003a80e000e141080d420b0420450f003041d0040b40c80c010305145803442c80c007540c145001da6110210354201552041022100000e95911801c0308de503a40426000008005215100f45003c80750407035400c0024014000c50342d030240342c000076908881034603451407401300a40f04211005060000038400c0700c0484041052500d0a6140303904c07901640c00c910301c0354101c400c9030045107400140d858055030304004184494a85451402e40c02e04c003078415800025103861500c10b01c24211012601905d6060395091809400c0c0c809000d2003a1541c00c405041c81031401003480382408a100d00700b5119400f600f212507841c5003000201c11640007402004c650b0741400c18900250302d581c4100001c40350305 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 266976474 1250 266975224 266975263
    0x12040e06040504020f1c0317010f0611010f02040605030a0c09030b0612190302010b030f07030c09051e161107030b150607060905010b10110a11010e0319060501060c05 73
    0x403071000071740481c141091150311880d400c1c018048284010f0000030310b140f09441d40046548500c400d518510000d01caa4004100015030910060344a041c200000000d16800403912081444a54050f600580c01c1000050000703c00c2140c50201ba02402050300001d041030029241191036805004100600f810702440038103401c0e00c000f402c00c200308041d2080c800710201001007145402400b90411110145c847c2c401c13441d50521039500410040c04880d0700c0228080c0152034800c00202410000300901c041190240b8241c008006030b50189100d001c0c1002407001203128144090040d2401c1c15030b60710f0581c4108400e0000495100127607070001c8005802c10746000070000041e8452180d0301009110368107000c50030702044015000721034540d804440c0c0d02201000c80c0c80440740349001011141c0341c0d503c10401d403004505030100014400364185003501d10011220b010902d8152210f117580a100001d107400f409001c503d22685001d41071385e18001c0d08a20301a124a1b07903d0641c8030700c00300d00c03001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 266977724 1250 266976474 266976481
    0x70309060509010c050319080108030c19080412030e0a06030b151608040f080615060d0b010e03030408070311120d0305130c1202010e030102030705070605041112060912040e060405 79
    0xd01481503901e500c4012a87c0d6071880b1648013119401215512001c42c1a0b0b100104440c01d0100581d490742c6207860040100d039210f5050208488000c600543da15682004041010241c0302c080ca95040e019407681490514841d061101c074030300a6201c1d008142c074213a980c40141d5260401c183c0d4460900f41c0b581d444903032a440050207091030810040c80c3e8600000c000800340c00480c00e000885070034005489a95892841d407084042c04440c105078040400c110b00041c100c0710342d0082c41c0050062400d005240080d0000c00c1c59030b0700c990401f00310350f44102400c0040105070a240c4640302d5007a10001820b042035000c1d15656891001c5c10700525440c1d400103142c0358003840c400b04245d03030005d0460308080e42c0d50a004200c42e00e805401c0e400601c40586201c41400d050086900031103c60b55103602e005c0c460385030b0304001c14002d0b00c00c4604803440c3e1460541e907502e11038250b01c2c040c0b141c0084e114505007408001c0c41d207000349205404494003844200302e070007481031400b90301c0728080d100460381d41e9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 266978974 1250 266977724 266977727
    0x70204021b0703061b050304080c010b04020d0b1f090b030403021c0507111504140d2001170103051f021902060115030515040902030a061407080c07030906050901 71
    0x528001c0c44481d0020200c0c115808000181c41c004907401441c007080550400303041d094501142064402c00302e0000c0010400003100380c0020300c4550040c03400068650313021000142641e120303501032200546c480811250b00e140a80800c040c10700306103000c0e16402a1901c0141a4000c9440b0700d151062001c400101458024048110190300c0c80041c0b81c0c0540c902d402c0500790b0b0b0440c0303c060342c4000450444c0740d44e07401c00054152584101c0180181080d180c6052468080e0400c00965080010044054000759118254040000d030700e0460f8015044030600040c00c1071800110f1079650549080100049900851170900811086400c504820340d00446000a840b5040e1119654000f4407003400b000c5030302158a606a680f04042d010360300200706000c0b004c1c0c3d00141e5055040a80720401e4981a240a80c00000c0c0b5502c00383c26503002c070751079865983c1203513484411a010b034481001001101540410229400380003110150708049998800520520a900903141407010016030607c02da03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 266980224 1250 266978974 266978977
    0x150702030c010c170c092b020a0909050610030b04080304061b0c12110c0607050a020909100b060c060615130305150610020307060b1f1d10021207020402 67
    0xa80590000e000300c070844200100803225001c4a191260440804241034503180340c2151b450b43e0004020840e806c0c4203001c0d0154410f119101c01c110603030f84050880058581c448518020400d4450024205025003482403d00200600504000180240078000500f240460303e40260300711b0201901c0c0e83d035510b03050004100300000d248000d0402d03980b201e0b940b9805180e2050003441455017171052410751205030f440745003140a000240d040141460010f0030800013511150340680d040761721403851a008201e61076016215018581c02940f10110703011664003403100050780c181e8902c1e03c0c0229403281c0d03d8840c40007a180b58807500001c0b031b81400300881a41074031807542c00c0c0c0044001c0c266403407030155a50b0744a0440e0b09900801d0400080a40c64401205038509807143c000d549448402e45e0f8420080074800c2c544c1c0e42c415008403005200140d0460702c8070343e01d050307900d48024104098522003126594005001d100d545c2c072030203045030b565010a9103004101e40b02900c9440e00014070000300607 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 266981474 1250 266980224 266980237
    0xf0a0e010204090f020703031a010c080f0d060f0312050901120b240d15080d080c0403050a12170c0a030b010e06070501200c06150d0b1006030e070815070203 69
    0x10a41008908813483e8040d6000300701e03281c46034404005a02810303541127841415030582e0380c04284440c25440c0419020001091510f6548040034503000f644020315080b07503002e8100544400c801c050a10070450318600c03070880006039051075400c10300364000080107000901c820900b502c0e2988a192078507103c3d4052190900c044a0003440d00c007504514240c0c442d000801004071070760402c4200e1480d001b50071441004d484040c3d024200c042440c03082036802c4130024012151142d410003001001c03560600c580745005220748625403844050910040142c010420070303000d047c01c49014002c5010102040350f0581b202810701141c2d1a440e0300c01030740d481c00711a0395680c0050000429204210041d4410002d00d002d07250315044105000c85001450b010302c00c0200f802d03030720034000311b052403102c2680407058880061280d941d25030340390313284035903458240d4090300103880040d000c0c002180c050141d0010400c0000c010f0101c03071700d0131700250b40d680040e800307100701000990081840c0900c00c0c811a442c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 266982724 1250 266981474 266981489
    0x105011101150618090b090402010c051203040b1603181101031103041a0c03090307201201150b0c0604080904060f1403010c0906020d141b03180402030f0a0e010204 72
    0x4840f960341d04040d211000c83c100203120f080020300045242090340c0b1503d010410040d241241c25522940103644502ca226401d442030321901059061086040c8021032081d84500309149150074082c800c8181250b01d1103110040c1070a000c07210001c80e6410482103c00d54101c814a103d0400b0540164010000301190500b008400070402040c41906a281a01c0314136002c0200c8040d502c2a000781400e0000380d591003a03c0d017080211401081b02c40720065001002c01d6400a40305010700c0000728190050080e090042e519002c406494182d0920a00f004114000040c0d20300341c10100d810b515428001c000a050300300104041185403120350003000680343c0c002e005155951240d00c1c0c40c1c400303198402128841d46c242810b80c80540d00c0bc100000c12101079400500510200c10801c0d11b03490385011252810380001d01030180d0400120f043c45500211a001441d610300300c407031801102c241c2c00c10f44180140c2c01081800038a11009100562000b00c0c020001040002d03d0081806442a94491030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 266983974 1250 266982724 266982761
    0x22050307060309120c210e060307080402090105011e14090415030c0b0f0f0903010902031e0f06090c1507020d0303141333060803040611070e0105011101 67
    0x42150b0035610505815010344680707401c03070441140807250351303000010040c600c0f0305204d25500f0011542080c561100307503509081e10000480404140f89410884001d80001c104100740010350030680781075805403c083c45e02c2c090f2000c0080744407030f43e001204400000c002002c401508100740d0300c1c2c140c808000d07004105000041da17414056240b01810f0100b6113a44132041e1000075003503050303000c4805003e48007001e941000000a01240960404100030340c044d502d41c0b42550040e0780030b001003074120324003241d10310800294140240c5000c00d500c10b46c14865210303200b4410165000205111203103c11540e40046926810021005025001e0004e4028890760a8941095007540100103403986450f80380e03005554103e032503d40041080340c0605400f549401e102004907000405102d8072401001c2c1c51640f203915003880084898030b5000740c15903080803805010b4240e001c0940980e06810600500c2d405050280c640018901072044505001c2c070160103841c80300087d00031140c0100c900d01020b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 266985224 1250 266983974 266983979
    0x7030e06070b10121505091905010f0608010b0a05040908040906090c1d0d1e02131b0206011a070f3002030c0601091109030d020c0907080c22050307 65
    0x202c10644080d10054009200040b0101d180d42140d6010446650170810007108448904104e1000708405003011003180180640030764601d0720040213180b42803144000113001031408100c0c0ac116030054110b0403880c2d05007070100400e43d884c1410002524003c0342d000988403100d1505030810700c00e40d03010f0a9464280040003441600313603400480c03065480e07200c203440c9a0f464803140c1c49100341c040020703620400b128560004104101c4012414440f800c1e4411454000368000844030315400041840c0c040d140c421481d0000e105081500a0004a0004024035410280d207003c03511894040d183c500c06022a0132420711444241c03c00410f07401c50891000301c107101800001e03200b0707051602c10030a042d040340345861074400811074080c040c040010b00703441d900b0140383c940544454844462110340900401c1ca85035402e210b502c00b480001d800070500c010f020024449410030040a00d824041e81000300003200d0a824100c1d2103210294255101c4090b0000303644400c24041d0b00860b070144500c1601 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 266986474 1250 266985224 266985233
    0x806061813091209050d060507110703140d031107080903010b040c0206102403020c0309150307080a0506210703171b0304050d02060d020409020d1a180c07030e0607 72
    0x2c44105004105103501e07188581d0007901e8200003032040c41e422070015403908020070b40a620082d0010250301e840440c0807052a1030074604040ca4000b50b5a0b00d9814580c000403000170054070540c6802c908092142e1808440ca0041c640a1120007801041002030080300d00e6600394040401c00100130030400064800310402580e84004031440440c9d00c03c031800204410180150900c0a0040050017440501032400300f00c010313410412908100384000c5c01040003540d681100321320803c03c2180d003203440e8948120000c01030003018091003652407800003809107603210410611510007008001104181c1c501300441e00d040c00ea940040c000000c3c406820074896030040050490076005090001118a911a0305440c0d10540c4546a8080b15a130f61100060a01e540504095419688010f040039a0f5041550590f0b0060fa030240056035a801f04042c940c103490f062072101d400984010400040c02d484003500c452000d040f03000001c00c00308520742018450085c3d11030005014207080d4642c0d600340341 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 266987724 1250 266986474 266986481
    0x10b120a02071e0204051b030a09110603150102060a020403081e0d09030306090b091e18010c090302040e0307020a050105130b160b0f0408030109050705271f0806061813 74
    0x4080303110710304000204047c086440396011401c0c24080070a4910b4640c0c60414000304603000d0111680b01c0c001c1034160b216941ca6000c1e500c10540a4a600384296584000a05204000740000d403002d1043c00244041021030341a00c01d04001c8044030b05284007071280c4062035014400c0c2c80301d070403401c200e05507042541c50f420003000c59141d00410f0000094880c2040050a8120f85020300c4100f0140340007001031351403407002e802c052415000403184c40500d42080c25200420011000305003400c1081045061510941c21480c0420700a1424441c0c642d0001c0c021750b00600c80c480c1001008284e41100b848a9141034004044c1e0b0300149130780b00c200c0121a090b500e0603035020354002d0b04a0000844505440a48034801c40c0e0100c285403861b07080a8a0b04010800034000ca030402c4000d01003228140f0111021001c001c4100380c201c01c00884090030005044114044450b10090b40820213441d40d800610300f03a00080102c801903100c5030300d8180703500b1200340205195400600402d800c00c0c000103030b92 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 266988974 1250 266987724 266987783
    0x40801020715200306152503090605031e06040b0d0515010f030f030507063207050405130e010b031f0606030b060703050a09080f0706020c09010b120a0207 68
    0x2103052140c0d105082c440c07000d4022103401c40070103c80400c001142450401008807140115002050a02614000c00743c54201c004806403812451720000c02c0c00c4c541c0000d0060010a01d51405610350300c0d01310f6124440b801c0d1109804804800c0c90080b82491b683c41e0481e1101c001c01800014211505080140da80c0c2540c00c0d80b6051800d9660010550030751090402c0d0a0b250020202001c0c071069603401c42c0c441d400b9000603a8856501d4500e280c0c001104808003510300b411400d407281801c02c199a0044182019020206002c41004204200e0700d81390700c800e9500c1030815000442e5055600c19178090000340800650601425540c1020028543e2229400881008081100603100d5100b03400b01c030103014206d6844001800408006880340000380301511251405140701c90355402c4440c505460341c2d80500e081e40050345c0600c141541000281a02c03c3d003101c0d80d0f061035140c4804c40042c0d10072207203120400c540c600001741e8841d1181c0c040b5211258482d00300d5051281c03180348146804401c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 266990224 1250 266988974 266989013
    0x905040b0a1409040c0506040321020c0918030c01020f0c070807050310051e07020309040b0d0b04030f0512091501060314160908010f0203090f03030103030507060c050408010207 78
    0x1000c8006400c00d09a000269460041e51070082c0312000304002803540c0051048500d10920740010072a501d40314041c1c0011413080c130107010340d240d0981583d0103251008040c6411076010814030110380d40d030310004941152503902e24201004007000710301d0847c070030b01c05082140e600018001245590301c400600401d01007070160b80c220342d03c40c0300c540d480c0c2c42c1510500b50305601c00e4503c0510b0380c2c10342d402a60000c944140e88020030803105200b00f60f024080760300c440543c101244216207030411303014a152950044400d240d905505030360703202d0101400f90001e420444041c00c6051030a0090301220079042090101c01054a0308510290350303880d082402d03c00d000c621800000d240c50081c01003000341e05441741281041c0e030303441e034181c610109954445800c01ca503d4000054004080c41507488a14400401503a45d14009802c503241c00c480c10158003840d0300400c0104003280d403000c2641ca02503841440400e43c416003210894941c026a04000c0c0746500c0042e0030302c00c004020700f80710303c0c00105 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 266991474 1250 266990224 266990231
    0x10e1302160f0c0f0503150718031b03060b2416050601031113020412060f020415050d1401060212031f0905040606050334030816030912031d0d05010c090504 69
    0x3c5d030042c0342c0c03500410f1500c003229080c1100880c44c000c0c0135440c440d0410443d40c2047c0e040780d07070700d884000c10229070054880c100c584900742482840400c2c052100d6003101612450313075407035045a209036152071064900005190101720501e80000040900c2c400b960040300721a040c1d40c407803c20400300703481584603038466480d00380d1440454600c4d0080d00c01311502e401d12120181240c0d15804041c0c11425100300d141c41c0e08100225600d9820381e80d032820407105985c9c0350340f05c40c011116035046511184446959009035001041500d40c0000c03121605500210b00a440e82c680703203400c018143c11640d02400341c484043d400f02d52650180e0106101701e00464043c848503568000307250b250000300a00c1c0c0180090440c544064104041c040d030180241805c0041a41e80d6a0300c85d0940c681041c1e07107100304603a80500b88024180d006080c8400707024001c607018088ac501e9a070141c491341c0f03481450f0707041402d603100f401c02035903070510048a500d80003402440a19000e8000070404002c038080c0f140f08918 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 266992724 1250 266991474 266991479
    0x6080d031401050a030f0309091a12010504020a1205010609050118050a0522230c0a060206060a03140a0b0a050106110f0303150a08030d0b040605010e1302160f0c0f 72
    0x9003128a41c0c100c803c05404001102e0a64403200c202070f041c071109405110540f40c002030f400310184100082c0e42003447c508643ea01c051010003c1400410402d008268102410b000142c0d403441c22000466584604401e40d00c15036280280c003402d030680c05a40d800740381c200005030711000c00b80d070800c010300b075206d080100b175840350404c2d42280c07400e60740c0c0300f420384c01c1d88410a800440310601050701d50007001d103440c0030150b101c842c0714118100d04454140d50400000d007826401d105a00b034003d440c0c940060310302d900e440d2002c02c80444107884094442500380601030340d40802172000d203900b2500200c010201e481c0003615040038104c21f01c00e101c00a0514404003803120b03400715412071441800c070055407454441000e290b00e05d40200e980d1650040c00300c0c0c00092428402c00007042e44801000b00410082c40103001c102c01c40f0b0440d4045418000901c9a0862a9031800e0350360180c21140d520040c0c031050806040c5240c514a030394024000c80c01320075400244a6800341480441e5103202c050900140c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 266993974 1250 266992724 266992751
    0x6030c0f12050604060507020a02030703082d0a14120f040b0a0209130c02011107060903120b06070609060b0d050a200a0e060d020603010e0925260106080d03 69
    0xa00700300908950454004030340010041e801c440e07002201441111780c0b055544c0c000070300789240e035842200c11190000c0c500011a0b03174030070301e91b581c1d845034080c410202006410110091050122480402056440e042c0000d151007080d200058a10b1503040480d1910300c031141501001910251a155445030028100340d405008a80d2500809400d1405c0480070300b54904c060562035042d1000d65403a03100740c11800f80c410005d003034210b004210214160050b800c0240c02c0018076204250300714102644810309450f844201c5140b254030800001d4210b40b10300b841c200611100040303d90026034003041c082800000154860058014142d03c5200707141c0880e000c6403280114040d40e000342000b08108120300000068070341c89074010b0300341d1445c0051940046c0c01c944c030136005012401c00301002e104a625081203c000f0000c1049a0800413070038454003507007480340c248a4035400d10f5400e41280c030541c0340c410319180c601000800902a1544a60340c441d140c0708200d0415000902d095107080340d46 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 266995224 1250 266993974 266993999
    0x1171e011a03071203030e0106030206030403021b040605091f0803030a090b010803030403080f1332061015030f022107090f060c0204020c1501080f2b1206030c0f 71
    0x242d20b50000d401030130607603940590250021400740031f8995a100400000360322070070000d51280d8401d60140060b1600a41d400311185c0000c0300e81806940b41c040180102e440c1c1c00941034001c8450865190311600c171f001180c5000c4002c0e044020180000f03c280710180b45140c111405a6109500440050f03803070f68074440e500c2c00304a0b005400103d403032010403010b0881c030724030903085601c0ea00401054500d0b40ca4455480b04a0562034190040030340400d1001c0e0b039007000340c80b1504860f0b40604a0740c1403800404a420816001c2e8580b0380a621624038202406079001070741440c1c4903035003551111030f0b0403407801c2d038440511007820300404200005170030148100f810100341d8100c10095000141049811600780003400c1c012a0007503400c1020fa416620700304500640102081201422581054016070401c1404d640506080d80016912195008602d001421003614003e103284450b40700030040710a9060101d000101c2c5150120102c280b00280f190709080d20843c10200320021f5540081c100030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 266996474 1250 266995224 266995229
    0x60303030718081207060c020c0919090f12110607050409090614100807061115100f08030306010306063615020a05011b0801171e011a0307 61
    0x5a00100005103a007405038a40280800c01418441c0d50b1076220043c203480c185002c080604003d8020808508119041c02107190444043c03003e0081c400d003440c0071034a0240040c24180750600f015200501c01243c85d4055030105411101c240d00303403050390a2140d4074a507a9040e9100099980341c1400388100e00054071802070805665041c5042e1400412a00410380840c0845050743c4516142d10b40301daa8544050041c0c052405d100307052450030051628003040c5901440502024107a60800001e01140301c006141c0c03181010090303030341c40c0708562950701c0d4560000303942840c4003070380420340c040d000011318490a02a01c080080e44e48940059543d51842035454010340c3c803050071814130760303100d110001c07452608021800c429030316515080e441592000c0e006c0c0040e4400c0b103100007880380034058010034501b0840004280201960024160b0405004082c0351003070b1840da0300f102c00720801c000d8260b800354001c440c2c24442010010790203484c20355051038400521403210f110034903002c1803c0c0c08 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 266997724 1250 266996474 266996479
    0x201050f0c07050a0b090316140d02030f0109080a02150402280f0602030d0f0204050a15050c060109060302032b0e0604030507060c0209010909020f040b0d02032e0506 73
    0x600310316089910041d400354000441c240101c850000310390702c500b01401c018103900404d007500c50200105051801d00700290360400071050640c10006550000368500d50301b08292454100300f02d09001007490465981194480e0350b1a080d51813092142c1100036003080d00c1c4690955155a1201c109941407403011358020f507115680c81c041c410380400702d05949440e61041c05104181d0360343c1d40013103169016203a0000000d80c1000170541220301280c0300786100c07040c801c00c0031810705040501141d104074160050008070038450315051a0070340110260780001c59480100d8801c5c0d80c50b07079049400b030a0180310803070280c81000128481c0480e26006090790350107823030010550181c0c0050490744449450703600f681110b41040084045101400200040d01b034030784503001800a94414410740c40c6050b802030286502d000c8916006030b07220300384401e580b001101c0100307440403c000081e04400705080000d6040c07080100281ea80c02280035000011300c00340d5011441c690310615a1015200300301c815a6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 266998974 1250 266997724 266997727
    0x50f090703080313050f0a0501020316021b0103200c0d0e010509093705100b0a020a030c080d021801020c03010204031e080f1215010e0306060103050606090301060605091c020105 78
    0x70700001103409060344c1a4003443c21950700012000240c0e0401e58001015030b1140d40000c1001884480203401a2805015100030500c518001c0384516080b00045015410503854941000402c204800b01c020b54804041903142e40740744004c0075954405d00c444149005c148424544401c9600401c2900d00084001d0305c0c1519a580b03e24080c028080c0804003150003082c07401c50745a40024500c0f1880d900c0056240002e0320341040c40b84440401c84e90790103420400020403817143e000d940420344a030404e0703040c01c2c5281c0c2c0714103501d0b00c840075002e0298000c0b8841d101041641500c00880c00740105c451080c6c003540c1070600c0d0f04e030130725090340f049000280c01d5454000d401004659040300410185000301d81140c1040000c2d98885084c0d4040088001c401d118001400304407091000c0c0015581d80900700840b07200c1402004c41c1e01d41500904c01d82c145552100024610740310403040321a5884014002c00c801a1104030140180e0403900d006401031440d043c800c020380c01445240b55140c3c0c1c0503191513 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 267000224 1250 266998974 266998981
    0x6060f09040506011b0302010b12030a021c02120c0102090a0e09070e060d0b0708070f020a032a0b13230a0213180819020106180209060913050f0907030803 68
    0x10002d854041c01c00c1e410420407800c0c054044084c3d00036007030258400c0d4000300710221403008002d044c86001d0b0806540b9041000f1242c410b5030000340342c09910303d0092594504d2600240144c0c103000d17003442d8004404000164079010054107500034031917144100e82c02651207803036040d0241400c10454204880e544242400d22094080d0031205500c81401060050a440180c1c1c8910701d2070401d0f600c0714040b41c0902d0902c03041c9a00a045014074140320310080580e01110345005024003001000c052400c203008544121284c8101840072610350400640483d506181c2040e4250014041040d03c0c0c801114250112007100703600014082c0d035a010051203200496002c100c0e0360b4160720076000c0c140d60342c0c41100f20800041c0c0803104484c2d0113540003a45418a00584c08449040e0504c214216454018140200e1242d42d1b00300341d40681a00f40140c48031001e03000308615210301000039500c000000010400410705400c0307148100b4a0307000c006c03490349a140c8844d07031300d00c030382d00004041000c00d0001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 267001474 1250 267000224 267000229
    0xc01050f01140f060904020f0a081b070f03050d060f151e0e0607050709060311030a0b0106050d02040f0b030a0c02120301061416030e010801051203030103060504081308010b030606060f09 82
    0xc80d0070f18001c1440b40707803500400014040380d0160311a080c4d04000442c0f00c000003900200300c02c2d88101c8801900040d01c40c800c0e01d110f03442c40350348001845408000b030300106141c42031f01500c0c1e43d890340d0310040004035201c0441141102491050340200080b0585441c1014030440e00304415a14250000703100c030034015010740f607440001c00900e4000f0000d1020390081032080142c0c40c01403041c0080020050304500340800c503c40c039140a1390103a400b12102c040000c010070b0645044400c10302e801c6480b00c500c0aa910064401c0d40d01030385015405400120344824804000c40c0958140007040060f540043d0081c0d8484110400f154192001030004002150040c1010400d8800d0500728902d4400d100c110040118103941301500090480d80804800d9600300c0b10240c050301089601c04042e401244102c0e07130320700c01404014803071503c440200d01001040b0b4181c0d2292300021900c001f40380d03120070390140206205d0000300c1c4648121001b25006082000c1107555808403103116614002c408401d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 267002724 1250 267001474 267001489
    0xf0105101d031c1d04020c0a020d0203012903070e0108070e220312050f270304120b0702010c081006200601141801121b0b040b0c01050f0114 62
    0x39405000f480718040d00184002e400c0a0180b03031075103481c8240c41c16504480c2c41e80000002c005d028a104102d000c1400000080c0740f048154101c4094000403c24400309000d030200607101a24444044200c0c0d400000003880244106001c0d011180225034038064500b0200007845480031541146100303200f41e400440500e60300c80300700301a0401c0300c018120002c0c071100314460183d0001b1407400d00052041d00d00d018154001d1000010984542004410a07651541ca04c2400d100c8005025100c0b450003003d00685005026000542074442e2250800f040122012100c0304010b5180030540710401303008065250280d050200d29640103814001c00340c45071103156146110385150300c400721400720006c029140c007800c41402100342131b592003030034824207504114029080e104940010f011902c40a840348141582100040003100c0301c0329130300407110b44260403818109400003008144221303248000d018806103040204004d0745d850083c1c1420102c01c2c06481580d2a42400c8451240350150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 267003974 1250 267002724 267002777
    0x9061404030f03050904050601090803030a090c030c0e010618030b0c0c0a0b0c1c022106060d05010e041101030c090e0901020d1a040c0804080d09060609020d050f010510 74
    0x1500500d850348a4440282c0790440a0040307000900004460440382440d00510307030846000c0c02c28140580c103200740240c49020060030700b46030903590080c520510800d040440000c41c0c200084a550585408064045403002d02405000c03e00c0c1c141c0000c8104100c403113001c12a5001218600142c6888000381c1083d40715000c2c042c600d10504040d40c2c017048136010104c2c081c4903207441031592108400c0e101800c00e80e07525002400c9510621404500340d1800803402d000303014a01506c1c55030355500c8001107540c0038008032610814609030011036460340e1070310000e00650042140d8800008030b0030045040d20766900065000034020401008102c0343c4076038183d0401d803110005418061101e441c0402c5400d00600c950f02c40c9122200b10109082c00d2107003607041c00152800c0e0025240584600340315210381c1702400e00d01c958807000142400300c0c1e540040b018184c81d2a040d5a40c0240d0401d602c050315044c0d5070f5215618003c00002524540b80e080e495034141c1c981c41d8450280e0460202c00c402e00d9015 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 267005224 1250 267003974 267004007
    0x1d070b0a031113031b0e0a050a180c050f0402040302010f0c06020910080a1407080705070c050405040f11010815010804020a030b1008060903160204050a0f0e24070906 73
    0x6200c540842c40c00c0741c02502c414048401c01d000d81034a107007002a00d0510007405800080031500045c04540c80211020360f01098400c404100da4484408420040990f4005a00b0030f0020707004260400000920403401c4130f508648000e807200009003040103d01c101d100090118401c059040c2e034082c005d03a441c0c10594040d82d001400c1c490300d400030926102c0c1445541000580403000c100812415200300c114007102584200c0c5240340503c00580604d9010f00301c403081c000007107a180c0c20030903180841d5020709006001030100c0c2c01c180c5803005d060021100111041c00754481540865480303803070390740d10403424010340c210140c50510055031039800103001640c200c0440d08003c40030500107003140d800f500300391355221030b00c0f49009900c9040c00c83c0580b825501e1740040000302540c80703001e403d00d00500d40403038000400d5140c0202c244003c1844030022540c550400070048a4039034042818a20300000d41084100c1d00103003005460310b820308490b58008948a074800f8821035105c1c41400d07a0000c0c0300d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 267006474 1250 267005224 267005231
    0x20c01030b06071121010c0311040303020613050109170d0b030a0201050405040f020403082101060207150f02010b0a060519030b0604030b060612090c0f09060907030e010f06030807061d070b0a03 85
    0xa108400c2e031907174021000c040c05030f440702c840c14a000d505d482003a601c2c0d6000b0302e40900301411968001e44034100a0000d110180145122006002c0b007903002c0046a50300c008447c482c1c1400c0c40d080e00068201c5182c40241501c3d00c1c14000040c2808a41009041d81c141c0d2418a807509190400009110074848101c40d80e038244001310008075a440100400102c03040348401c4040382d00284034105070140c02420454008000401004e84002091a101c4407542003080c040444e8080403401062070301c28031a0300031030710100041c02c40d81100062031507049a84803100451040710081d070507554510451500450200304c10004185d0031224541c00c0200103002c1c524010301c00603018611001660208e409400c000002402c034a8940242e920000046c0d03100000c0e0301e00b0000040c08100024040800d15445020498000d40203501001442c030200508028058480c00d00614503002003408460007403a1599050510b82022030300c00c0e5402c40c00d00180070241c10030f00d101200e40c010380c0c8403000703040d00d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 267007724 1250 267006474 267006499
    0xc020106030c09090c080a03080402090a091209080607030612020d050f06010906050307060c020303090120030a1d04050c0d15050d080703140f12090c090f07020c01030b060711 77
    0x88002e04140107044118000c9100350490074050354150a036404020070354046540f01001035040b001055209030115010744039a501d68880301c1c0940b19001b00100001100c110685240750400800340c02d5480c41c20446000c1d558882003501287c610380a003030f090904005040d4014a400d0b20205c5603544940103540d04690740707000c46880d001003a08404a43c030748a2109200e5401e04115942c02402e01e80780228026215030042074a910803400300c40e0400074007d200c03544030b280314004002580c003400100d99940700000c0008105510111948503101d0a2001e9a285483c11307000b030b039016070002c6007814541001e003680100201072404100e00034000001c400034280e07482d5000800328a01031b9400a5440c0c00350720380105035003080403000f040f04505000c14500d142c1c003241075507105114680100c0050f2250040c0b6481c100b40000e64542c005115010440c01d0b6100810b240d000d00303866021101c28800303500041d0706071442c803010607421610512004d000724018a24059510750081e151841d01e44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 267008974 1250 267007724 267007733
    0x1020a02060c0a1b1401030c0e040504020f130f14040c060c060b0301020a03020c150c090f0a080d020109020a0e0705072307091a010509240f1216030912030c02010603 73
    0x1c40320403214011310258041011060540e00050004000d20b000c0144207007001c005080c20340e0300680c007070050303907540001130440d10355503106c66404400a040c80d080b20100c6886101520318214148072144c280201c41004020b44450076000316031200d5410040d40c20201d04440040d80c0c1b08050f01d095072110300c4c420042e2400c1c0700501980c021503030090394800e4030801c10352030004035103d60400039200008005080000c4000d03641020b20460318070f50040710740000550070003510b410180b800e0150548228a482d015482540c40920071f40d07001e0390140d503822800072441000c4495502040c13040042100040d200013240410030900907203a140e0901c41d140803403400042d5003007031008903070303802090300301d00d80681360001011002d01c0c042d4502540440031130b0300307035040841d18005184883c07042c101022480040d00c40710840d04025946450068080c260024426038000d04842d8000110207031051181c00340701c0016820007110b11031111501c01c06c5000f0540c41e10403008656031001b000c000034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 267010224 1250 267008974 267008993
    0x1005040c0203130e070f020303070819060803121501021b040c210509100b0604030f080708130303030b0d0f021009090c0203090906040b010c06020d020f030405060f1501020a02060c0a 80
    0x10300301e0740d1136078041e440c10080107010200a00b8000d41550b0082c0f0412507001d40c4040c1c1d06510120030f9215440c1c0000085448000d81440c0c0c1010a00740001300c2d1200300100300180d080c1c880ea03510062020400c04010059071110700780034407070220351751252100c205820242c0214451301ea151600c440315900901c8141c0c01c810120605005103030f140c0c024003060400800001000c1c1c002400e08001c2e1350300000000300c2d10f11446c031005041680640c403903820701003094155040b4617000100103a490780c03094165041200b2600040f00404e01e00b050001a03400c00320034503020180c2c800c04240c4413081d80c0e001c100008a80c2403c003000c21021700350202d03a61110b030080420303e0f00e00703400651f200c440441c20041040401402c01d80a281351413640000f0380c0c0d10004151020b900082e0040e501c0c0d0a81c0010b02c0a8032410a01c0e82600170000180700030864006450f80c411032042d00340001e980c985281060800c5030000c100780c0141e004180400141ca440001030031585c0e008411182601c0143c1d0f15134821 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 267011474 1250 267010224 267010229
    0xd08131505060f01020706170a020c0307032c01090b09030109060e210c03071e0807121b0506060f0409020307081609060f0e062103030a0b091005040c020313 69
    0x40d241c8410901c6118141950ba00c400c120090014010242c14240b0080000c0d0142034038943c190140400718140c9a01176045885420440d0152030740ca18281c14043c068061040b48099581e42001c0c0c0c6041900003c1c4c404042c0e450140c0d11b1001b010301d0400704002c80d411416040707034155640d02401000500a10030000754000e40c0d800b90040d440ca0070190545000d4284407842c454904010100304401d020003128032203588880103440d8141001520340c9200d52195005000090014455050200b0750440000d0000700381e5580d034070700c00ca9580d024043e841b0788400415035406400840c03050710703081c00f00a400c0344000d000081d440f40b030b90300003a00d440825032007259982c1080c6441c0210701ca00358a440c01500401070709104907490072103180c90400c50b40c0300f40b400b107600c110003180c503035518501c4407405041021945604008409415a101c1e4010707901c1c1c039171403460301400005506048200a01c100d10030f101c080b01c0b9a103403900b03200203005603176941e0045010820100c4291112120010301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 267012724 1250 267011474 267011513
    0x1060305180c090c1b0703030801030c1202010f320a0e0102030703020a020108070509030604051005011d0109020a11030c010606030b04060312200706030911040902030d0813 76
    0x49500740200c40074100890301078200d2842d080b41080441c2511500c04441e042800c03e0744940d80d64901310f00d0000244119902003400f8092450b00105055100316558180c900850781541907030707a200d040c02144103400000a0200b442190050490780c0503211006010301c000c10810b007001c521030300f0458940140c415607461100c000c12040e0342c0c40e40c080070030010179500380015440c0c07a419460103503484060000080c10464108000703510f182c031400580b50132072070150864079181443e00e04652074402155008410529000000840d007503283c0c140042c40c0032000b258013040e424811280302a41c44011001d00780400c005c401040b14504100401c01d0b0185580005405810140300030700f07451820101d28031a0341440c00c18004250224442c2040c00344c10b00741141404038001c3c60351074441c1c0d040c084214901030004000341060f0940c015500c0790303200b84420100d100f5107034200400c40c0c03690b410182d0560f00c0000195040b03070050301e200d60000c41350400c0c2000221196114403805500c0180300c032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 267013974 1250 267012724 267012731
    0x7080304080c060403151503082106060301050d111903081305060403080a0c030e030102030106021e0a03090501080a090602030a090b0f01030b0a1107050a140615010207150e0306010603 81
    0x1041400a00003008002d00841c1d10300e240a1558403402d1040440a640c002c4c2c455880003040312030445481e030100110381c0102c03901d488801c1002d022000c3c48508102c42041c1d41c00c1d01c005441413a000003201e040e41d0000704813501c600011b449030809a001514038941000c01107050020400c0c580345d0080c000c41c81180c0d103d546001211082c144000d81c1d07800b503402600188418400110320340281c0700003010701d1601c01c02c1c64a02d800c0440c0c048441c50700c080d8040d4400400401d446a0124000c00610f543c40803400305414181030705039031410342800140020310040c1301407000d923101d00c140c0b40e088062300703102050180c1d454071030100326841900d1114809550381d00319010001c03245042507105680031000c0d4803a601d1911054105e1310028042c090090355480b01808071030400041e1401e4680020840f01a00860b00e000308401d14800d520540078815580090078510041e84840401c201c10b0f80607040c45031805c40d0021a2068400800d0103000e44503465104640302044554000c101030354020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 267015224 1250 267013974 267013979
    0x19030216081e1207021225050f010c05060105240f0a0807170105010311070510051b031e04170307030b010909020c07120c03080a02030a08150904061d07080304 70
    0x852400001050318419800400c40401a40f0040060364569a01035440c0f01500c84802440c60420324520010003607442d6079071046280c0c2c0346003030002007902e0007071b11a074200c90800401980c405007950b100624544c041ca006200d24182941000000c2c00d141036000c032500300c012210f00301c0340c001217004d807801400800d580c00b44580c40440303c0e801200600b801c0c820201a0740b41c0a9500320140035031030605486505440352a1402d204032500c50760044140e5400c0807a64a0007405800107481194100102d860b1001c040040b00049a0062910020111401e160a1015060540f004000352048000108071840d8102004011841402c3c0c0d56800200098136078000341542c425a00f1043d1444c1c414072243c00c07031745000030300c44041d00d04210030b8130710303805035442c200006555580009015240c04196000002d4000000d0402d05107544c4070a81c1c0d50391090600d041d011000c15080e94868020000f06000c2201603211120200110075400c0d1031011210a062404245a010042603400000c04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 267016474 1250 267015224 267015253
    0x1e010203190e180105210708030d0629070b04031e031506050a02031c020405030a0f030806190e130606120204061409041202100c0518030607021903021608 68
    0x8101c85000f11440058035418000810014480f15131a681c410201025102001808004820040c80300004a9640d1181645c00c54090101c2d13201c1c80e401c018100300e8400060000000d104c12207451a01c000d4104181601c07420304440028006806110400d00700c1305510b100780c2004004080b05403004070302105103400500301e0b0b042ca91320078001c020782801001c0c0160f81c0401101c03d492070150032284d562004e070040302c0c0288034940c48030358548074001800c020081d0141072200030500944403044544c3e2600144408030082032540da24422107503034140514440111020340000c0c4448200c031a070b60869941d01d0440b0100d401500c407584110b5401d10862410b401850701400d503414040c400250f01c103001c103281d0f13000908000c041e0745604104024442c0b080140d00c5510392070300d600340144410400007501a40c08041d031200210740b54070014141c5e0a002078aa4002ca040d82d00030400700000c43d5441e500005415021400c45c010424905051120307900058041c020b030001138039150300020309 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 267017724 1250 267016474 267016489
    0x609050c180a11040504240902040b090d03050903010504030806150702030a080a0c06050a05181c050c0708030c01020c07050a1518090516020c0109051e010203190e 72
    0x25814465115039150700c625003484099a40c010440c20000304040d03d841e81100a203018981219030000c2c0b41c1031040ca55549400c500700503094602811030348150301c40840c031080e4401c0d4007a22542007000c204005139802c00b0400b101031b40c0d000e4580f1600b01214000020f0039143c0aa03010f40003d001c0707030b0034080e081c80c019801454001c41c280f4801d1a10f032843d40820f8851884032000351260501155040c000f9005e4110f5a03440e41e40a0010455403410143c032a00900c0d017581c80125000c5c105502c4c0400603000140303440f042c1e003a0350780c0450102a4034011103842e4000d8400710b00304d00844030009001c1c4010005015150418800582c860600108103494641c036540490701c2041d20f2441004101100d02240c03501070194036004029400d40f2005884503441c6a000c003080c02c0c50041040f04011340e04142c282c014105500317407044404080011142c1f01303054050168403070040c0c601000f83c1e814280014010309c0c418010b49003041305041e0b4110000d031141c0c007880c0208981c1e0302944c01900e403905 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 267018974 1250 267017724 267017743
    0x10b01080a02040e040f1b1212050f090d02040204090603241808030901061703090306102601060833070804110409020a1508150d0f0f0f060905 63
    0x188110f00b00342c0380550812a0510151000d404c3c4110700c1d40f1001841061481c0885402121040e0080316039210402c1501c0e1802c0e1409071205c405900e2002c0400c0e10500498440d0b8003418050342c206940e407400c114006036160303403c0380c1c0968208800901d41d08240030f440004c0d0700a40096002d10704c99500248500545500000c01a25002e07483d4180310040740d0901c2c1654001c00c00d02d49950300c2d148000c3c01440d454201010104000110035403d1138000000c0200030010780550721140c507103c1c030042d000005030007a071070001d441c4072003181150450b604110f6030540d42800840c0712962005480e09142450300c5880403c0d004030043c88054040c022080f07001c13242c0c528140790918103420010608103000c0c0009201884443c0c40c91016902e0340c21406074941c0041003100c2d100c2e61016207114401f20b0700818030115040e10009041c02c21a014a5a00c280740980184502d100c3e554414403805405801124940100407551011800683c030394914039210b800006921041400c2691420302100c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 267020224 1250 267018974 267018991
    0x100e010b1203041508130606141809071703040b041e1707140f03060a020c0c0103110a03020a0909050108011d062703070b0c040e010b040b0f030a0b040905010b0108 72
    0x1000100081c4140c1c5180f5104c0c04001d01c0c0c0b01c01141c503400c00c9082c2810300708001030302c0030b0304000000c100140100f80b0610819421a10700c400c05000114180e940c0804580f16030341608010000c1219440000700001801e8142c0c0540c1d00e07150300e61115542a800c1a0010300280500000030543c500c43d4019610240111181074600861007404c026900d5070540146800040780003020191a100c2d4090740740c40030710050a903002841c054604d403000b9003054124424602c158400b64226501034803654510790070040c54940f8000545105902035440000c184003040325409000a486c0d190744501400390886070008280c0c02c0c1c9807607004482c801c00281520580d00140300780329014213a000301c1031255070300d00080045040c40c400154107500031008040c00c8615000c040100203181c0e007005006641c01141c1c5c2d0a0b440c2d0300d4200744403840c09140180c0041c4201003001c1d40c0c03556882405543d01582190001c030300d843e00c250101d0251120071234100d03a180e4440700603a28035038220407842d41c0055070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 267021474 1250 267020224 267020227
    0xd261209160e0c0306060d0b100e010e0d030e1c020312070302160e061521100801020c03030a02032205030d0c14040902070c03140f0705060a0801060e03100e010b1203 73
    0x4010100c0d0fa910003c1e01d0705200d0480024409802002500444e40004c8000d003640c401c00c191420240c1000c8107049954001450b0072000c41d8680f50080503041010382695400c1c40c102c000300240701c02c45080c4454514601d40070513110005036010000303c1c0d50000c181c1c20150700ca01140c40c000c0c1ca0f000c072014036400c00040004047c0076814032210301c0c0303602034402c079845034800a000030b42c0c0446d84200010409404080351100490108041e0004d0160204c83c0c02c9540040e643e006081c01c0740140014411540c100b0808a042e03004aa00510b0700891401616000c0600b03803202c2000e0b071a000300007100c2540001c20b840444103158485c503072907000c1c03038280220440304003241040b2902c1103014200c04103070301042510501c40c1c5030100501a40d4440c14440c21504408040d660f18928840c0403803240c403803040085064106401619901aa180c0301c1c181140d0802809689801c018070159405208450004010320180d00400710071a140c000006030b07008002c424450704490800c0c0d816050b610 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 267022724 1250 267021474 267021481
    0x40f0602010506090f0718030606090603050c150702060315130c030c0306050105041205101a0a080c0a030618170a020706021f02091903030504090501050d261209160e 73
    0x4000c2c40d540e03000d80715247c824042c0000c0078a80c1044011500003400030341c80c008000c070758100658040e80949004e00c007142d8164203134008000b0f0345982a03030915500e43c1306020745001401c00201468100c0040e8082c40704040340140403074200b1104940d5654210749500222850903054410050100400d107000d010050500c80040d000748524800c41c0240c2c15507198150030b01c81e060290713012048140313000f4404004041d4a0310504040c28000394403580503800c00141c400c00019221004080144c00383e0034891858075900d0051040b101c0e504020b00d42c009080c4001030b078030b81c0503007810381480d00103648405d801c1000920302150794102c2c4003954000d8059605081207108031300c04200512001594034048000400d41812580d04010001c0b100840d01204164000000d04195401c102c000c200d5a0b0b603030010405404010381020744074040064103d40745800c004503108102e1860340780c0d54904213030780005075501c0504890743d40300341e00169101122aa004007106000b4661a00710300380301d04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 267023974 1250 267022724 267022741
    0x703110306100312020c190510050c070303030c110610090b0a050d060f0605090118050c07030c0b0402010521060a0b030402033c0c011815030207020d0602040f060201050609 76
    0x2c030a000c09070440f1861040e2040c118400c00040b194102d01801c50707074000c0504004c607100721255000c3d9520613803100203c004114481c40039900521011001450054a035032070030b4006114194a2004010400303030124551801042458002d0b0b007842c0c210b248452401d1100790031116100d090503c5000007580400040d60750000150000350410340000f0404054122907000b4880b95028a400900320400002c00d110503840500a441c2d00d000f050000f070303071059550340d1284980078000b00410750315216880031845201e6290381c0a841814060320703000000086080004010b080d101d983c0030900100046400d021440c04028000031f41924110309040e0b0010340c44107143c40303c1e04025400708000c02840104003481c401160494007000d440b0440f0712600d5030b00d400b09043d2050105280360710354102c0d0030807110040d003107841d8680803000c00c0c0762068040b0069444520241d0f80b040c0c4201482010441504c010401850400600b1501616103c0041e003541d2006118034031520360b12041200710b5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 267025224 1250 267023974 267024001
    0x1a180c0d020f0c07080303101509030b18011a01030e01270606030f0b0402030c0904030f0f0309080a020c190503150408130305070512010203090714061b0703110306 72
    0x851540002603140d58000301e204546004105882d00c040c4604d04002074111808802103004260341c03916507130069112107085200001000c030300800610790f1a02000131905018107260071540b15040300301140d40ca08002e902392143e008404841c43c901440c0803c41c1d680500c40c01c0c00243e650b038028407070324103170510a003000030040010000f209080c0c00403004103c202d520100143d83e01c012a500320200c0c13404c00c08031904003242d003240240b04151f4503200701c0ca040c2400d20701c0740d80d0580d01c82103540b5000da4116460440102150f003410b031200b400400084d40035010700318011980d03004089100c001d40400011104004803620150180741c01070086443c007149403404200d9051440040303440b80d03e400c5206114145081c141101d281c0804410410040342c1c8070100c600854206141d1031245007102d00300d200c1590105a03642c084d403403c00030b440c02804455403400c001080241000c20b180380c82c4078040807010090540d82c01014042c0104151840c02d80d04000381600203103000c0c640036400384070301c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 267026474 1250 267025224 267025237
    0x1403060105010e031903030501090f1806020c010e0a080a02060c070c030602032212020f0c030705040e0c0a0308120c0c0607031d0d030605130c09060c03050d1a180c 72
    0x4001143c00c1c000816182001000f03000b100c40c03045807450440d9801c000b001400b00b8040e01c0d02103401c0c00b00300c0c201558a405540e02e4085042d00c456000d1150382c0d9017030001d6204d2407400c86555228561452040c0080c050304d010a4000e600141e926854800c0007810001e0042c90844104400d025440101c0d18155003a400c0d00e520000050380d90b00d83d00071004c0c062900031a00328001400f081d040d001c2100030080304030441c86503003c0704d80081d0810a030039200c2000301804d03501075025a000f0800c42ca0a0703040540c00c4148802681d003d142c2c1a00400c0c0b03611984c2d00306442d525170015800703010031101d030f131100c0d44001408000c41c10000d00320182c50305d45501400041c00c054031003100200c4551000518200f520001003243c20221007a00050701030152440780a100d01945803030101a00290b0082d007270504400d685041d5080d0030190280c0d03400d007161000303400304282404003c10f03c07031032031040b0322402c42c0500306e05402501440800169a41d03200445111a03080002d0040c01d40c100030913540c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 267027724 1250 267026474 267026477
    0x3060906090415110f0a050703020705042d020702040e060103030813080415030605060c0c0901091119030b030304060c0209070c030504061b050102220e0714030601050c0f030310140306010501 84
    0x4444c043c0c3c4000352124001c144940034201e41c00100c0c80710003a00030000700b010b02c5c841d4007600c40d01544c2e40c0410003102c0e500d208840c1c0c120f0b41005103504c200902030885181c413010010042c140462030b0049411540c00e01c40c07041040e404070006005042e005000d2940c0710b10505148000e031092941c580340d035401144100a080d00f1420b03100000d4a009411210140c403024110b1a11010f002d90b080750b0300d2075034004050113169900d0012503110340c00e010303243e4520802c1c56100d24040202109002c086040c542d0141015036031560074a0f80d035402c0c0001d1008120642c1e4910484219004101512f50083c1070300b0144000c0702d08a000103600842590308540060428445182c5501001e001a154200700288194800503525001d52031100ba07200c00c00d00b03a00302485a2540b20209d003000220180c0d11200414040c1e440c00313400d50000c0005541c005010316040781411000c40001d440c00001a100d140a50008002c000c646c2281c4c200c440001d0000d030340c0401c610945100801c3c0c4442041c0181da0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 267028974 1250 267027724 267027731
    0xb010512060c07061802220b01030b031504020a0f0803090a24081e0c1b030f030c0304020406080109050109050c0a03020a120305120c0a1e022a0604090203060906090415 74
    0x21400103aa42c1103032080c0c003c5c00c4203900b01c7c0042c80103410f41c15070300040f49625242a0720310301c80354480e12880ca01c08402800030401e544591501030f0400c6c4004004aa10416440010690704120075100c0004c0c10140021600c910046082041c14000c40d004902189c80c5191111015207942403012106c0400303080104090302c0722110940e034030f04c170308a61058121606c018498900c038074038024101e0180e90394003252408150540a42c41c4e04c03485c80d08002c0e014041c40030034011840c0a00039500a4802080050099aa80280d07829101c034540103a400b651f5418480c800c1c00014000d44051000440d0103d90240c1164006032807800c0d18003c0822071806040506c0c20175001e401101c1300c008007030300511018500300c10030150380d503c1444113100081c1c00e0f2000c803001c240b00382c030450883c10181d0080c14401271084005074001418030007003a10b10180b200e05401c9911018002c0014040c244809aa02d05c3d0003024427000101c09001e050081c43e248040102007101040b040c41812000302011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 267030224 1250 267028974 267028991
    0x506061612020f0d090311030a210201181202060105190905040206070614040512030106080a05041109091515061b1507090503010f0e07050103110c0a0b010512060c0706 74
    0x7286000d0016143d0a850310618214020040e000034058003140c1c45401e4169028503007006050f104d041810300240380d150011525841030701d1109680c111550184000038118041021002c0a0702c0380f8079054950070140310102c10f0450341404035501500064a5400030950060310b0b0010b41030795441010040ca5a40c0b01180c115a1450100e1b4445034100070280549000248800c0245034261402c0300c4a22881310340c0c0e46242c2e5003d081e64100e0380140c0768000250340300d01c00c00300036140051084984807080c030035601107551614030742d60140004100504284100c0f00740d0140085010709420407469203008102180d82d983e0084440c031050450052404007148001c5038509100c3d010a00c0d5004954003c20200c0d6074005600e00c202e880460007805090028990102200c030380701000d2586412540d01882654000d0700620703901100084d00d9880c1405c1a0401d50a000c0d86010464030a00403030010480f500c0c0228042492451410103041c2d1428007400131032403841410001440380d41c417038084 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 267031474 1250 267030224 267030227
    0x23160501051608040914061f080402010c020102030705100501090f0e1b132906120606030603101506021e07060804020d0209070206090106081605060309010e030d0905010506061612 79
    0x3d59001702007034501480548540501c0e848013203801c40c3c00c1030103090305d030004403407503400b40c0c2c11490049415103c0505e2625075030011118454402c2080e819848100036141c0010001c001541c2034035031a48000905504224140d0155079114814226560a080e181e108003607001c14802d04010b161001c0075122541c02c0042010300b180c2603400c0c40310520302228100307103c80c400c1c0b41c02c0044100e0100400b880c451441000308601418450360443c40807800010650308004000310b412400060485161580b10464102034902450004030141020007003000246c3c0c0422282e0b8280f450880300d020800429003115540340b210344a15010090003001041c15034503140e040e0044180c002e003c18280d454401000f075a6010f0030743d105040d66281a90010301d604020864140100314011803500d2986044200207007a0409800513699541c1c920000c45000801c200603c0e0079010018041000e9000703003010b90845400508840c003078074040101040c010320780c80e003206045a028140c1101e240030000d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 267032724 1250 267031474 267031477
    0x1112701020a0c03030806030c04050f0402010e03010f230109050925050904082d07020f040e1504030809031315090506040f23090c0307020a23160501051608 69
    0x2c0180c910b401c00000401459032000320705100c1c0300300740c00f120352512503041031000311541101c0214034202c440f400301c1c0040d03200e1980031101c2080200082803004146080008440040d103070b4104045030b15848181c543c44a460840c01060040c108000524141204c1501c440101451410900b519100c0100300b4005400c13079400382001801da03401300d00e01454600340d40d074407401d10300a84d10164099842808060440d4550031010305140d20f062022076800d0001d03602c00700c4403150707201e520303503545a001c01d40030000082c006030305403042c2e0b05900309424090503c0c01c0c040c1400c02c8a8208120140d0b0040e8003070600011a005955001d8030260000c0003220f0300d40c81900020750084001800103003031030301c0c40c070903006440c8101d0001301e000065034010412441c4902070742e0b802141c03400024100d101003001441c0d000c40305005460301c81a290703a9000f1460301c18a414001100e0508000a1142e01040307a000ca9254030f801d45240a424000040c0081c06081441d07400c2c105040c40c14010440f9a10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 267033974 1250 267032724 267032743
    0xf0302030f07120815010e2725021c0c020d1205090418020a14210312010503060702060604020f040f03050309011103030708010905040618050109050111270102 70
    0x410280d1900c1a520340f10001540700801a070002ea000d0021070002d0b101e041280001000503151b01c4e01d044840300610040c0190180078400c810128010b40529002c4003955078420008480003000c8902c41e068200611701d1100c0f50081158080f609220462411042051204a150600c8840045030b440000c10424a01a00510010321030002c003030a20342260140000c07150881c0c09000e5a502c400c48010500e110300c5000c0d60000c0303c0402003040300c00700c0014442550b0040c1401d540d26038a080070980f0300444181c03055050348005105071200c00008421409000c04a010b04200d00b0308000082d621100a020b43d489983d0015200102c1502001290003d000213000040e5080d81c0e03003001a00d0307801c11800140414003003e82c0a45070500030084900c07c032060b80315a0700d04c0c0d0901340300f11300030100200308840c060342c0c0c2e01c0100300340c8100647c0a007206201d80c0000c100750070540341a03801e454805020b81041c00052000f5081344007104103c01004c421029102000701180e03004038a0700c060032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 267035224 1250 267033974 267033997
    0xf030a0f0c0815060c030d0f0603081201030323190e22050709050d0f0f0f06090606050a080c040f0615020f010b060f04030803042d05011b020a0f030203 67
    0x1144000c540c1d900301d0000c0d4400d0704041e030141c1500303101c40d0501140b40f1a6000b000c001c0d410810819000031030039070011841e490b180100142054803651130a0455114880224502000e28010820564011042c0502e0722aa07075001c90250072003607401c00e05009110300380080d042e84000d8042c11600c10580203414680051420358551151140d81400742d550f00c0c0001021410b140c005803400d4028440b00040b04d4024205c0c101110598950035483d40e02d000d02292203581001090003c40c44089280035000e0181c0c500042100c0c0d1441d042040b541c40f50b0089015109848040205440201e400803440d44d00f070320b010407004048044503000f8070071070f04200546d03404e800003441295800100f018400f9152002003240c0c2c1000020400b0b180110b29400b1700b040000c210900004210340b002d50f0b0000c0c4901124000d041440000b00c454030492104110307404000c41d003440910100b4003070714810040700c02a01e07843c178110b10002910341950000140003e000e10810f02c0c1014800c208840040082 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 267036474 1250 267035224 267035231
    0x14090603060409020411092d0105030a0608060106030b12060106020d030b030c030f0a1b1202010f020c0a08030a0f0801030b040b04141009030306050906091b040506040f050312040b0f030a0f 83
    0x9421b015074054000c4240c1070300a800c0051181c411041000380300d1a0324003802074800707a110b1000b0044603990310007000d0950b000c2d04e0300000207043c1c404000c07040c060040b036140400d19100c02000e214140464140d241c10a40c000d1004025940c0c002c00e140108212a00c1c010809040d4400801d00d85944280c100c0d42510817002c039100212800700c0c442808a02c20585500c0d007510521662100d11458010780556042c40c5030004e00542c0280e40240c641319050054410440841c8001190860306034019850b40d040001c4401129a000b400200710f194282440c201a505645030420390380001800185611601d80204090100328409080d02c121240200c842c0500c1c1c0f0340825002e0081e1900843c04242800c0b004551803422001e0180304a40142890401d03549608e110714030740256107848500c0c0e03c010440490720b902c600300148081c0912902d025000740c9402c0a140c80c00c101008540000340c1c0a00c01400b1070014030088402400311502e02c99240e8031000320080c010000d074214403018516 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 267037724 1250 267036474 267036491
    0x1b0708070605040b06030313230306070e090c0a051801030204081204030203060117060601120e0304121a0c0d050a0204051c0201110313060c0c0503060103051b01140906030604090204 80
    0x994000600c10b904c5004440c0c26901d44109250f074038015196a180d07040c1e0405810f0180855404100f02444000e56040304100d0789030010a0614501356044800521a04403000301420520b200301d400c0b0210981c610310b032071031030034005002d03008603c0d545202400c26800285503070304c0390701654003a1003601d064407000000d18150543ea1740c00752000324040e0060f400000365200c020326150001c0c0c2100c0024042c3e40e611400115502c8011584002030107594030f0030300040c0d04e810000f42028003803c1425401d0b0448a041030111034039955104000646500200001002c41e4800c0c4c80708200085008a403d454500600d0064056600030395040001c40c420f0350150001454003002c1d040c002e0302c8141c00a00d030114a6612482041140d02601084060030414070341702d144500e030034074000d0056900c00c9440d50b00080c01d000003a4015038941d40f000741114180381001d5543d40208800f400e001c9108010700d00405c03064028141c5a52092501200040060310b564120100d40c543c003c004000906 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 267038974 1250 267037724 267037733
    0x6040e0115060f0201020301030812092814060702190c08030d1b09050a050d03140a091d06010f030b1c0b09010c18090518160512060f1b070807 63
    0x803035441002c0c00145501000c0750340d1030062084078183c94000c011149442100d03002820a640c4c00b43c2114800e00c07400e900a03100b20402990341807541108034440703450b20a6400d0003024040400200301c030940221060209840d00002c500b400c000f011a446400c2d003c440c24039005d45980c6500094140c00005020200d20329254040ca00d904c840b11004d40c83e00b81c1c485011140e000040c050725400040d010b00034400ea152082c0c90b080c00a00c02d1800380806011003640c0c01040d0001003034071004c40c00c8010b052101540e0b51490214032407100440c80c00c0383c40e00c0000200111f0030440c4500600d52350310790390b411b2500c07006010070002c80d4480b41151040718520b80182412421100c1d070790f05510382038000101e9031240c4000408015942e442031030303160809070004010700010b400e10f8a1110411209040400180426101007513002100c0404d00c6c41c102c24400c485a903d8a0700c15281c0111080003a01880841c0054000c00d50301d04003855509051762500082c841e110005d8890b10001ca150700822 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 267040224 1250 267038974 267039011
    0x706050103030507030f02030307021b06090a030b0609070215191820031207020603070513180b010c051005070219050606040606020d1407030c14032802070e06040e01 73
    0x840c440d51b0344d55104c0742c2d0403104907100c0c042a034000c00142c104d82030300c0742c064088060000390228004d1446107080f03131250009100000300d620442d04656900e08011440c41c003044020b6000d90b29001500c01054511041c6880b114001c064030458003100070303000400030706607101c000c0c8144e010541025011803410300c040d14410b2141c1c2c00c1c400c19041824008a8103000c02d040300380c0b8110501c500e0408070160308000071504000d0011081007003d03c804804419800916001003082c108050408410561602c050764801c440b0103050181410340100042d400048010318051001c8000a803074650407400c03400c249000010103000c3c1541c0035048280b003004030300d550007402304481c1003040320b640c0d41d0183e0300d0f00c1d008802400400c002401071804190810001c000480c80381c50500300d62185550341d12405a40100783c0c0059030b00c04189a124036010220350840982c1891280d80c148001c890020b40d101c4240c00741400a681300c00204002da00c81d500882c5840d9030380c50013441a0b422032080c90066 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 267041474 1250 267040224 267040237
    0x4090207060209030c030c0607060f112701080402060f1602030d0908060108070506040308130906030b1f0f05040e030c01050f071412010608090c040c020105070e0303190e0607060501030305 83
    0x5e01440310080c2c01e0340b030b00280605804c107000c1d210742d08264080d141d400040060410754024079846111142d4800e1003d80208011581881040101106904488580501c0040003414004102c05020160350703048280c407416a02e00b01c195654100081e449200f400060400a4142c4900784401e000f9a400105101c00da0741d0b103204070b59a9a903203a040e02c0e0b8600642c4112600b00404020600100b18a1402070207480302d6a20790036031a035610302c510421107038203a000f5109800d0003000d2201d03000420860240b20128401c00d80c810504050101808034210305c00e80f48030707070707a50123004443d40c0050041e18000c0010300000c0000785441140078001c200100c0d804000030b01050740000d0310110903815540e030301703450000f42e019a0382002011b0f1003d5202809840551158941d950030660b690300944900080300e5002045a00304004040d02c41041c00c1d8145121303130810321170454050b455001e850f0400c1001e00d890f01d02d80c41d030540410f00c01e115000f4040c00e003500707200c004004d054100c0300401c0ea = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 267042724 1250 267041474 267041479
    0x90b0c0c0c01080609150d080406050d0b09070e091504140a06060809030a03110d1b0f020114060d0602190207140103020a080402010c0201110d030509010b090603070b0f04090207060209 81
    0xa9001c105401100c8040c4121a640d600c070881d040894902c00500000c1034001c0304c050712501615140c2e80310050590000ea10240000c0c1001484c1042e0600a028100c0c8000003510303d02c6003810181c0f400f8200f8003c40990398010b02a010005030804441e1070000d81e00321001d003041002d074600c0c010b507810b507040840c0c0300400141014030004006c3c0c401d400a80c49007108801440c104581044220003a140302002d090000d44144201402510603100344141441801c0c10300300380c1d544001003d041803a1500380041035900d440340a41810070503070701090703200c0c60442d030000481795a407070490002e020b002d45a845d61030f80041481ca116030000349000c2528a5941c86841e02d1507414011416441001e00b220300151214000c140154050301d40c0303182141c81410103028024000030b90521300441406802e000a0300c803818001161710a2141108100c030503240c4000034507121010035510134241c0f00f01c24500c0703400904110044407440c25100904881d503030655030342080c3d040c200041c0d00020383c006e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 267043974 1250 267042724 267042733
    0xc0c080703080d02030c120a090614061305090120040e0615070308130b0a060611060c040b07050709091104150305070b0d091a1602010213031203090b0c0c 68
    0x110410001010300880340d010440d94a400200015000070f0f400191901c52134501c14003003001c0d82a0190407041c49003240c040d0006100016041100585180ca805d044090380c0c480c0a0050035124070740d1428003c94203ca01040e25251044682c1c0188007220601c5070350b0004848407056115614000c00c12520b101c00d2507006a01d4a40401902541000004500110030050100001d014444940d8080458010b90b21886106e80712411400d404540050741140d0319881840b826401c10200c0d2404101d000042c00301d45030117801e41025108a000341010f03040d001c42c401c0100001002020f024040c40744040c000d04003189006204000003068280c892800c01b1030201202c1d44030303880d5404483e088001444402d140044880300783d4030140401c0c0d41c4c10313190381d0000d021840200204515883d0700011102c5454091f0300708140c01c11041590302164010810002c042d00402803620541c1d8000c043c0219943c200c84081d0010001404000e0061864104000044028001400b02076006209030f5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 267045224 1250 267043974 267043979
    0x10903080106110d1d090a2309060109111b010b0108150306011401030e06011d060616081308060f040519020307030803060d0b010306021809060d2a03030c0c 69
    0xa0300d03d80410150680580d00c00d0100b02000c1e4400c0e0301109500056981e8200c8806280c000b02d9800708040340d885042036110b290300041e12402d0364014a1210072001890402d080034110320340c0b103100603c00d000981b615222504850b0104000301c1d00c402c40041030031068078106444140c00f8100880c005400314409030009102c900329040980790b0500010094540c3d0780c2041e8400540034202c919a904069135906254820002044498064200380e069000030b02440040581e401c00024505801042c051014042c410011068103400310750010505455030904d1921140d00c10700d039400703c40f45200e1802070114041e540420f0501580c003409c00d0b9030010f04400309090000881d42002034260344020002c00104800c2070103980c000314024005641154036407620078901d4401e8005640b4154009503004c66003500090b51b1600a8083d18030000a1401ca00020098000ca010140c180ca82003140e15000800601d41140c20201c01089064040d4403400c004200d841c1c075100403201081d0b8201c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 267046474 1250 267045224 267045227
    0xe0a0b0109063006080a0803040510020f040308031308040608090c03070602031b160308030a14060d11030f0610170601050a0b0a02030d0501060c15050106120e120a02010903080106 79
    0x619a995541010a424540c00540c800f806001d00c03541403000c2941d00e01c0042032402e005d204d600304c010f0080281c5c68403800d090030800d08140b00380140050b60392041118440d41d19200090b00c003100d40000b5210380740c0d6140001800d12022059006225800014010800c0b40c1c00c400c0c01c80c0030704034100031542e0380341801040c0350b40d83c0d5503030007010003580c4280300540d8880464072019000c000383c0b500b81c88182e4980e40b54440160b100d50011207070408007008102c002c06840c446d2142c0c54800701c8008030b06043c0f1402040700781204c058043c207900e81b03c01d1040c134070f501d0800c005032102d40c10303400301e40300b92405090000b1488194051000d0440004101c20f18001c00098020b0581e4030081030440400d1500d04540030135440303040c0d030b80150300040c00b00d00d03d078022030f00c5164003d01e110349440b84007038181d28140041d08511100d4550040c5004014001594041c1c4980c05c0c41d0800e000024001c414000341500d003080741c80b440d50f1148000240074607495410340000c0c2e1344500c030740c450091607601c3e84030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 267047724 1250 267046474 267046487
    0x3152406030f09150b03070305030a020717070311010e0f130617031206090615040603050a0605060a021209030307080d09120c05030a2006040515010b090f0607020301060e0a0b010906 80
    0xc020742000340301104e40300c15035003a5102d010700050040481d0300f115942e0785c4050854021009c1a03001da0000b880420601c11807100050500c00860003402880b41941c0d2250700280401c4001c07030400c00da46d09405010f0b240d60b040d60f0030b0041c000b407140c0072030a50800304001410080c014401001c030807001100b0f1456000050710200800c000d08150700750340307500501408890082000d50702120480f20000030941da18000c1000c1c11040d039001c0340340d1404207801c0d01520350950042c0d00641041000e48401d5034081104d0901031011915140d4918506001070b24500803101c3c0a003c40000240003d07060444c0c1e0304c440082c034442c1c410032500c001500000e641d03141c505240503009070800c00400c00a24840c048100c2e011443d1100c000c0c0103110000b5091074480304403003c440079401000042411f01002800340e00400e0b20703508592508410002248410382131a44250183c2c0020034a20304544d82900584054004001c1160b0907140284660b806009940e005034089100c6400c0891464031901 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 267048974 1250 267047724 267047741
    0x30902032e02071e0222060501082401030902130609091502030106170a061508040b010801021e09040906020307051c0504030516061d01061a0a0903152406030f 70
    0x4c0c032209080b6211081c82492104050100ea001070000c41e000c10014041162a031020010840001d480d42000c1c009454590050300d01c039201a100220031050f003520203040e885240007881c003c1680b00351440859121220b81c400c07050f0003820000042040000c541c0240450340c02002c04c10042480b2507241030491000b80500c1e000100100d6007002038500c0c0c285402e0b080540a080042e04030750f2802c0420f45c00c0e01400710000010500030030712090181c10312280d409002404002c61a00c1030301508480982c3c00c80b800120b030f600303001c41e807001d082c5c0d0b82c0d52081701110b8006806540e28a400d01d0f0040040d0f00030b80b0190310040c0d1011014581822070300c140c921455242d103440e450091040c1e00359042d80c0800504031082d40c0c8491400c04080301c440f050400d0845d540c4e0000c650079081c221070f4000710705e110a07080000f10080c80600e0007103600480c100200c0340c00c14003800351344114500f040e002e0401003045d06002480c19116031a0003c01428030f20885005640401c00c15441450000c241c075280c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 267050224 1250 267048974 267048983
    0x1808030d0e06060d0b0609341206050306130201020a210f17010909020d020a1e050d0b010b03090f0303190f021602040213081203061f021c030902032e0207 68
    0x2c400050487c00c1200315a0f4204884c8a007030001030341c8286034150754117540b4110b60780c00061619403041c0c098000b06450b88005070f0000610a00c1d092a0200b540c1d00740050507101140031022214040da4001d01881c085030340c2211115503c5860001c00c00c61034813a44450800103442046c00c180028031508900118540e41c1202c4420f0342d01c0c02ea10540600b980b5075050764001542d03a05000143d540807000802440c1900010240d40506007071081042519845140a10840b4500c1ca0025900b0018241510700002d4070a4907502c0381d040349841c1c110844085034035444000140f1086464071888a40500c2484106200aa003241d0025060340a016405020b01d40c0c0b881c1144010301e441d8000c0e29400d14858114000e00d82c0d100b03140b516000004111902141001050000d541029642c903c00c074801d070003030b5451402103010000e5550604144020810020007034490301e1910981003801e5450b00203041706c1068101021050380807000c1c001715203810b020040c5605001c0031900a0f1616103812 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 267051474 1250 267050224 267050243
    0x16030b010e1906022b0e0114070b0a05101a030a06080d05031009020a020c1005220e0703090f080c010603020907021515010c061112010e09101401061808030d0e06060d 73
    0x10305170a440c504a04004241030102106003c10b00c01c0101001d0308219029511510351030808440d82e1040f03600c06001880d608030400b20501c40f05044802403901f600008010035500c0d07641c02c40040044c004c03134010110f0b0340920228108003c1c2d101f00a14043c10900c402103800d140d0343d010200487c4101400c9501680140c99035181c00d02d05510301500501c104d0420030b261840f01903481e220341c1004011000141210780007800385000e0080c01c01d82c007820a050400203104a5107030300310307118518880101310420001d030b803400b090000e4121b4002141c0c003410328980781c00d013810060f49800745184000c52444c40040011054003030415800b16441060b180d4002d01c0c40d0300c0e00c170f080c041e007580d031400242d00b2400c01c03101520404040c0481c1c002d0085100c43c90f454281801403d0610303884050700d0641d24100358103c012907158507002c03811595207080a64aa22603002d2444041809501c40306e018080030982441c6006030b90416400c10b11900c0613100c00f5a914010841d203009000405000020f0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 267052724 1250 267051474 267051553
    0x108060f010c0b1303020f280501090203150618060f040908090d0311070608061305070c0b07120c080c0d180c0605070204110316030b010e190602 64
    0x2840c54003100124018502095202550340f030741d26051909075051051502585101e40505505215191440c1242d4004d0201072003404503c1c82171026205250782c144421003410420080700f50b12102d8001d1b030142c2511802007044041c0c0c4c480c0c007012503e41d80221108958403c050b028034413154818074000b000d0b40350711070010f41440001c00c0380c07035402c841c0c0880030080c05115a480602440c0a00e109a8a4102410700880c0700f07400e18032240d001c40184a480000c3c010161740b600c030800c1c103001d0103c0000400d550b13440c41c1200ca40d0410000905090702c01800d00010950200d1144003845d02d442c41031042010f01c000494070346000b11042a00b05500b0b10800c05e04e42d02c0303032b00b11220303031070002d0100314401c1b109403039501c0d4100c080d40c04440414400100e000850905000c1d00b148130001c0c80895056180002684106640c040b408604040da504004201c50b8000c803c506440c00300645a21a880d8a180e41211303140c01d20f00902025109103040e240b16403184d01010001409280503050380d00f00b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 267053974 1250 267052724 267052729
    0x20604021e0d0809011b08033913030b0a0e061005031506010207080f0105070e0603070c020f04240f0b0903190c0e0c03060103060603061a030408130e01140f010806 72
    0x4020807851410444600158800c418400a014290a00130104260b2345d0a28800d200140c85807104401c0d090061903a62040c0348400745810700d01540700700d02c1c0c5507030b0b0000200d480c070803606240c200900c1488107a0038000c010b2a1035008a00e55500b060803603145454403c40102c0300c192074441c0b160305d94440c0203019902513500083d2500721070103004565690340c4910300c45040c442c45501e81c500a81d503c1082083c0550301c8041c1c000ca104060350351520358101040f0051201e201840d010780105a807141590090300e595001172140c1e040c078581240510650301141c05c01f0400c600ca40310407540c3c8100c000c80e0602c001c2c000c4801078034000300100b0a0703807030b4004c0f02007083c04061400d481307131420f41c440000e029545901c2c1c035200794202d030402e95492800800150449195030010820136181900c1804682c0c0c0c1604106a40701c103a1424075120368540c9880f83c510300c1360100c0d04107806002800010240050703082c00f41654050381c1d8000d10603085005008040c450054407a00041050f000b281050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 267055224 1250 267053974 267053977
    0xa030f1a19050607080d15140103020a021e0106060305090d05070f0309120602030108190c1e150f120e03030403051602040c020f12041a0903071203020604021e0d08 72
    0x12014400354507958a100041d02908103207803d0394100d40008240381741c01258490307004038841c01d000b1040d0160421440c50092a1041c03209814958000303501070b48640208070320810030f850a20400b00d1041d178000014040c0c49241300d0080860308040100c0e05000c0c000c03c200c40708201580e40e290405070300303440c2c907401d081c1550810340030301202e0b500101e40d400050b03501c051071901808002d40d0303d514240c4a240351090000c8204440000c80c80701000041650b24010120340d03003005810749000d01c0001c104840101070b404100c070008080c0c80080e035940c0005c4684808116900d440d20b44d00c00070140344007039601c103001d5107045800800002d000070f40100090801c0e801d46018004c03501e01150302090889030002c0c0c00f0800b507404407045500170311041281c160000c0b00d04220506141c6403510300c0e00f81c00040d0180e05407504011030300c00794a4404004400003400d07683d4100e8490892810040d40301c5605070703002e0f03000d9403802400d0310202848848594052030007130500000b404c5e190b02c803442e45 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 267056474 1250 267055224 267055249
    0x30302070312180b0708090c061b19140607051c111c06050301090213091103061e0a27060b0604080f0d0e010c0b100f0b0a030f1a 57
    0x42c060700380d1a200d241003240c032980040180640c684548060181811450848000c0c07205007040442c004010300c3d2a070114001941e02829035001d62900401003100b007029540d14803c1d17034203100e181d0400742100f1a01e0494071340d00303000301e443c0101d8048050340a500c0c1e040448007480401d604000c20311600074003420984088080e0000041d40b6401202c030080c2710780c0064080074040c081e403281c4040c85071032403040e00000c0504034000c00940d2050750200b01c000700308c032100316012652500200306229920450f509003070401016500c80d4a81100c000d2408100e4100840184e00d111002485203122131140400d040440380480c0720858600203181d02d1020888400c440e0305403903c00907840d0751030f044080d00140c0084005010503403001c1040340d1901c8401c1450f80104104820f142d030290b41c00034411400c075508007541c0e1049940d008400d11141005078000a98403c198800149a003500006000e8074000741d9410b00400700c11100740d00030b580034150000741d004a16141002680303000c0d02c40084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 267057724 1250 267056474 267056477
    0xf0a0321120203010b130807050a1e080f07210c031506050307080304051309111e0d0b04030f030e060610030608030d0c14070c06080703090209071101060e060d0303020703 75
    0x492080c1d10640001c0e078100ba40003540745400440e6881401201c041c003000600212801000303568904400100e9402c41440745d100d6600100000113942004c055851019140a1341100c61328050700310282ea036840a4400d003030100007080044203801001c22030316420715030803c0c00b8100c1175045843c2c0300d11410001c0402020385566100000f60340c1c809004c000700070a182c2d00a191658509000d0021501c11042c0d102c05407494201043c000600e0007070103890000c03003a520b124059202c40864205e1302101108680d21040041741c0104010715440041d2180d4402e955000400c0050300c0b0907000d1f9094030141208a81004001400300c2c20104110b4480b41d80c1c038036011800300c1d6140d4800f8219400005181d84807510f071b0101e0500e1030f800c1000012451041e0411b0752074a0110303110017582c1e40040c014281040f602038003054203a4402d810000f1107540040081c0e184e400c14100103040d04c515070f00c0540c810b508004000600d541ca0441d200c0c460200a06400c045c00481d1b90110000c1d800700b00300307c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 267058974 1250 267057724 267057737
    0x3080a0b030a031e02030c0a03030203070203280e01050c0a0210050f07080c12040b040506090f0414010302090709031106090a0f060807120203010b0912101a0f0a0321 73
    0x490075a410460b410300b06001ea101c500b0401100d18450320a141c0340c4000d03c09641c070400c5546100e040010718247c546400d0f150060f01c0e80c6500300100e080d44500310380708043e03480006403607440d11100d20701500501c4050b10784c0009690010010f4845010b410340d9a8246d0304002c07124405402c2022906040100c00c1ca4164503240c03004041075580e8002700c2e02074807203040101340f81d103039400d04000110030260203100441c141880d1807415040c40c4a18020309029590124000107a904c6078544d000c00303281c00820a00c48000044215099200e0074402a84656182004a8812401000c4400c2580d800106502c0071040030000d0103105c0d80a2180c42e5004010800d0000d02c100c1c0618000c0c000d000300341e8a8464500789408000c0808040c141075a8403188104010031000580e80122100b0310826a41c0f400c10784200c64030f42d0f04001c08140040c018500b804808041e0082403018035a0003501180ca214100d0303800010310160000c40d00004008804060360240d4508121031040103201d842d20b1f014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 267060224 1250 267058974 267058991
    0x6050d0908041215060b030c03150103021606090b010902090a0306090503070203032101091109040b040914100f060b030c07080d150939030b06070b010e0c0304020d03080a 75
    0x3c1a001042540035100034480032a440f0b02d2810500840009020b08600d0500b1800c1030b40000840c1e100150260894161101410760903900980641c0c0c886400d49060958105036424110042e00249070211020a140320001c1400305a0744261954100041e200503003450655030349900511100340c05032064401800000d006a4081008004030840c8140ea0f041286c454000c0d040c0050060304210b07106030810706110008440031043c1d94845804581c04926400b03c40c0100c5d009291030301001c0c120100b44010b500506100040880e000c40c0322070010040b000c1d20b11248c001322805406a990513020802c041160f144024014121407402036103014a40000300000104881b05054401a655111181001202c019100e008002c0c030352042c6600020107010300c10525a0b01c00707250030007458550514090303224401d911006034030001030800c43e62070a00d81824101c04100344a9100c80100f8440028224494542981d000325400340c403160071328640b60340a48540d20001c100e480c10a40d680c82c071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 267061474 1250 267060224 267060239
    0x405120c10090c05010206090c030a0215130303020303070e1503010306090215070308040b0c09030c09070306090203090601080d020a120c0f0203060f0a05070e06040312170c04060905090106050d090804 88
    0x1102c10051042801e140160301d030000190a011009100300d0164100c00061002c989000c034048011a038122509200103031320141d0210305028034680d64002c906c40000201c10580c000008500858840e02e80d61810454001005045810140c801080715420f000400005066400c5180102d100030711007542481d41440d2a022604a00c2d0b00382c0028003507600f07000c10f0100d448400385c5c0050900060740c1c988170308100413aa881e003d401030240119000000218010302c40c0d8441f40280140380d10940d42c0c1e05005203150350f0f8200a020360462806003421001e81e26000051151006500c900f25040c2c8003605401500c011030b071400191138024205880d440140e805001c2e26103d45184d44080250341420300000c000c4070b0b8000c04030420321503c00000349095403444280c0c0c00326680007000d83d04030003820f14103e4104a06a00100080c2804000d000580346070a0181056070a160b84445482e070b034039002c000e00c0c44001e128800226070100190740311b02c00030390407607901180210b106620b0203a89120 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 267062724 1250 267061474 267061481
    0x50a0e0d0801030308070512060f031006030605090d0206190f0605130207030e060c100203040204020705010509100f020301061d01090305101401090903141b150103030f02060405120c10 81
    0x380e650001d9a000c006108054101e1080c1d0b401001a15007642400c440d0300303000154005c0527140c0707485000400b00380400703650100003000b4408a80407080c45042c1d034a14150018040688030003180d13004110a4000b12840090024801c00340c0c41c4113403c000d483d000780000201702d06015030070000c1e2200000702e0f440c3c441395800440d00f80001c40050b0b41d0360407410f004000e20222500b0368440c000402000040584c0010306200301004602c0050780ca88540c1f0015000340305444008089500742000c1040c0c2d007001040c00304001000080a100a41d002800c140881c802405408003044800114114140e3300001400840d82c0c103042c10400c140d140e4460302e241060b248506170079030b9280e100c024102c10b9032188860040c15050400d00c01e01246a07005049a807014081c68480080410808040410403500d40344486002050360560b000304000d10040a800f400160007240b46111a541210710000300c01e44919001009450003200d0240b40002070350058421060611911100120400044c031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 267063974 1250 267062724 267062743
    0x60609150411032509090218030601080c010f03060302180408360a030f02040e070f0b281e12021b25090c0c0501020a03060e1018050a0e 60
    0x441c0f030b268580390080380100303840031001025240c800164405440e4020390710100b6a0420308015031102d40011881d2501d41c0d0288400c2d5048c400e500000800701c80201d2943ca0380c040c00ea0b90a0003041105800b1b6042d6100d92100a420001300c000a842d1a81000d01c1690054462042d403890850050a203141040000791007203d00d0440d0741d92905040080949040c601d0004d44200c0d9003545503031209000c10124440103070080d61609804c101d54041803055401500c00701c0e801150303040d12450740710340a400c0308a51070b80440d048070028004e01c402c04250742e101d9100360b8400310101150035a50f44d0b0329182801340401d100002c02b008003d4a11800070700b07001d0100d00481c0c0d41e182c0c26088103034604031000b0410080c250750825a416402d00040c6180280c4031a400049020076401c0b508483d050088070000e005940b010030350300107181d8580c11100484030384810300c0c1d6013500e55803000b01c000791003072090031188901007000440c05207042c1c11a0303a1003030903c240080e200703101683c0c01d070903c410314 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 267065224 1250 267063974 267064001
    0x5090117072304140106020c1909020d11030c09090a090f0204240b09100e010801060c0813090e0601050103020a05070318080d1707030b010914150d0b090a0e0606091504 74
    0x1300103008241e8104040c00c1c50410031900e060780341d0404114a1003030005800b444048940005140c03112004a80003800b82c00d05000e8080d5980c948072520700c505130403543d000d0b4464010840802d00380d030818003560407900e410003400c040c0d40301503074200401840c09515440030030f41c1d403803004541030f440300010390010440400c00b20b84e035074108001c12008400d0400c4000500512180701c1d08903036400458a81500ca00303082464461001d4100290b813401001c0044844c1d141290020a8041564001b6060350a240b8211100b50362164019401d034081c00380541c0c0091414482d000c00720748a42e902c1b00320366003000c42800303802c1d84910065082c0004040840c0102e0864207210602e00c04a900c0d4a41c1300159240070801888060002080d10240303200d0840f4240811060415642d2088070584500d4050b1000030340e00c0c020203400030045c2c2260340300648902e44040000b00d21440034002c40030301c054800b019050554a440410040080c003501410011003000d407103001d40d4035203100340c3c8000c1d03415 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 267066474 1250 267065224 267065261
    0x4020d0902010e04020412140f1006080c010f0f050714060c0306120c011e032405030f060103020f06030c1908250f08150607060605090117072304 64
    0x500024000c1103503041c1c414000e85c41044104004500c01040740c2510342d01801c2c000c940b01038403c140b0b18100c4040c5480c00280241c3c03440da4a940d0840d4005000c417500796080e04d89000400006651007180000008041042140065911407041d401018501e00c0f541c200c085110005800c9841e04100301ca1603c1190400001d0010618100b4501126070320300400030100505d80d480001d11a96203c92a060240806541c001c3c0b0180a0382021360140c04411010740f1951300440700a00c0484135101d001e021340100c4508400c04030340032544604ae02c0c1c02a0a0b090780416410138400300b98001407031010a203206004408208201c81178282d124078032956aa0303194188040620036400e40c1e0111020140d2a0407560b01140e90041c001041c4d02105003000c2c0090742d121564007012000c24500c650b489a00040d103a010040b40c1e920100c141c03401134400b445203a803110b000410061440b030491409911080f0f08201040c2c0c4550150008001850384d148421420740104040d07804107000c07014041034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 267067724 1250 267066474 267066491
    0x503040305031b0a0804030b06010e190f080c0108060d0302070f0b04050307050a060206041419050102070b070c0f110307090e010912021606030e070b03181b060a1b0204020d 76
    0x4281040c078003001c02200140c50b01d02042d80c1c0345c0c41d0500c1a03100083c00b40803c0000070700c4980c0030380041407400e00c000d00b58400745801c904000f035110045014654030100e00c9903012a40000c0003130194040b00040c1c40e1496a52543d0701040042684d0200c11402c43c4642d05010500382c1c4000e9294004160f5a83d00c9a01e4904103404c0608121451708a10300512803080b0400005500054184e0040c0c0c00034681c45421030b200c1840703410484000351042c4400311b44610001003090549c018111103000c0e4250081075103803000304032502c0007a00d40141c8000d80c0c000f4040d021424a0300300c08046007004084404050740d4080c47d1054450302c201c0c4980b5659144000010300c1180320018003030002d5403011b0321040d0781025080745000d100e030040404166079600c11503a80d100c1000518050080200903e45034588442003030a00c1c980f2290b4a90703c1d019501001c0c58240e1040c0c084104403c1c000c1440b400c06a038182c04403404030050780c07102c580c0f20b06c0003200400b5032904d200a000304542604003095550 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 267068974 1250 267067724 267067747
    0x11b141b0727090b0103241d06180d050d0225030206090a02061b120f0702120c0108150d15020c0d080603030306040e030f03151f09060516050304030503 67
    0x211014008114a00f45400600002d6800d9100d60540c4c0d40041c0c0e4518440388000f170700944030000034010074035515024140f030710405d075034960210307188522040351120303541c002503401d0032600c54a40555591100340c0c001c002602860242502c0c080b4800d00500307045100d0360100e42d802d40c01001284040c076000c88602495414002c8940c02040a0000d041006456012800038402c0308185a104103c3c400450300e10b503002c3c003508030710140c0c2d000e1080e1100e41020000360300780d200c1c40b422403150031641d0204c415040007207802d8400c640141c4480069503075550360000c040100c44941a03008050147d12000101554000c44c1800e001110042c0c65040710191245013601440f406002d0001c220200a1503a400108890b8050410350b8046000385003100200d155000394114504488804000c1080f42101c5641c0402d4904c01124680e075202e0014411340094580120765800082000c001445403d000324010160141d00c0c003d1501d660002d030700d5040c00c640040d0800c8405400009410b403120 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 267070224 1250 267068974 267069029
    0x4120212190f030f08090604060e0a06020f280c110103060b07030201050a1a0307050402090103090c030b071d060a0e0604091505040501081606030c050d0f0e011b141b07 74
    0x350036082044d0309003061001240e84031f1000f44000e0030a82c07a05484a03e4040a012040d40154000020b64581c00120710400454101d40c0c409460528a0600c503c80005e001d810390004144076190064280b8080e11400c64400e04240020b050586420b0001408803200c401040214041e60000440d41416681c030015035003510803d00383c0122059100c1543d03070300070811104030340c4101c07001030b134030740c5450010780207416101000b07031000c1d800e4500041445260031806d0301c205959504d981d070340302d04184184400d030041d500c1d943d0002000d07c400341440340246051b000c440001070045003066a9822520155440305032848400c43c80801d040000341868024180075103000c2000d00303192100c5520140040c1050302c5610201a1600440100c4c503000e503046424000400400740000ea003102504000340544906218282d80b0300060102054084502850122456510107141074203104259481d500b0603142c0c0810007a040c1c4141c680c69404009240c003e24800680040000d00080c3e0317207048 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 267071474 1250 267070224 267070247
    0xa120f0501080c12160605120603011a060a09030803072304080d08100902070f0b06040608060a0b060c030301031a0f10050402160203060f190204120212190f03 70
    0x4840c2400d0052141120101d00180568002d0740c00b0400d60a005116514001036081c0c0c50048003c84040801c0c41c907400401405100803400c1c0100060b141c440505080b9200c60325850780d00da040a03a00080c6140120040c03490501c2460040e880e9030301d035280d5505503030040d640d5034081035024100c3d030b089008000c060010500c2440c5c0c03c07801c0920b01806191560041036800303007001202d03800515160f413400c0c4401701400b89100111f445140900c0c11500005004100b59039120840c800941145050301404003520b0241c40508190340701e208800e00904000401660b000c0d5052090110032041000510300850240022240041c03403001d00542012002d40411032030701d01c84007000900e2804800c407404580040d1401a640d904914003100e190861003002036040c01140c00380300044a41204072070088805600070344112601000c00c104a206921881c0e00004503129094003618015a01d08c10b4102e000e026a40042c84841d000b050701c3c014030000b140d5000502d103214062540c070010b46849e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 267072724 1250 267071474 267071501
    0x31407060513060507022206170c1503061c06020a030506030d090501030e07030b09060105120307080a1404050603100906090605130b1804050714010305010305150702013e090607080903120a12 84
    0xf07842d2b42d004042144112409100040204004086132130341e22a5120a800d64404020031510b2003107030b140c03490103036011182c3c04000a04000101f0594a0007058403610140b043d104c4c2130700e5500d000300540151020481c0000e1602442d600000461410403c091089880b01d0161040b58140360801c1030380075040c54040f500754003e000300d00028410008036100c501d041c0c18043e0780c01520801c99082485540c12440d007110780070052004000d900c0a1000948a4141040c0600c0c0e803104603000071a1410310038640e000801804107494000294480200490040e00c401e4286403201940b01c174001040e18221078560146808000c4e40c0281803100340c1e00c800900e82401154034544481d41da40703900400300890b50320138002090125000b540030803e03d085480d8854401900c03007001803245d034030300740040f0280301c1d074803000e00720042c80c0400721228200001c19190522145444100d45904002c00b410707050b2080716030b4056520008400b5148a00e01035641c860000906030740e20040e9003020b042c401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 267073974 1250 267072724 267072733
    0x71a0304020901120204110c010f050c030603070b09120109030c060c1b0308071107080a02010207090203070503190b030601090c030b0d050c06070c0e0103140706051306050702220617 80
    0x10060b90350340451811145908140350b14000c8038000500104507021810961101c00105400c1d41007040d00000071044401c8030800c425601c0b1450303400d262108640c059070507009400c0903c65a14510040c01101a01510b02e4a80c40706001210b421916140c6040d0701181c103c1100d5010402c2601412012a9841c541140c00c0420b5120300300e000504030a00030240600c801c00501640e01c15038142c05040800400c031383ea40c681d5041050f44820a4400070390050082c92400b02e44450f05000316400b0344050307568686035540e05000511840c110308a001702c0740c4d40302c8035000c05541d01001024040c100000d0000348200c0c02e044003508507003407501c03020b00604855800c9804194040760324034000c0030540f41c0c965140703907900e803195602e8010381114241440041c004414070407021038030400c40d600c7d40c0c110707080d00fa140c2c2025031341c1d03010b4164085c031501418002844281c1c410310143c0003c034400340480c00d00700c0c81158804803c0403c0540c0e000b1035039840008111256402a11201500005004c2c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 267075224 1250 267073974 267073981
    0x150e010807060516080903030d050103060605030f03070c0e060a08010501030b070806041503060b0604030606081c0503011a0f0d02031303030606050a050f0c07051c0b0f011410050d0c02071a03 84
    0x1004005810070141c03025070080346c2d038a2541c4041c01102ca003200c1000c1d082110f1368403440c00c00000c003464003a0782e00920541c40d1810203c10008101e40380c098015810380125894030044a01e0824014142500019112800100004e00b4050a800386101e039041819501c1d003c10f00900c100d800030030f4140f180d810810400c00c041c2c0180003441c103032900040041036010341000441c0345481903500090555113000300c0040e400e0004107200d4507a200c0800c4200c40d0b070402c0c0c0411105400300380103000c09421542000451014840014002e000b14504006d0070100d00307991081c1243c10407a5030100e800300501086c0e040660600c940000f5022900b401410640d1801c0300410354000c60401c0208601c000070591000c20080051800500c801094180030001050300c8134184901d0200071151199000081684580480074032030503101440d0909074026584410003c011282186000911208000d0800c1c0400fa5019010341d402c5a50010000c0314076044001c14644409210100c02c0310041c000d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 267076474 1250 267075224 267075247
    0xc1003240321020f0f060103050c0609100c051002070501090b07140405091305010c0c060506090c030f04060b1906090801110a12020f0d0b0f03070501120f150e0108070605 75
    0x114074003a5200b002c01106140115001d9103010074640041900d0700c14030780e50142403203000039618162403007031044e5280100500b09000c0c00340989851542d1002c480810608018400e00c0e00c0558180035808945c80c030b4015084000072030340140020b43d02a5110070b880014420b150392996000146854800d80d02c2c40c00d010342c1c0360640146e0060601c280000c402060b4211520303214114081c0c2c0120003041440100b100291401c1005182200c0030f81c248400100300340f81070010f00744a40f071803950091465a40166140b8a140c00500c01c0340c0d1940c3e5407900442d29203500ca200c40c0301c2100b1100c0440c8007820002d015105200961010503035030304114480c00308410403030075103c0314001420180031503034400a1000281c01001005c0280b00301c08a0071400f2f800c00d0b5004440511410394000d0b401e46001414107896841c1070040b030b0301190b160385010091884c1039000b1414820b5040c0300098002c44030300414200fa5081d44030110500009005014001007840640028040d0341807452901c040c007010b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 267077724 1250 267076474 267076493
    0x501050f120d110703020a260102040806151c11040f02130b070311010f1a01110d18030c0e0f160804020105070321060801060906030c05040b030c10032403 68
    0x50880800c2002941c000f5240400c2210201460b801070800143c140c4400c8000b5003c0d90100d0207003800020389007801404030301071007190f082d42d0001d00980b8881d51009410015030301613400c0c4a0304084001c41135090b0100009580c502540b003120410007502081c020882581c51074000d4000c2c0d02e01c10020010682100504681115070358074620b40c0702d007040d050641d1a82c04280d09440f0650030020038800781039055000c00609495484840c000035901e400458100c048489804001d074000c01700b41c40c1190003550420204141e03c100302c0081c0d2344035034a40c2100c400da40e21200d41d404010341444512030300311068550042050b600d1030860030038500001c20b40d40c00030300064140803001408134203052103044000078034a48102c80c51100320b40005c261004004034440e0f400707194030344030b800700e0101654040c0c071003100e400c880703013441040c203000c100070003000c038036403142da00d4415100f048100d900d40180840c1011040d44001440030f100c003202000c00d02101001210b0340c5455070003800011000c11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 267078974 1250 267077724 267077743
    0x60705030c160501090f1a19020601080d030905030d090602091002070f14060711040f0504140d05040602030f090d050a0f0c0e1902030709030b1f0f03110607050c040207060501050f12 80
    0x3100c0048050620b4911700440c45141448040810781010003501e564001600e9030407503003801d049034000e460009045084880c0cfc220001e10540040100b08400420f9401141c0c4045c090840103207040010030005045101d0024100c025801c5104108002da54100e8104010640d01c05c00c0c0c080c410303003000010618031070500001e0805482c0810601180c5071a804680d600301031103420040760815092180000090924964a42c460007040e2901c8078451410b5908903041c43e00207606140d00e0000c102000e40203842d010390405680c808036404600204001400f0341c1c028034403180c2c0d010315410001642c404c150000c040c21101c1e0000c0c0814001501d080315400003415600507201c0c1c403075600440b400485980b025000400c11801e010220107502c1c2c0050301c990364000c002d616580e0f200d0407507051000d540b002400820726a16240021f01b0444002c28075039100c0c2c8191445000c00200060490700221030640e022070743c40e0014050f0742801484503c400d181211008014092a02403e5903840c04a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 267080224 1250 267078974 267078989
    0x1212040315110d0e06070905090114061c051b0403030804030c1415100909050712081308070e060f13020c0a02060706021e070308010311060705030c160501090f 70
    0x200c8101c060084039500c04030401d08400a03482d6500102c2d41c1003806448112405600c034024140807911960041410404464000e4642c86244c0e180c0a0f449040e540a881c5054005c034040001c400700c0094203c0c01a002c0400410004090074945c00c0101c0d988400303d01d1505044c0100030038030100750804042c0fa8015031610340014200d560f0b103854411204240c00482051003644460051a40c0301c01500d0700c035210f0380c40a20805c5a50f020400159600d00d80081c1c180d410100c000c0c80380c1c180c0e0302a0026401d02440c01c1601e41446100d02c0303070390003049601211064101c890300780b18420101e904641c000104603100501090a800001c80074000420606451680040c00000f080b0082c0159010b090300240159100c41c12414240040e600c060142c0da900350340d050302424113803000001e843c4882d40507510403d50380e085d69504048880300c449150340c40f21042c401800001c60400041072042d1004d8003425030000c0e9003070141c120b4010742e040b242c14060111410b1002c0c0d04031a0346d620440f02c25 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 267081474 1250 267080224 267080243
    0x3040b0d020711060705060f060441010b040303030f05160c0c05030a0f06051812030a06050909030a0801091b080c09090112051203150d02010207050901060e12120403 73
    0x580f410f2510245045103003a000000480d4180c284a4045212440345100c0c0007410002e640e40c03410001107407104d40c00d105655034240341c50070080750219080c40d80e054100c5e14100c900740b410240c08100032002d07171254800c440005070500815915001d000360254501c0002d00203800e089240100c0c008000d80032900300880400c42c64103101e54003000600400003e001c0e01d144d1556418a1282d6914084040c0e03180e40c01d010124000d01c1c6042001d4011181c41005000c0c0489401810074103030384041c161800480c2c440c03002048540c2e49611160040340c00000039603480e007504c10082d003001d805a21146802d031400f504402c030f840c212442c0d0012a0104d04d07080c04a569912480708203801348134900c94014482500204085481246030b11009005d00c04882203040745a0b16041e151108840c603068191004840c0c00c0300d400c090300f401d0420351050064a180d192a42c01041c15030400b64040ca00043c3d03520b4540e8158104a096000494a01c0d000341c00c81030311180301d111f000d1080b8400101030500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 267082724 1250 267081474 267081487
    0x60b01090614220603020a020f0c0306010e09030c19061409193210090309050909010e01050403050901090f03020a0312050f040602030301060e013f2c03040b0d02 71
    0x11038032608042e11200203d1202c0d15840b484020000e400c0b03031614801511802841c0342028000003000c0301c90020007801045942c1c20030020782048200038001c150944400e1050400070350091003509540c101c5600e0410090103141030060076103d010840ca449200700400f4400c2c480c0f004103001a000b02c03801e6503101100c509d45041c54610302054a03294501040a56440600010140350708003095010100d4040d4581aa0301004071100044000c010075a0898100594141072640b2075004060310000035103011241c42160a481e03003294101c00013480041e0046d029a0000c1c80c1c0c201400703601e403118185c01d045501180c0f140301c0b40d0101038000400b40405c1d85401e48140d040381d02c150403102c0d00f5070701c0b01d07595180039540760420b001e40c1000c41c8000003500220351007841c20203042c61180150000941c00e164185400b5003400d14064080d46a042c1500c10760f0000c1d000714458041101426480b83c401050319489024010b16800c6140d00100001c003c409050415151008080b40d4010380d90758 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 267083974 1250 267082724 267082747
    0x61d01031106091c030f020706020c010c0c0e10050a0807030f0206031506040803040e0f04080d0f0b0607080d05160f1d04060b0c010509070602030703080c1303050604060b01090614 79
    0x1180c01030765000d5100d08480041d065204c05260070588240c07140e07400800c6200e401d984034282da001d40001039000441030081584034010b003036a580c0c050414000384c0758942290040118045416010401c82203004004506141d2602c030010702d0010f0217441014259900d1030401510410040d128441c040701007012003c90109120345a01d0040c04039640d150b41d200c50315182c0c2c00138819002c05c0c1c400800064803a40c65000030f02d105940c0983c070546030095000e4204020244080d03500080b607078446240640c1e03201c4c01300501d00c00c2e000380003107500c030481c1e40c60b0b50060310300c018220041c244c081c0c0d0038000d0240c3c0004441c1004c0300c4500f04007281c04103410001911101c680005507106041c5400003070049035400040801c4548140240801c0e038071021282e0361140306c1c0c0f0440c0c006078020002d01c40442d200c0d030701042d0402501c1003c28685680443c08a0000380c180d003058400d0f4001801384001c11042e44641c03042061700f0301f4003a01103403402d08040c01010780281c000c0405000001d4080031b01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 267085224 1250 267083974 267083977
    0xd06020c010509060a060911190908160e09070609170a05160603051008061b0c12120a060b09100c0605040c0617100b07020312041404061d01031106 65
    0x6008500003040b80c0c1c0b0745012404e036100810340d42c2c030b5041c07450160041418401c6d40aa100c0b0785100001780c0e8500410105140703510360f00c0300003440422180007804600c001c0c06011035101c034076052680e4007040e410042103080200c0090f16004440e40441c000300511034001050504a4075801520f01003a07042c500c0c8039042c40d0701440d0090560007410080c0d070051a620012509480755968100726a585a000c5080c1c45012402640340591023100010340c8003c503141140e1180900e06070060400c0e0314141030910341403252250401141c1e000c10485c01c5003085100783e40e40400000b000b402210316054a00d400e51085610303003405000d240314100075040c0124010007840342d0241e4200484d14050509421321203240c000d4000041121417540707d00030362a07041c2030041c0041c2c1c01c004034681c500001110180c0c000c21040307805010740d00e4120303d071503014005000209003912441c02c0e40d01c0344a00700000c844881d0862042e0a9003158110301503c2a5942981500e9001e94620030000d42c100006185 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 267086330 1106 267085224 267085237
    0x40c020c090a0e060f01140d1e03051204050a05010507050c15061207090b1c0308070f0e060403060207020907020129180c030402180c090d0602 63
    0x481c503100381065000044100001580e0001100c0d00d400c0c0712084441e01120b43c5a00300400801c01c8402d04040e504908950b0804451a142c0e600c01d8490720f940d04280c64001030f00f00c6c0c041098015011141c01c0c10054118091a151500d0001d0f40d0b0202032408403015400c100110742110700904c140c50039002540060015000d11680a204801d801802c5c541e1080100042401c404001e2007148050140c4140200c2c0d040500c109000da100e03080d4104603000100354142c4d4020a5000180c1d5070410300a2a2884e15084042c00440e80f2060484000b5030040c800a8000304010040d07008040c83ca10a8902c0b0f2910750312400706034201e918a94072008040300c100c4101e03040710584210041c40850040412801800c80800300450100c11030704c41d8000f080000500003075107848200782d000320008294600701440e000d007034041760340961a0554001c2d540000740004001c0e054040e105d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 266906474 267086330 := by
  have h0 := BRFrame.cov_init 266906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 266906474 ≤ n) (h2 : n < 267086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
