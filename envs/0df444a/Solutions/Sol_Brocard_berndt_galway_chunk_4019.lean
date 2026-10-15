-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4019
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:20:33.618692+00:00
-- url     : https://prove2.me/submissions/433c17a9-1c47-4033-b853-71fe4b60981e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 722661870 ≤ n < 722841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 722663120 1250 722661870 722661883
    0x10f030b090304061e090b0d0b010f021218010e0901080102280c061d100516030219080c0408120d1a010e1210051302040501080d080103020607061b09050102 69
    0x8010360748100f008110495104070a01d420803a04580b9004200021034110b50101481c0d002600840c0d0110780c05000010a52110300708107002d88441080c03a80d0b440080e030715142c141e0a00d02c0c00b48000d2082c2c084010500f10040300c0b00c903052508030b001c02c48000000d900c60000f0381010302640c0d4081203c010814030b4402100351040303034040134003c218414034010300590309060300801c00d9440744488003101c4030780b03034440307011880307090695440200305411040104404c4400ca1a000f0760840c0100c8a54068400c84403492000d9851701c2c40c0f142541021b54030400d02030b141040303845007040001122002884010106010640220780d11503180c0094402c1d0f40684004030420a014032160f00e00703a800a12074100000207a62284c00c0021184030b5500f00002042081a124240010448500e490b00310f02c1703a1140c4212003c0007e80d0301d80411581d0b600e04c0500983c00314100c80014405031401c42c1c0601005445804042500346611070320718240b02c1c0e000104808144010424041d03980c0500c50b2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 722664370 1250 722663120 722663131
    0x1505090705060f07110a122103090b010b18030a030f0905040501140d110d0f14151b280305010b03060f040902060d0908040f14010e19030b010f030b 65
    0xb80c5042c24403502c00801203101d0100001c00003840c00b01c090505844408100005050124503a4490040e500700b1052007504002070b40e810080c002050028280284a980403240d0007090180c0b09a09003600661341d6444060340c02900b40184454250b2641d04024400a552090350358000341c20803010302801c1c201880e04418842e0b42050014050741071910050346203c2000c540626101c1ca01d8241032030140050381c04c81d908048048521000e100e08580a0b43d903803442030107001881c00000ba165903c5850180010307511000303950104141c59408283c060101c080e00340c000e85000c81d400420201e052200748440e007003000d0b280111403038507014452540142651825507155250100006131046d0303410505a00c150f94902e50034055440e504159400c889130403104100c0f50400382444127541d0000e224030031502c0204140840c04003060030100064a0043c0c50b040781c11011841000782c03440a55820002c01d1800304000004100c0c501036507402041010340c01c500309801c604000140e468000e08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 722665620 1250 722664370 722664379
    0x605010e010e1c1b1404060b040b070c0f0609050316080d0f0c0c06020a1b050105030a02030606190327080a0305090f03180a1d04080a03091505090705 66
    0xd480c04598210940a018140c1110788a403c000700c41048944440c4106025004d00441d203003018460b41e0101d1480260f86021989541303070f594550800c025a203075400350700788140e01800b0400c07090031040c3c050b000451143c501c11800548031090958414a00c2d40319000140781b040042003207050601c0f522008019011200c90301c01d0030b0007469961588162203e10801c0485000c280b075281c45074001008156101244602e07807951048000c0d03642a03801c105035040c444240c040c03a1032151552080b002c80300c2c180c441a055648100c0c4580003504000d04294219004004500c9030030451055028102c100ba140000c1401a0754145d8248082409000c04924044412040400e583c0c405442d0303507007010f04d408a02640c1d92201e250800c00741f600f80d501d0900c03001c42c4e5441d195942040c8590158070030355202000690b035105012075410340301400d5000c11640004034000c58884001446401d580e81000b24940c44290355801103e00c0003500284595035880500c401d9050512184004000455 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 722666870 1250 722665620 722665637
    0x3051005040b010b2b020c2b050304110d0309050d03090e090703050c130207170703030f02030c27060d05060906030c0310020d140f0a0623060d02040504021b01060501 73
    0xc50300805c050341a042c0c600c1069481c0f450004280c110f8040340c83c444101030036183c401c1c407211b203242a83c0540d00340b5610a00401d1400240b00e034498020b813841581c200614040d950921814850850b807402415402c0110b015400b24803501c81c016992000340c441e50750712a0b101d107001040e41098502820305030766074106800c2040840c030b0008140d070341020b0451740a4800e0b040100078030300a2041810040c40300f04000c2c100d10403840c001c40540f40d40d5002c0e8030107204000303a5005910481c481201c054102d040203000307042c04901d401800e5154140c0c40d0000315070300d0b07440300d0004940da0012100f5140883d15581000043c0c2800301d20b15802140590091402c240381c84006615140480e6518001d598040380c10051000c4541112110703e0300000c09502030f0401d04502c61400b401103031082a01814685c00082951900c4604840703500701041041d0b5a944030b030301b0054103500940b410b0038119028000801c0b1991544002d21940c030480b04c5601030b04047c42c0d020b600351003490b07100c54140450b10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 722668120 1250 722666870 722666887
    0x30706030b060f0d020712090e060105070c0e0a0920011407080a1b060903171501050f1309020a0201020c1005072a14030301090e0c060a140403051005040b010b 70
    0x41c01500c00207903032182c3c03068945001c00e1450009000d0010081c2001120200d41c0414540200040c8250b96481980c1c0b0826610540152620b118000740100007000d40102004144121451190012032030000070404402c15114801c4080c0c103015143c1c8400b42c0e14404024541e084424040000604d454041c107182054030307a00303214001c1555281c1030200500c0305038411404000c501460961002e02046242c50341d040c000c0140c855000c011004207100404194030302c0d51038100700d910820583d5042d203885410b680019a40d04481e0927500d80400000000c40c208001e4005800e075941c1507400181c8410312190040d00d4030140c030300240c0c800c5103002c05201d42c0d030703074001090810000703011032001005800200c880100741d146a000307000030550400140b03056801200843c12901a0b103001c1c820025501c41c0580c80e00a4402c8459101c031003040178040b0b0340c0c0a10b043c5403001060b00d036010705140d41d0380c4806092107840e0f24880b1042d550b4008010402c4040408a400350403041307520760801c4c003107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 722669370 1250 722668120 722668129
    0x40f032610061404050f1908061512070302040e0a06052a040f03080a0507060c0804141b1c020a06030207120509010225090f0506151215130207030e030706030b 70
    0x44d8090180100a800000789050300c0300351704500c4000003208001e0b5003075500c0c0c0c9a107403507201c1541c00d00030500508503140d00c0d80c41c0280002c001c3d249090b010f01500b51030341e170070000103020820000690303000b0410180c01003001845414416404501040c4943c55000d801b50082150304001c01c100400c240414030150711200c060005482d803020880d80d4800a111013620a0301880c000205a10b090000c0c09030303a03a40c010162805248101c0461014202c000003e584410141071480c0766865030340c0410b805464922543d10b5200c0c48003854565040007034022a00c40d0505410120200e074001aa0300104509565000d12404607072a00500302403200d00005c6d00c404540c2500c00800c21865140600c0342c903034100d004000c020b401c804004000240c10000068081250554403c0d90020080c400100c030601c11a248240c2141d62001c0e00c0d684e0341e032060700392150000b926422055000d81c1c42841140c42c802000800d01907290002840e00e24402c041c40c102e442d4001104160514800341d0003502c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 722670620 1250 722669370 722669377
    0xe040b01170f04050312091e03190513030803011d070212040303030f0f2f0304020d0b040302010902100c050d0e031b0103090503040e060907080609040f0326100614 72
    0x410b00b82119100e50404e80e00d10b004c3e1244050592005c403040c00b00c4650b0014104035042414480400300001180301680c490062001076100c02c2403034919031040034860402402414034065018070810348036220444540c000b6004040e181c1001002c4c08040e554030580581d2001c014801071060741207440f244c0500e03006034840142407548807092a0a029010703000101207001c001340410420344880c84001030304400707407198000529848485090429141c0440b03114070340103040101c504001eaa1400803451000f04154215540c800e4100010703500d1048502280c4c00c1941c50503c800c2280c10301a06090203d03900f40240071070944240000e840115885160940358039a80c081c011030040142c010301050440288203010001e80802c01056100700a400780200350f50319482c1e0754400b01c094a502000b07440403a88810924002000901f01c2c248204007640701e443c00c5c04104c00b58000e2220f0920032024000c1c40c100d80c043c10008003c1942e1040c80040c04107141021290f404010711110910 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 722671870 1250 722670620 722670631
    0xf02130b191b1b060f080f040f02060715021c050402011d030c130e060108120f09040906050f0402040f0903121a03030d06080c010509090609040c090c0e040b0117 71
    0x30010750501c00b80d0318a0b10108507115040168000d03010114540c0c14108540c0c1d0103804081048440840103240c401e4034036901c41d0449460402590705c864a66040c0c030800c581040360310010411116001030030011488100b80700f440405a11400c4064410560598010314044640c0c540020080943c0e4441d06101c05001464000c403084140c1e070003c00d0500344080c49240e000900c8540380c0c1e0b18100c0aa100d40201e04c0303600705035101a40c0b240307025921598100d000040ea200c0134002c0014007410704009140c040301c020000902442c07150342c0e03881540e104481340d04169441038104010344c2858004c1501d10191104100140406550007800701c0c04a04c1031111120390b0784424517603410349580b421000302c90080032a0749803208040302c50080c0409016404060040008800c0c0c1940503000742c42064100404916043e503c030000d1100162000748140c0f00d05185d00710014a1200a104000c2c58528036034960145c8603000c42880150354401500340d0402950707805040100245201142d00f28 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 722673120 1250 722671870 722671877
    0x5040201020d140d0204062c0a06081e010801020d0c0203031911091903030201060807050d1203090618030206010f080a021c060501170f07080c06090a090f02130b19 72
    0x3101d2101d03441c1d14013480300b2042c5024070000c1c01242050300560301688907425581e0303480e8241c40049801000040e21210365800c607114403030a110707260080b040c0540c020207800004825240c40c0f8181c5180c0f0350b0a038040040f59500144250b04d501980c0650301c002d200b940002c51450429288800400f5051203103a0410307580c6080780304c48181084c0403140b40d40e80040124a02081c1c03522a600041458481100075601e0f0200c0000c14140c08500c1d041200c100501d290055680354460511045804000074209071b0f41d1410706000942910030303074a8216809405a91186107880d020380b03881410f03000902d044c007078080100048180040d5000306650b064030003200d03414003001002981411034034020b0081d41010008500a25543c0d0003902c042d0060048030101000c01158646030600e502402e9080d0f004041c0c407d64905180c802040840e1020308483c0406651308844e90403110460f0440e120140c00140651200c03044280400c0075100070002035140015102c1d048012600a40960092 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 722674370 1250 722673120 722673137
    0x1e05010e040f0209030303010f05030d0c03020c010309030e0a0902030a060f14060c120f030f010b091f050d0e0114071407031809050a0605120114191e0b0f010305040201020d 76
    0xc2c0c002501039519610340a01102d449513103542c60035a0440c40c2c0e008160080c070440f01d1103002d9030710035240e14503841c0d0103030090b160b2840b080380110094281d0420603018401e00803015007032615012454401004018001622410501101025240d040e4810704501884540a0100d40103c88103071007044011034400f07681c0d6400f540000c0c00c1500995541d01151404150240081ca40d0340046105402c280c006400c543e0b21011214001d001d034110090300102c0c3c611421040c0c100c2d008901c2e20502190401a0800c06203400010544a4101ca01491070351200305005d0188200c150603074000c45c0781d040c0407000c014180c0681c0018024004003504001d081c0c103c2440403104803003224043c0010035028042890003844c85805400d0921540303014205a02d003001c5140d8043c0725035941d8401d42e03583c0d0001900c0b010460b60801d4601d4250403c050790f80c840e85031106080da02103448000d02501c0214241d0340c41401c110003003000d444268145400d0008110050f0ba010900c2d85030302c0360300d0915205 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 722675620 1250 722674370 722674391
    0x1406100605041e05130f05060657060711060c030601030204051e090a0e0307020103090206090315011503200c0a05060108012708040b030c09100503011e05010e04 71
    0x3c2d9840d4402604088040072504120055070080807028001032001e024a489050030b01c4128071400c00140124030042c1650380643c0c0380c1800814070201031302c140c266140c040c00f080014006ca43c802800030928550206165114203100055110000d130810b8600280d2810070162a950000e020b41d41e101000400980141e0007503060b90b009c1c0201801c031310b0f4001034609101100c0c42844030380074420b28480000880e8140603009440c00c2803081409141020f1865005401403c05000100da1018007030000290640341000181420407802007400400d5241c40c42d00010301d940e10010400305410140e81408800c6d113401c141c0307942107031003000310764410b041c1501504100f5107c0c0000e12b240038100c00041e24003015044100141164016240d03080002140510300041c12900101081000d0008010014010024690018012041074078248014000880c9059080c0ca001301094001c0010300c00550005c03420603d82034a0740d5030b00a0242401d0021300300b9410655040e20440c1c64914a0070b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 722676870 1250 722675620 722675669
    0x1200f030406180b041a090714060d0513031710030f02011b0309060e0f0307052101020703200a03080c0903120d020a02010b06070c0902090f030a140610060504 70
    0x42d1442c403c11040c00204039482c014071100d5082d60140c42c034040416031a6030100d01c0d1782015005452010040686a140914012803164213801c02c42d805103040c890b0008210241c000c1c144103484011120003600014a40901a00742d20041034041d41000010404040720307050160003500e81004484404802030300c0101c4280c840032060901c3c101000400710201038110200500341c81054403a484080303560018005040d0a400002e5030540c0f00b03040400590030b00411382d400501c1c040c006070b11101460760b8020f01b641d00c040400c40c0060000c071400000c2045920307443c400b42c040800a02038041040d00c00400300c0c1f4020f403280c880d0500c0024404800d0390300300320f028540c1e07081e2400b65880303289a240320402900700024840240d424095202040e2030f200c0708481c40254800c94400e022420249944002e4102d40c21a0790000940a4003142c0c40d5410000c0741e03d980c1c030450112a501c0c2c4590110f600300040074140380c160003802a805e105075a00202a03c00f41c03036400c410300281e0402d080000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 722678120 1250 722676870 722676881
    0x30c030f060b04090b01050a080a0503030f090f0718060e01031208151c0b0105090403051905120108030d060b03010f051c0209070c0506011a071415150301200f030406 73
    0x40d9409844d14410b802080b40c000520350498004880c003200d460340d110030aa4607200c0b00000200035800c10400905003001d542419a003081c02d20003100c0da81d442c400c91682c90400309401403c14000982c0312400300c440240500000b62801150403a565495030f41c56a604200315204101030110003400641810418a120754202d003008083c40490101d0002d0070090028414064400120b9407001051a052010000c1e0049a15a42c0c4918041c004ca2501d6048060341104000b080820410221070302003000c040303030203021951b005c0c6d69601c16031080e0204542e03880c0c1c400341b1013080c240010012101e28a00c603404840054a0303408a41c9802c61f505049506101c10081d445a04502840b8005900c407e0b81008036101d0422507210707036251481c03101c510000c3e5035181400c1300c0412031040001e02c2c0c2d602e2011400f040030104d94020341c9050480b600ba01c411601711041101c003298600207460240035000740e0510f80118200101d030700c03c203000d620f445403880e00030801000001003001c000b00c0e070744407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 722679370 1250 722678120 722678141
    0x60a060f0c2607060b37030206130810140a0c05041d090d09051e01050c0d0203090f0d02060924070302030a11061509091906020712020601030c030f06 66
    0x50140c242c50024400801d4006210554915250001e0116681802c0300782403014910019000300300710f1040d810503060401c00483d02c00404003900000016200c1d04080c1c040c0903891107010050600388181c0f649004a0400780350815414600a9901240b0002c0d0007a0020800c140215041301e8a074070517a03403441154030820200504442cbc0701c2c0c07111700d0182181c1c0145092825100248070f403031382c01c88144445004465000e0303408041c0c0e0b2800301710403520303040d07409040c1000b50501d6007d8203c281440390f01882c9401603000000d10407440d2420f50b0b40382440784000c0303601c050300c14182d4022440c280a410103460082f9202c0c903101080090080300c410321241102140ca80c0c032515031500a4880d00008007001c00305e0781c075684050a450022a5051041407207043d00340d5030703039109420003034000700103000c8c9001070080000402e481c0c41d554460440d1180958030140c0d80740e680749003004092000a4000d41190080c02c01440040c1c21515200d0032640c208003120f411009a0815200404546a5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 722680620 1250 722679370 722679413
    0x30c0a0b09150715140f0106050307030b120610090e030405041d070b04050a05040204060c0b061201060303090e010b032206110706140f01052b17030f060a060f0c 71
    0x210070f81000f190800521900b009210280500c560034501140417140c1503030708101048004005200c1548104099540302c1101e1034042001710340100443c1e42490134192404298200b0010060340c0a107211501000340003a0204000e0b081c107410916890b4000c2d070194910403600d035581e0441c42c1081980a2076035014500c2540d0b28143d940d09042059032151080d01c0c02011032401c000380a14082c4241c0d0f088590b5515401e8105c1c8499940915451000708450b034400e410f000e4280d03a409003442000c1c00b952007501c810608030f04200c1007040c1c0700c40503031206406513820130811142e0711400f55400c03001d5240710201c1c20811402d2a10300040c0030840440d40110001194500601050750081c9107140c240058241c01c81c0c8030070700681381d02e290074092182c112001c82c3d0381300802048200c0e440a02402c401fa443c00040050390b58813000072144092154060001c0144013180140fa484181c200b14120340010080d40b520b900038100a00c4d8ad0500701c14480b4460b0140c05001c826007440c1c420802924 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 722681870 1250 722680620 722680627
    0x4062c100305120a08090102040308030109150e0c0a020c03010b011e02070902030c0304030314070e191d190b13020d1401241b0204110403080f0a0e030c0a0b0915 71
    0xd0b4400070784d801000050740042c1081021624000041c421141920f0700002030900e16803e080310703136000d400c2e2101e400c250505d102d40d00182ca44003114600303000b200350398a002e0303644000480013440d00c069007503080c1c440e03490809540a240c0e00100001c0c0540c003024210400007042020503802c1051580c4140301c1c0724000400c01c62040312100081d48100e01c00c2d1001c00c030205040a0314009000308840c82000321707601401008040c40d100c0751f0300b0201240c206a0409080e15003030482c01025418003210403100f10001401800051003208200070328a0801c01c003c2c04050303000244c03031000144c0d00031445070381c00580c2c01000e0100d40c05ca04460f40601d0f2040f441355070b5802020040c80b40e802801400d444072446403205503071240d0b05010040c0c0140e0b44840d00340a19408100003000d40c0440342e00c20000400000001400b0f000142c000244c850410300c0d04c4500c46003002d8144c0d5901d103411440798002181d41462a55040d03840d1050350544450b10352612034010118104200f1100f48807042032010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 722683120 1250 722681870 722681893
    0x6190305041502131703030f070e030c040e03030114060703050a031505100e0427021504120f021306030b07120b210c0103020c1005091e0c04062c100305 67
    0x26070100d0119403040303040b82c40340c05804c41c1646d03c07800107441102c07480d10004041a40c0601c554096030f0410f10040941e28000e03400c1000808071000c01e084100c0079000803004001d01caa201d2002c10584d4002d60b4840c5c0740100c10396001b0171a21a41c040301c42890359400000c40b0b00340c100c4440101904024042118211040c10064a5840c880078a1031103641001c6c01d8040489202c40f529022240450120b08415080c0c3c0c01c22805202c0b004c0b581d00c0001c0240300006002841ca03c0c4000914040c120500c1c2c0c0703403181d0040c0001c462100040e81c0d500c0e810031408000241c1e8030595564001031914103010341c58000c0308040b028042012169a000d071001c40c1034400d10403031518102c07184011004641c4940c1164005400ba03000d0315800c80c0941c3c11040f40c007007500403290880c980c80310b601c00c2a41d078072244428030644400c0110703c105010380d0118447c0c00840c20700d4440c86015152002079480c88803500c0b0100081c407804030041604080d00034020604154180e0020f401460307015050710740f0309415 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 722684370 1250 722683120 722683147
    0x90807181803050c0c0f031b03030d02031f08030a1d0a03051e010e240915011202010f03062909040e0102070318030b07051b0106080105010503010b06190305041502 72
    0x402e10480c00b4045d40741c66151920b01460070001a0401a024000e1802101d1111411079500035002c0e070140400c000030294268148019403080144502d100802c000c0c042912404036119000110160300400405200c036420901d2045006400007034800368042c0f02c004035000d10344560000342180b02e080700031640d40341401c01203c00041c01750000c108000040329000e0340c5401c2c102030b00c01c62124070041c0d4050f001030040b66503444491a021640d2280880501c4060048240d10001d02070010141460456900c03000c0d4851546d140e207000e101403810800103188407075111040c080b403044aa2807008524002c142500c100780b02c024020810001146c190078040c0d4010030044000804103180240f103c064107da0505603038200741260710582c0e9200e000c2d1a141c0c460030020380c010401d01e042003280301b0240607050180c00d50a0002c1000d5142c00141400c0d82c1c490004203104180038403c07248043e0b21812000c00c0d036580c42c900841d03280c882e030a104450001103051084074a00000340701c06543c29 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 722685620 1250 722684370 722684377
    0x6070207061805090414150f16020d081504060503030f07141b0108130506130b070203041202060a0302040e0f100e0c07020415091d010c09080718180305 67
    0x41d00c1d01c1c0400c96002800302e481510038022154071a07980b5001c5004641d41d030317006100c01070380d07041210140d040f19805503032032882c222210001c0000b007400300328403205030f411444035050250004000e181480c40000e070141a005011007914500803051400a0307486405c08802040c001e0140c030741d07079000a0380040d115403107043c081e2119548081923803140503001035031820040000c00c00481521400c801150710b136034003800c25022509c0300000c000129006100d0140100544c4445006005642c5061064580700800c0b110540d00180f02c20046000c044444c681e800c0d038100c8205139a03610114054000b4042c0c2c1c2c00051142061034100480c0240302400359003d0168070300d4604510f603965142880c060012a02100751680c24080c4400608003508103040c0391321024604801c240e265000c4408680c4107004101800c4545d41e00c00b0b0300c101c020b1182c0c0740201c03040c2c41d003ca0f00c07504147c4815500d80080c80794280260403c0d00c01c16100f080f03503001c0c3c0110b00d500e40b49039130030408909004040e0342 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 722686870 1250 722685620 722685629
    0x150d020403020a08070e180a15020909010602010515041d39060412150c030207111801062318090a06050f04020c0f030408010603120804051c020109020306070207 71
    0x611084001c1544c4200051030740c102c8030042c924021641d40d1880d0030400d028901c2040c1c0b0f0f01d1207590001c200050341500c0e260304c800f900d5040162551036203010000c400d513040e40300c04256454402802000350180b4400304050201756004907181c207020300e400403180d200350070a448038002c190329440641c01900e0781502c03010603529162400742c10f2612041fa4210710400050307100c0d0341044104840c80040303105035003840c0941601024188002c0302c5800303440c008240328001030390003d0490204401600e40c5d4030b4040080c1c03441400d802c020607404200c0070060007404180700c001c5c04140c40c8648040b0b00d070000904900082d603224107c0d1242954070407902c03200c0724403982e0098005404595a84120001c4440045c442c0c10340b0b59518060100035030014000c80d0303272400342081c22401c15904200420003013103800000120b15286051140d43c1041c0303e6000740c200407604e01480085103001802c1240c81d454031403281846203a00c0002e030700501d02e266009402d80500c20030042071940100c1c0510841c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 722688120 1250 722686870 722686879
    0x601093b120c06060d06090501151a12220c030c090c0203030603100203100e04050a021f050315060d09030806040b01111b12070b040503160e0411150d02040302 70
    0x11009000181e15000d800614141c80d403204001410300c5c9400d4441c0c2e00004d00a10300005c3e1142c0c261101401c0d1510b003004c01e00480d030402410440c8800000e00981100c0786111a9400c240800e015502000c1d005040c1540f45421100108400140700b07800c20400b6510044007015a0358920b00810308191034458041054940810300606034004411039201d90b100401a10b00301d01c1c8000000025000a07040c00c0c00a0b0545102042d00d401c180d0515020310b00520017000c80c10080e104000103005207201c1d5001c20150b0b85004202c0e9900300c0140c0350440d801080404088100c00041411340c05001c44003c0841e042c004c04409154114208500600f015982030082e01f800c4001514107080175050800350b58807030710802619840001038680a05c0c801007040c10158218140d4500d03042071500111803840002808100c0b52804014103103000000020f040100d514000450702020001840908506110041c46009584815450041d41c000400882c1c84260f0341f80300d10002c2d0403501049005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 722689370 1250 722688120 722688133
    0x30606042c0a06060c0f03090803040b130602010b0a03120c0206120414060108100506040612050d0e0d08090d061d0c0f04051b1e030f06011206080601093b 68
    0x2824041c3c001c4005540c1d80e038850580f011002d80c0c5800d092400001c05400b0413113036404c0070075900d01c1032000f04002c0c52070f040040d8980f0301501c00421042480d41c00142507a00d0040d0303d090b40d40f2072440c260102c030303082614011443d02e00380c016100008503480080d8400800122a80c910b000240068000c4e070041200109810704200c0081c0e5a160070b000b42401a802941481da00c0409a042107901500c003800c046032132503540c0f1140b11303001c44e10381d170464044c1c010311540690301754000030f01d0104100c02c0b507400602c0b09135038840d6141d92062183d403030300420062180d1001d002440c0c000c02100d401c0340c8060300101245001d4180c950041e54002449460b050021404500d483e000305400b804008036081200c424100c201d20b40c5500c2601104001c031030f01c049403141c6400a41c0914418141c000d20741c0010310707003c0300044c9001c50031000c0c01e4002c1c2c90a8414000c82000007072450565003040c800041c5006104071791201d5984650740c21000307889494004669100b50341800841d0f20480040320170 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 722690620 1250 722689370 722689381
    0xa1806080a230a02070302010e0f070303081005010f111603060b0a05120316050a20040f020c0d14120c07121e05131706010807080120030606042c 64
    0x203500c80c030b1002e00b5805854501107a05402e4603401400c686100b4000003507900444001982060641c401141c1181c0000310100700b4580c01030f00480d4854124910440841d04000003c0c15914040300c05400300301c810a10b48010041c10031808103c10810700400d040c00d42d591500c1805010125649401452111000100e034100f5442145031021a40d01035400e0243e0303858200c91b54042c0100c15189440f44805405c04120806072041c01c485c080b01c44144561b4011003480190f07012603900e00280c0b0320401521441400c0411038019240940c1b400b024880700000780c000f552b00032540c0301d49144e0003000510481046000c0102011480f0b03100f00380b0f031944408000c0d210710792a00303007a845901581098858641c400e500a2a80001c0000449003541d111202503c1481c8070587ca4251a8044030040c0705140c4200100f200601781d080090080010b0b920f8803030f5919108401c00c00c5003c8004c004a1103c0ea0384405407400790011441055a4103405070841405208640c4100b1000034020003168 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 722691870 1250 722690620 722690651
    0x121305031c1407020d1202071a07060b01050309030307032c0109051603021f1b0609030801240309020d0b0405060121080405060306030c030105130201030f0c020c060a1806080a 77
    0x10001500285065a04451034a036008241e403030b40806e004500522002007851041c0c0b44403d403006540042540c1c8907001d92800f1000c031085030a807541409400d1041044c4a080001180c2d4490b199107404581440d03031040c001210007500c400c0781c41080d040e150421403c01e0540c0320b0030b8418012011184d00c4000d9404c402500101404041d402030309080c0c04508501c0010101d00380c1101c6403412000500004000034500c041c1401d00710303020b54039202c10b1010b0650003817000d400341c01c3d0101e0a00403130717010110000310055025500024582c652032403009564800504084d400e400010b03090721403826180440e203c413824010281e8101e540401004004c0c403d07550140d0207175008280c549018105810403611783c000514165051003800049240d50300d0a0140d40d01425a1100c19004502e840c4000750a95810203070350319a0303c0c5071041481ca075946c001095050600c040d034407203075600022001140c0c14104402414122415150700090030f586c4400c1d40d41c4038900248080040c0304070351304941c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 722693120 1250 722691870 722691877
    0x1062301090339030f0210020703021804150b010503070e0609030102042d060905060313241103090703020d0f0b1504060506120a0e030c1504020907080405121305031c14 74
    0x43c0c805d5054002200050604601c80c0707170401c030740d230040745e1040e0303680d40c005030302c202a032140c004603159080b090100300281007054540b0760301014000c1c00070410240008040b40001011076080042084024996442c0c40045031074074800600255501c0f600c0707200c42c4c0066480409500c50a03c01c1c0065949140307040303202601030311103603690441c0851074802080300c40d80014107201103c1c82c4d010150000103031140c520403010302d44546070050424464141d4008c0b2041002070340e040321001c00400218140c04545101520341c11130781c0384001304050902540c14104220010301c4030180350140003140d60340c81c280d0352a07440304890505c0260703190400e2040034002c03400481c40c40d00c40c22021a0440486400484170a0722a0044a04280c2ca03204d045151a0744841c1002240a60b001030000750f0070301030302440e0310212604050000b402d203603441c160b0b1801c0071848040440000b2910b5040c2450394101c1c1c00050200800304c4022409803c0c400c0801c46104000d0404602041d005500c22404401074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 722694370 1250 722693120 722693123
    0x20604050a060b120a03030b030c06070f020405071b20040204030809101b0803044b06050f0708090601050d15110307080a05090106230109033903 64
    0x24007000070690b5a0300c40508080300032550700c01c51549010a400070b00300320168000c0c1c0280e40106820f1800c070149414000501c03422401000100064808503640312080140c50358103540001d0169aa07100c2207a00c824002c24070f0034490074104005c42807222040e00d0812078829013800304864209401044100d128520000306543d05c10b101440841c5010242c420206a01d418101e000c41060303900c0846900526004403003c410101c240003e0280001604040e0120f080c2510b070101c0140d106000b00d5100c400c20101d0744801d080030003030f210240d81009010941e10250601860411140a6410b08001c4403501c00198019001440c1d110001815504858000e0603c00f40f100c82da80701c030b00703202c50003e01c220416610751220b28410103074a03000310312840c1969202031613070034a039694009884014203103c0b0540c0c1040020301484010080c4524481c0741c8501d5142c1a10b00180142c0300300341e20b9172000d003500c1390701c01e40307000312110203045d5040c1701003444245522211320304005400da6819000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 722695620 1250 722694370 722694373
    0x20d0804060c090306020d1a060c060c071505010e0a14040c260f0307030f090e06010e030c0909010c020d0320030702031207020c18060d02090a0603050a060203060f0102060405 77
    0x814042003466028844041d59840e081010f42e031252902002d07a03010b40114828103903075104168000561018140c2c4440301100e16a1920007003001b06a6500b001901740f6504101c0020300c1e40400203034080a005e12159070310b05001d2582d4503401004e11103800c44006441c1414250aa510818440881c0348150703404040ca59440e818603c4403181c51008081507600c41044c0329140403004e00030880b542014464030029a900c29151900910303650a5145903002d0100300b41050188101303410b405940a0000e2800c01080c07101600041c2c0340c105020403498010300144180101c010040d000307d050500d5a03021185ea1b550911022400c4506c50000d942e040c0c1411115000031080e000011a000300d42881280d08000301c840741d07603441c01010364500002d40e025001202090509030380b8109882100b200074409445c0c91000315100c0c1141c402c0091140007a0400207074055a183d001401840d040310450b84804050f244c104000d52040d60402e10503070304604503070074644c030001e01d592003558001c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 722696870 1250 722695620 722695637
    0x3111c050601210b0711030705010f05100f0e060d0609150f150e0c0307030b10111507020a0f060f0c05070213020301031a0402010c08070302240702190507051519020d 73
    0x1801c986d0320100d0340e41d04859000030401240030650034080c8120601000e040000d05041c0901c440310f03003605540c45500f200080000400404007a07804c01688140151490501a032040c54250000c1c140004000c0c071000c003070078000d5004080ba07032100800c14034508042000c3c0510315082140000383d4030408451103c20000200b55015903409150004c40d503081c0402c2503c1c1c00000981444110407080e000100c1ca00610000790000b0004503d1000b01c000f0300b1034444c100540d00944402205901501040403002400e04200079a4030080a1001000c010440300110baa0010156440008264462420841416100c01182c82241d048030381c81100c640300d080c024803800d100030b80010002d86c14030010b4040d01d404503000c00d0040c0340702480b80d030180101000032030000c0b40606c1d041d02c082400d0190300040041f85500040e03402d00c00d455046026101c902c080c5131032490014990001904503640a0492407134804100c058003964185c1e00e00460004201b80c0107c0c0e03540180c8008400080a44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 722698120 1250 722696870 722696881
    0x1201170d1d0f040b0303190f0c0f0308100e1501030e060f0711150c0702030f0601150311040f091413080306092703030615030405030403111c050601210b 67
    0x41e940e640c42c2d550054000b0032054082c4001a0458000401c0300c400c0f150001c450b02c1c400d0f5401080c408078000715040407003440207640c6914414500c0e5500c01014082d41c080441d9403919101e042c200103181041d01049180350a000311007980f01c2401c9450f000c41e051160640440c40c001c181e45100b40b130720940e40e0003290f84002e0100d0b900e49803030003042c00038051000603041c440034444100e40302c1d6207046100f642d20101c03417061502c0c204450704160f815402400041c08080c00c0300d981c02c88145054079021811142c05070300310b9281c1c4555031041d50102c0c4004400143c0807050340111507038001460004010b03030b6503542e190607900b07955003005212074420800580c5620b07159035080d801c02c4080ca61040041e07003100404111840c900080340407640302008102da0b0b441c0400c078035070300c04122003011420350400c2e6468503541d028500008180c1e9810700741000e0a62140e0015090300007000d405190101003a05185072034640a01501c00c000040007801128400028910300640342d0042d42914650f885 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 722699370 1250 722698120 722698129
    0x90402070314042304050910020d1515080c04061b0c0504181b0605030a0c11060a020705011a100c06060f091401170d0c05031201170d1d 60
    0x4803022800d101c007544840c1048500030014101512601c101c140d140440304a0202014070010702c0d8612490034507042011410300411040300e00700000c40050385480c10022002c3c0075090f0440300d100d64840842c9e0000d401c40c107020380a40c40914644480d410380e202c64641081500c11f40c060341d00414070700000c42544001d0414182c021a005140c01a100b0380c0754000603043c0c8250340520100403120381006014045040c00034201003003a006400c000ca4904017014141d03000041ca45d901c07040c0c1e40d5000c1c982d01400b440d83d440f0408000c0060f0303903052034805038a40080d0001d90056900b58a0700803e00303516100140401c16020300281803080d602203200040b240b501c04454221659520350000150300384c40901e04502600e0460f00100b0024000d19945072101b005070b2024501440744155140311407030120b49181034414510702129205100c0c02c1152a5208603004050300d21410360001a0b940e079040603444802042405030381d11040741900c2166050769080040c011721904280c11006441e2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 722700620 1250 722699370 722699377
    0x2109031b05152d0706110c0703140f150f0106033b0f0a0b0610052203050a060c1701081f060f060302091008010e012c011418040503090402 61
    0x1500e07612401000c41003040c07441c1000d20508120307039100c800314131601040024003503e0718070031440003007504000d0a004025543c00d000d02c000380140b01c429400300c0b0852014080c00300c500403100200e03408849071038031043c01c0742800c6645105c60000003001003407a80c400d00680e401d25003103c800700c241016114026808007035440390310544181c801d46240354804140b20018409a11001506058400d8140480300407001041c840c420310080e0311400720607030054192000811000300040c081c03081c5804440366000d240e00082d20038032403410800b0400545030498010601300b507072048005c02808080e504810428000d0b0170340c940000391041002041000400508000d4a80c0031410a54030070303074105c8551081d000640013035000074004240b803c0c80c039010700f04403945142c050300c10361410050b8103001906000d000036481c0c81c1584510703106910059a1040c013400601c1d80d03455659502c85204c245206041c250080403140b14210b854915420200d11031504400998500409002004002c6d030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 722701870 1250 722700620 722700637
    0x10e0403051b1f06060203031626010e04061404020d03081005120607020106050303030106020d0c230c04060b160b0c04031a01180c0c0b042109031b0515 67
    0x8500030700c01c0b041504100a43c003410705000070120041c0003210044801c1d20040d4005000390340c07080060001c00b00100c10080102003903454404801005400c80c6842c1900d8404908554205500003266003464490720501440c42800c01b08981e015000c0d0740540072104907800707076028503c01c40b5000828058600c5550266070441c104143c55201c50000b8200c2c0c0741100c44182c00c0d0300034002c003e9816024490000034000840045080d98581b5000955500840c400e40041003660001312040200001c0c2034a00400144200880060201c2d1260740e07800d5502010303840360341031140000c3c8000d803810482d8400500010443c242c0341103500e42d002c80326006400c0b90080d290401c03000010540e00540d0314070203910706960700107135454070441c402200c402c40c0c0c00c490007901d8003000d50b484ca500500200400791740180b1414541e682c07400c0000444020402010481054442001c4640c0c1d101c580c403000ea034444d60882c1e840d0592590310101c0700c2a10300665803c503602990020130508214040c1c42040c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 722703120 1250 722701870 722701897
    0xe091902090307120204060608090d050705010204091b080c041a0c07051210060b0406270504020a020703050709050408120a0906020a0c020f120c1003020903010c0203070317010e040305 81
    0x4035100100e40b030f0450302d0307000d21032005240307244108518203409107400400c43ca01d08101282400c0520302c1e11003c40260807414001c0c00201102000401e405640051410080c00c1020a0741c4440314030180d204110b500c40080d8101000230300030401c0009843c1502c1007900855140740c01c41201c9051a441a007103101c180c46061000601c130b550b1680c0290f0b202c8008405060881e46078a401e10544d001034000c0742c06400180820b0151940c082c000417015001e250307440b0344000c035407140b9280500098005039000740c0005484182e0390340014280c8101d03442001140c040f1540d0741c503940100c1d0b00940f0024440e4404104004000400b0041203802401c10100015060040d0f0f80d00402c0ba4014140f010220f00140c1060302985440030754144140c2d400c1e280a44512001d205c196281d00c12600518860101280a4070007a4403a5041d921181806402080a00741000c800b964980002c8011000240003070321507500300300f5141c0d0041c101c4a10b0b2504080a03120341e9020713219608441591a0038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 722704370 1250 722703120 722703127
    0x1203060f0618051e150405090606160b1f05040213031103120d14070c11010807050c03040902030a0b06130e06120a26041a0c1203010e10060e091902 65
    0x103a40e0700140e03581d5501883c10414a0203102d1081c842d506103c40306803c808801400304100644403010510389c0180100c404641d140c580d1446148018620702c0060503203010304040007221480042100b0f5980051181e50890700e50b51810803040c0d2040c8040340317588241409040000170300e040505000020001d0943d05003000751207034a11241c110360b40032105070b501c0d101744481c441031000300aa000342140c601031a20f41c81030f803076280311640f01d095050304101e0310100059020b40b050707055500b036003054000d60b0f603101c1d41c0b803901c100a50020749500105520344070441c110f610381318040345d80d000f00c9554602c0e4800d10b060103001b40d040c40204165003000b0030061580711860203210380344206115075006d0180c1201c0b41c032000000703002c034480b1a070318040800c0f040c44460001038002c42e10311011000a540e815070000707400d017043e551040c4500c0002c000700c000300d4034907260703c00d032489001c403040301e200010b54030001140c0030b10f10700030702c55080401c04001c03442a2000c1201140341c9141044054035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 722705620 1250 722704370 722704379
    0x22080a03032f0d0c09180b01030c03270618061517060711160b18010905030c12010216030206010e0705070c0506090f19030b06060310050607030201061e031203060f0618 74
    0x1d0301b40c1d00340c452040007540c0e42c0e80301d101507800d481f410309800c410786410444490540032404004111060001c1418100c8102d403041104d15007008a070b000d031034004920181c296192400107442001d4102400428064000c1424200c41159240948508000b03000b40c0e01e9950080c7d956800b86074000515000342d0542804542503040980014402062043e9175844110041c0051003c0140440d0422082c024100f00a54000400c0b0307121100448508810702d41c900302240c020710030b02c50b940390f6082c1b803000040107064012400c207040300c041d4211540701d5a9000001c441134070614500030102c0406920078819414050301800c05402e028110b10b542d44084000a007001b05180510074602217600d005004100c0711500c03043c3c1208098800c03d00314100754010f580c0c420032602545005000220f200002c0c14401d4001000402e04408840003016845002c04620701560205440145807080f2066080e0b00c2072080208a5040a00b83c01441c2d04015084804d80e0902031100e1385201d20352004107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 722706870 1250 722705620 722705639
    0x1c090302151207030608120d090f0807020a080303040b0a1a0d21030902150717040f052706011407050115030318080322080a03032f0d0c09 61
    0x6800301151070055848030b00d540204005007000030094010903050000030000a600002c0300055418402c00607500c80203005069001030000403c041c280c810710900d620207000194008142d014000d0b00c55181490702d60380c0103543c901c41510000c0c2075005034400544164095404540034850026010315004003800002e01c0310b500e9102c0585400500c07545220141f1154000441261594202480741e070b1082d400060b046000c000b541200c43c0000982c1104020484548443c40c0c07008031017a58540c0e131590401d04001002d40111401900003100e400e503c52900300305840a203500303e04055499481c80011120a031807522100c0c0c490005002020025500303000d000c0b035a08480c00018032052031414020320f82000c1480510640101040030b01c443c50001c01102c1e0f07185a0305009440f9202141464402101141d000b015940102c0c4000000c050745600304682e08910554410f00c4400c0000b58400d44640e40054400340820411811301904031580014150000604000c11440c2e80e4404a6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 722708120 1250 722706870 722706889
    0xa090c0b070b0a0504062405030105010f060c08030603160308030702010b090105030606041109280914011e090c08060108090c0307090b0310151d070e0f12071403010e0a051c090302 79
    0x7c0072004500d141c24040303030600f482418018000c01c20000115071415501030720006a10a0203440c42200200113001e5440401c4480382840c4208010340c2142d42c0c904150303006400940f640801035080c2054000e5a02c1d000003c80d0688a0050250129407a2403003080300034409040480c01c02074051000c0e01095640035805404e100020303541e1414040c03d82c0c1922411050364020010251038442c219800003040070085054881954a42c103200890851070f01c207107061540003042e068141041756101552000400d07001c1c020a03200d04c0f4480e00d8041c1000e40346c0038502c009641640c0301410800c1041480e40006504003005025201018807550a100c107503064507040c1c02014600304010491205445062400480c84030303604000f0f418201001003100b400300146038807030421a0240803599440e80a501c0b280550b050844910640d245510f055541c40c441165219510b06038003286d9040f000b28104075000d6003c40a801000800d40b8404200040e40b1510400c0100c0f80c0380100050b1544a0f21 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 722709370 1250 722708120 722708171
    0xb19120e0706080108031602010f0e0303030106030204140a061e091e1a160b06011116080f060903070204020705030d05090c04060510020a030302030a11030a090c0b070b0a050406 78
    0x905800740c244000503101c0801a444203030b566108000704100c3c080c4c004400340105034240b0380340d48500042c1e50115208003003807940a91501001000043c4c43d07825a00030411a0700c0c09a20301c100b190300100304201920184181e20100d585c014801d210300a041011004005c03850424643c502c0d120b544124025140d005042c10b007403051241840744010b90310034201c1480550881524205001c9814560b40d032880c1c40080c844001400070801980c000c1858080c607894001c12900c58600c07200118004034a94410f815103401001ca0b0b1001c00381d00481c04511491403900103602e4004c45900303120007507018080c180d44074081400500b0b41d50f051409064010a0030340d008100180075001000115016980098400c9441280a0700e9554000c074038485541d425050060b2284c1c0e54200c56005803142852040010100204010400ba81c8d503000d201003d001e10003217a032550301e4144e85036441c1304101c1c1c06455070403000005000d0070700703940045030b1151280102046a81c1064048540850310001c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 722710620 1250 722709370 722709373
    0x60d0b010b0903030d1b0314130201050a0c02120d0906031104120606080d020706090e010806072d0504030c0602120d02160c090209090702010612031b050303100f060201060b19120e 79
    0x1280203625000c1c6800c01c6800340000230701400d018a5441d071000704468000d0600c5404103414100d280078141c0c903400c007030700a801503a61002081140e41c88103c00b018140202c0c0c803058010030742620078487e000c50070b807100588a103018200400460b80c0300c0861811924035441d00c8001c03031100828400346484446c02c0e001803800a00340380b4041c1c20901d0980000c450620742c4001003000690028841e5080307102e905000c041241d1452010703000f6500c070201048284c0c02074640151b110f5102004008585c084e10550f8041e0780c9501003240c075549401c0c40004014800e1202c0b20314440598024000d05403050b0407082c51914690f26101441442d6228800c41540811103442d0390504c645407a5200c11144020403d5500342440c030144c2280e4203001a04121441c0515808400025130015036550030070201d940703c1c80c0c403100290b1a00ca541c0950820701002040020b4050f005000d034400352040b070710485003482841d10b402c1d08030a100450031020050460340c02181c00030144500100d5044910 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 722711870 1250 722710620 722710661
    0xf0c030307080108011404030302030a09020a06050c010506060403030f3e0c030a120c0501020405090a1d0a0b010608281d160e0711060f0a05060d0b010b0903030d 71
    0x91002d440904140d00140741641031512040224082e11145a840f0f54503040c01603c2c0e403985010000240703c031000080d000034400078080350720740d04280a4074003c26040001d100035941d10040c44041d01852000501280e0060010003106006a8441c610301141100c0080a80e152590071081815211081e040c190364000160154200030300034244075807000e50041c03c03105c20f00d6032500da800504072140f10810a10703800e02810840290112401001c00810340f600500385030b48081c0080071580d407c200b81b0a02c03036100d001c01450110f00281e0b16038000303042005a13841c001c020b845100d030040030b41320b400e40c42549c02219000300c51001c00c1540d04c0c02000180840801d160b01194006a07920004a0f500503a00d5210010542e00d141c81910002005d0b10b05070340b81c6110554940c2200e241040741805030004014601c03c0d0120307468410001d0b094140880c0d15036100307204102c04140300240c01900742500510201c0101c0005203000c8202904491818181616980444000d0707424951000c2114 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 722713120 1250 722711870 722711881
    0xc0607091503020c070e060411030a36120c06050403020a061a060f161a06031b0306060907090513050a0506040203221505011811090a05150f0c0303 65
    0x7001000c29407850341000c524020040154655a840910680d04c4c00c085800000d034503900d854000b4040c50aa50700301a4032400c3c0411420301170f00f102d03080ca101d07042120500b03000e84403050850070f8403051b8540682451031855156004444002e070400310902001d44c01c030300c0004586105103071040303010340c2c00ba0000304501d140c60b20998411b101e101070b11160300d82854000d80c2d603c004680086501241c4d0503a20400c05070f21840c400c96940010348200c042c4c6080302551600c2d401c455110760012000c1e20385840302ea800e207110a0071855015a0194056000500300d41008500207400c00780c8c42c10110b0145a8a400040b28040f5504207500c055441d070b41031100035031080c0500d17500800f08842c25415072400c070354580658684d94030f59140e90111b000c180400c0c4500131120700d040804040c0203011543c0c58410f4443e5500190641008a42c0782c070031540a01580c900c10b40d807824070000c050040381071400c8200a415a83c441d800301207690200500768400c41e80740002d005260407040919120f182c81c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 722714370 1250 722713120 722713139
    0x150909020906090907051309080a02070602010c0c08032e060201090c1a0f07061503061e0b0a260607020606091806042012280f170c060709 61
    0x41d142c1801541d108081c00614600030800c4030a848051310310180c00c001004084018000c0980040c02c500f10000e4600c00c1d503036000c01c1081c103962460700203101884074184100d480348000e0b0b80c042e108c000c091010441e03502900c0142c3d42625400c12040c1400740d001c07849a1416200d80e40b02c1c0740545c1d03552040400300141c40440f03d004000d0b014400c9101c907400d10004929214800c240d00900c00005240020804641e12403400e550b4800c03110301507542c0782d1500740c00801c44015040c520085020f81007008200c180140d8407140d4000d00001905443d0005c80702c054041e0040c1400c2c00f28402000307203803425040010301d10502903030f0300034036407810208280311700d00f04041d1280d5221998110001c00405002030003540091b072040d2007080781100040020058194413480980c441c540c00300e400c001a80001d0890460080c2c1400030b1051404081d401405d0803488000502c0d400c0041030325400b1070b50840c0300c281c69400c0b00804070710f0000d0703031401281080d000b103070000c010034100f54051010404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 722715620 1250 722714370 722714389
    0xc1b010e0306010315180b0c040f090c0906050a020f0a0c09050105010807020309061315030f0515011409151606060b07051b12010c051903090b130615090902 69
    0x1000e80103010554115110308034401d18100c80c105c82075458a41161804020106e83c40100f9008030042c0c07031500f00365002e02e5141d401b510078a88403501c0d2141c0440c0c1346425100b03001004d40d80b41c0350350380001d01d40203080e515a0480c3c0301031820b50050380429281d001091002241031031003008008507040c104000c40040741c00c1a00403904024195082100880e00082102c0740000210f0704251914002c1802c40010348450b08003107401080c0d6007482c6030858046c0c010380241041410244440d50310b01641c4868044652120360024000e940910004c608034001440d081801604007150000c18231300e03160b00d542c814668441905111039104040c49050300ca00c03400350a10100561500c0b00340c0e180c0503907415904c8000902480920324a07484c42d03444034a881528010140203101240901d440a410354001c1d03100044829001da4005140034400c0c410800c00035481748042450340c40d0041c0070707203161110300411141a035480e1074070303c0f440400d42844001800d01c00c10100c1c0f01a021301c18480c0000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 722716870 1250 722715620 722715647
    0x1b06160c020901030303090807060f090501051f030f05070b0307020304150914040b0f1c051501050102031c020f070b07020d030b13091506171501080c09040303020c1b01 74
    0x55001950040e42e40707458080c11280c25141c041116110750500d5807241c4601000184154900340c035a1050b01e1040d00f200c641d03180075000030095552030665400c80c5500e5180000280e02071720b4014000078100041008055014004803900d40c2e80301e580102880d401500c966015074008101080120101403000c00d51105c9443d08115044c6441c0b06049e100c0c90003084140302d952603808030500c50b10344082c0d074840c1744402002000c1c83c2000700e8441c10751600c034030810f0b0f800b4022200100841d9118440643c101c0e10181d0056147c41001076400c3d108003507242c140c00c80d454007000740c4103404108401030404070740620b1800c0c9850502030740c013074a06840c0028050074142401c0c0600025590a2880041c4c062800d2011030001e00074540389086c18480b840806a50713160440c0818a1442e10700c0130a400405401100c08030302c1084e40c550081e000c240304a58155001040400b03640c1850f0782d040350080c0c420708001d03080603000c507080c9080c95012850281115034510700c0a1040d0703801402d505100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 722718120 1250 722716870 722716877
    0x30b15100905030715031806050105130e0c190b030702010c1b050c010f030b0a09050a0c1103030406090c05090a05060109050a21110a06020601141e0906061b0616 71
    0x41d032900780440e44410107440703800071280200180e84c1056010b074008150002050140100f0403000d498aa401420b0a0298600a100c03000502c800440c2d1481074050b0b810008000303149100100d4100810060120105030588030501800501c004141c0051030045d0042d030004280c200b00310b000103103641c495521229030860454920008038402140185c00b002c020b20f0400c01000c0c42d4030055002e0704045850942142084500160b48000c40d4440c0e8010951b40f0814400c0d1107a0702000c03903d684175050801c00c240c0040002c00c001482903884024040d10462200601c075030f85400003820030030b0407903000d0016600c80e81003040c1781d130340015a100600001c60300314046070700700f014230301200389620030307410a00880703600c80d500f405000c690500003810300414101c078076511400000d48404081c403920309041d40c1c42804251926000c10440e8a01100040525003440141c0401c0040280a00a1900414100210f0a440c0418808600b100c80c406c4010002400c203401c50307800d4800c0c1282c0d02c0040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 722719370 1250 722718120 722718137
    0x4060f09110d0303021603020a020414041a3408010e0c040317070f0c06141206010c020f040f0b13060b1b03120103060b01080934030b1510 61
    0x20310140150300040006580d0002e030740503503150030b400031303c502409485000c0740740d4002c1d030406030300080d03171903499100750303402d00246200c02450500c0c01401d60700105102004070480341e604120403c030542c0400010b50309a10b08030315001000f10301072a6042c000030354a01c84000b410142d04183c006006080043d44044289030181081500d400385020042034198150707051102d00f030200060300d0041d500302500415880d29840d00341c480005910501000c0741840080040c1d1010950694540710051240c02001d0390300c1c4401103500383d1840204a902c010300380503802d41502d942c03058510090582000042d001300070010403540c04a4085408074680c1410304c28016032460005039040c00f464000001e0000300c0b001007003402e6001d0500c43c402d040c1008000081404000d412107019131400780c8801006456400e0344548460681009900c44c18400015141003541d002c2219040000b403804082c11319100d6641e04400c92065032003051403001e0b07050310f445d20314000c2000740385001c2600740b240702c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 722720620 1250 722719370 722719373
    0x5060a180b040806130b3601200c072114030d0b1903061817040f120c03150e01230c03160f110607081515030c030c09090f04060f09 58
    0x20591070090048482c0c010f80b02d0381820100d1481e04840347e180c2e05008040241550841d40c030b008290103254401201040750952000c0440711044a030500c0c204005805401c0c10112030300b09020341100041011703441e00c4482c4010035501840c2541c400b401c8006142c0e40c130080c09001c015584c003071901038813880381c40d040c81c10800840e000c0c000842e9409000400c074002c0700d2104151040700780704042c010680c5880000c0120550358000d202f5240103280740d00d40552100b40510050300001c20007000e01c004038074113001017030030b803151100151854034000c54003099200c80c6509581080d0b07200d0101d411461105c84106494001296003c500c1080850a614001080040c1c24140c080071a0a021701440c1e003151081c415102034005000c15001c580d0f503030038035400080c4404411a000701303081500e8049405c15140c00c0103510f01c3c42e0f40c1c83c1000c3d400d540b030352410612186d0024211802d4260200308008054860400091050f881c0c4140280c5a20385130a050050320b4050529407070041c6048410700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 722721870 1250 722720620 722720633
    0x3060103270f030f03180b090703050607050316080c0307110309030f0102030108010614060a030905011407020d12290a1203210506011e090e19150b0405060a180b04080613 75
    0x1718056004102e007c00c03070b111440441c1c18145650000f615900800e0100410314ad001002580906802c0d10041d9191840b4001150390750400c0c2c5540150344010008602c5181c0b1905520120341c00301002c1c1d82c0b80c215075000107480c0c51805030108079540d4002c801042190340a103ea0001014683c03c01c1c2d41420901d40001d4851141058032024582e641d60b4007010700070251b2090b140050403a810710760b141008039004e9a50b04020761140c0c0041e94103008a601c641450007551100101e00d2031058400880300208500f059420001a070000111100015195421030101e16220b000f40c8400c200d02052004070203101c4e10fa00700c4081442d0134001481601d1340e200c02e0080380440c02c0180550b6100015800b103452035120f40c40b1406824144c02407100c010002440c80d003801c1c1040804100e0341901c0c0c108204002c94034844c001403004144000c2000d420442c000344460040e80c641424500403100308090444000d800020f42c040000c2030500c190481044001d030041c4c100f1603114a8005182d541c3d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 722723120 1250 722721870 722721911
    0x50303030c0a0c240501090e1209010e01110703140f0a050c010302070807051b1305010518040c0306060e012d050411040503060a020a08130803060103270f030f03 71
    0x601000000003003c02801214010001c180c00a80da03038024001c1400c0282015000031b0141500b400e00e0407131328141c03c0c640007401128000c442c000c481e0510440a00644401503440c15480c1880761100f400786403948240300c480c0142d40728240d1001c0c0c03040c0c50155a071034405c00b9030072106598040401c03000071400008010f503000e00240b8015a48a6491501c1c0306680640f00000f0107510490555403400703880340b902d44030700c00320075a16691611211120702c0e054500c01c1c0305541d001401c51400d6010f43c2030055040758040d000c0c50b08009401d030361b643d440007201d035030f50f004100851207900103003c1c211070140c264210000211400c80c40004600d9109110385c0c2c18486d483c425542c5900800211200030305541c01818000c0075510a844c055406002a40c0012202e20005504000040040104000350054260041c13070300d07030039a074441d0019001885038400e0551496082c0d00707908800c9500e10380c00403081e0310401520138008510b26011781402e65141190301030508001050306113400d0352519 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 722724370 1250 722723120 722723137
    0x1e09060512100c090b0a0e040f110d09292d06040f0f060603020d0b121504020d0b070e090108010b1309080708070305120a06060815040605030f0a0c050303030c 70
    0x1404002400c4140e61203081e85d801108890404110070301e5540d003100ca40b0550550945091029050f40d20b004003c0b6050b1906800c0340000502c42001c0884071f0f64040b40055100314245e05140c21703050307420300040c0c1c09840444041d48000c0100710038595007283c40b20803030100c3c40c1100c3d8443d42d0750019a9000600400c0d060141d5903e0382000c01400040c0c005448818002c40d0821565450b03000082c080c0d40610f0064450354200603018206052440340145002c014002802550b040001c50411545000e0000e0341d01143c1007035031074046109031003880e0140b0010340729603603010235240500210100503031180d06203901d0242090300c079441c4d0b4040400c4010100c00002803040359071400c000a40140d81c00917042e480c01080d11010503403c00d00406c6450000480b007600c82d40c8035692031090f06c14030300078040010070860100308081c00d40101803644030b00007000410695160350100703203807240011710910903a20803038642c001c0c4504450120081c0000780d01852551404100740540781c8101d56a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 722725620 1250 722724370 722724403
    0xd0f02060f070e1f0306050f0d050a170409061706070c0c120804090507080603150c0904050c0913050a15050d0318080f0102071e02011211041e09060512 67
    0xc0d40910740d81340c64040c02400d89050b110980d45916560013002040b840c0a028040c2c1604504c50f09a85445c038200714a242d8410024404600b1b154ac0701c180f05d440c2c180d500016448144030100380001c40e80a80c0002d0b003c00ca1051031010a041c00f940e10b00b5402511007400d202480c551748011032009240c0005907000240010b01110075403406ca1504e100c0c503440342d80c1c50352800013413045469010320f4180c0a03400480c02c4030003400c0c03000a80c0101e41001d880140c3d181c0c108001c42402030405812180d40714208174a550300f4441c9010220b01031000500751a0b44250781c034010800c59400034461034031100703074409403980303500d0600303003c02c28003248040b02405008096aa20040c80d00300003c48001c1c144800c169040107505840c40c2d030207900a043c0840c0c40070042507c00000102c80e80c0c02006a03038050703680c28039024140420000411a8215030507910504000c040b0b84011884403000c00c40748220483e100a130718013140c0008886007504014482c030312035a64945015400560480e10310303200788 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 722726870 1250 722725620 722725637
    0x30623160f02030c0709090c08030a09051c061815180b04064a100b060915040302040501082406012102280203040b0315120d0f02060f07 60
    0xc1030780f45004020000d0102e208012000c100046a50441d204030303817103490390b0140f060b110100161a4004c900550000a40010701004503142c400035500356800503500080d400c00e400e4840005403004a00940031042c00c6888681c01c100c0c4440304032204d0490703120200420400009100304e00c14024401600d065000360200701881403a034802c1ca041d59007114801c501d08a0350148031002c41d0007280c481c0205843c22500d80c020391160080f41c1100c54a03030080c140640080c06c0810003030111100c0c09420a000740010540d0b600d03000c1d0311140c85a10006c03c0da440d00d1640c0704000665005030055001500700c130305100d4060181d06514045540903050358440750f560308004950620480381000000102d10354041c16001640d4001c0c01c0348510381e20310b8a051750807070142c0c920309000f03140c0c0e190040e8010401008120440e001660304a5922070049104081010010b507413040700f042240f0442c0c1001c203070310740c149400c000700000c54001750000d006a860213038007000600100408140c01d021180 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 722728120 1250 722726870 722726897
    0x60a020f1e0c01050f011a040518100b1b070906060e1c0c090534050f04080715080a0c0507060b031009030504050f0306040c14010903050703062316 65
    0xa206039050701d182c04000701300902e00210302042a003420310402201110703d040070800000414119000d441d409030514102c03100d4442c1e90403c00720010700d42e20202d05688030110305100c0c0c0304020603070070040010031042d00240c44a15410000154050030000303160400400c209a00407c041e03000c00c0c01100c00c18450000c005421703040c03415a10b4000c0840141f10700c0800d00214030f40c0040c1c0035a00c0030418101a074581d41d80c201c4d0401c000c1c2c15018444a00341c2c04c003035080d131048000340004c900c4811943c0c00d040c0c0e1481c0203480d2440c250003442685184050305480240d201c804c00b58032030100c85d42030200003005e4a0180146c89002000783c180303a21403095070707240c2c1c0b005c002620b89420400c0c000c00c0300003a10700380180690014015688200c11500d0740344150729001a520f8042c0382c1107001300310010700d4032075445128007602c0301850600a40b01400004a18140002c5000358000c07100411703144580d0840000d17401c072040309400032900d0442880410000d00050008a80079030401f2410107810 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 722729370 1250 722728120 722728177
    0x120d0f090e0f091507020102030103031e080f0c0d0e0c03010e0d0c060c030204030803180c12060c09010215010617060603090c04050411060c1608031204120c060e0c0102060a020f 78
    0x40c14210704130b240f405014009810350550085040b00e0084d5a1002e400c050680d099002c1422402510f0003d070066001c2041041d405103e10b400080905920f85801104a001010b80715680e142007c4d9170007400d0724500c1b03400c080c002c2d865000c004101508500302c3c1040060b004c1241c40401810380d41c5c0d148082c0710294001d5045401031500304070080c0c6c07246030241080850460944500d0054040c01802280608201d500c0003521001c0d40094a913564031007030660403541020310851f0443c41b40344820030002055807440c501815080d90752181ca894200040008a000648550700401d800c0040003c2d152012640300710101040b50045940c0c0c41d1814a4030129000307030345007503000b07000044070780760400005000465204428076003800965038402c1117849024501541104641e488c4c0080c0001c0c07450800c3c84982e0000341800d8109020548621040710709401c204034455107c1c010340c220540e0100a034650001040b81d040d4645a4121030b101160700580c081060946000d0501404003d039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 722730620 1250 722729370 722729383
    0x61103040906090207050d021f09052b020c090f0103061d01050117060114010516060f0207030c030305101a0d0e0d180e1303050a0e120d0f090e0f09 65
    0x8a054040c840b190f11814070100035030290004942a228074106040058000b11303a0030f031142c3c00034030300040d6100390030541d1015212042c4221414000c40b1712609010107000c070706035110b5150401883c02d40d41c0002c800703031401c016846424400c5040c0b804001208119540c5541074030b900c000045109003078500c04a40dc00811000300f1825424030740081240740d0014020f901480c9101c040750100c4e40e8070840754544c00c1ca0000175a00040003000311032003007509541e803170001510074100011207070702407106c1c00201d82241d00120001104400e48806065040c0a4103030407000d081c40755001c0a1908810352411680d12050061488011450078401c08859100001d9501c2d41801d441e400c40c0d00040c020328001c001d0100052404a24101181c0382c01403103030b028462444a4014401844540c4055a03140c120010b40d504001c80014040c88031307191800455884120580200000d5a045c080503041c0c00300136100804018074000200101307822008810b0f000300c20070104210702d4448503040c508005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 722731870 1250 722730620 722730629
    0x270602030a031e41042d080903010f140c0a05040801020a0305100b0c1005091204030c090e0714300a150207020d0f0f02120610090603050604063602030111040f06110304 74
    0x80f0060700c2e440c1404a6103008001565044008125411041c0c0c0481c0845089025618cd10030b5075400044061240d00010810149a401c199040036964228142640d11048032030300002d8443c418004a00c25400f031001c0074042900e80c503030a15505854040d6950480f01d06441002c0d1203d000c607038089014420b81810b441581c100e1640c564880c145204503c4103840340611040ca09400302c00103040c00f10340d14082d11303a544c0340030b01d002400004200e822121000420001c090103445441403100110620744404d401c031000e4003150101c1c2c10501c240e00b10700143d03045e685004101c1c22005a40703122003030b80ca05a004101051070701280c10101c07400307401cfd214000d40140d10082500040c140c000b50b280d01c12512380341a50756450f2940340e25420380e03c291000178410b0340b18802140c001201ca0300a03c040284188a80e1152440c0500c6401000c4100c10405183d050701d0808006604081c0108403045000c0d00e41c241c94246000174002c000b40083c4030b07540421850b0541108000da00340112030013403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 722733120 1250 722731870 722731943
    0x3228200406060e0a080604030203040618050a180b060a050708070f0210020f010c0203040b0a03021e0d06050112360210270602030a031e4104 62
    0x4a86a240c0a440c43e400d841e900c034419800840b00154010000072014400c0c2e0f81a8065424540b501400340c421480c0380503141c084010064010a42c1d0302d40d1681040149040d418001441c18103908880440710041c03443d50240c617041001a4810303030000f044038412948141d00c141d0b2540c90b81401190384c090020025400300c1a0b076040d230a015400035031050a003040a0082000e00c20700d200980e030340e00c183d215858400d60240a070b40c00031030081e0b0103032043c514500a88416086001404c9070158010100c03001c0340c550b80c840c10b020550307100004a00c1040c011134104042120070f1803405580610541e07914001010a010b44091340070f071034502074070903406480c84561080214024164081114403080c045030044141d190700641c03404840d080310100d40140d86042c010407012009809006250261401010781e085c00d841c502c1d1088121000707521006500540c603c4150324001411405034000d0203410700c4400c0e0300c0015804966800c0341e44400d030480018903003590018040b55030000c10240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 722734370 1250 722733120 722733131
    0xd150f050112060503031b0706091d060d1205040801140c0403110118030605040b060f0907030e0f060c0928090f06050306100905101406030432282004 66
    0x10812409144602a47c040640307002c81c0c0c41e000126901c0003140f00d462402d50050800d60510b403020303445950041c501800090140b049a1038030000040da001c65140001c40c00181000400c200784641c80044440c90b103960300d02d040141000e0180c0c01503000140028428204410303003a030145642525006189080100c400d5480c06c01500070b10085400360703a058155030000b1214546817007039100050006280c0c2c22907894850f0f00700d000703200390007002900c0c1c82080c500403450b440030045144a00109580d031503482c0805414084035800c1010411040d1840c000762460f080c0c1c003c1405c200b40d60012100140e644232500c4810007030200ba61007030750907018410501815401401d01c0a05991200e0f2090000f41c580c1c540580036188540710702e04075841c02d80c4251201d8076058000f544c00900801c0260580c00c00700091304400c501d4600540050300750480c040c20a403c0c00d0010a16041840a06021b4540c1e14050301c040c0e900b40e41c6005007440e0102500a11510340342010380351824002d0420002d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 722735620 1250 722734370 722734387
    0x1409010b0f1306090f0626060f04021b07050a051f030209060408010207031d06090d060f020406090e070f0e01081b040b09090a06030c1e05090c0d150f05011206050303 73
    0x20380c1d49401035140032041c80300081001c901486c070714540c0c03444c82c0100428498004003501c0a4200143c481276000f0624020100c2071390303071400a0a00d0a520416404041a81000d00c6240240035030040b0f02a40d82c404d400c1001da90b03120035100300e0707a8400021041a0040b47d07402c034028030038600340d00c1e0f01c03090105006c2070020055000e800d001d4072a8a562034218001e082e0500c20500e00800f01d5130180302001640d0003410100a1442c425200d041c2c0400d180031034a051000380c0c0c0298000400240d8081c004201000c00d18001d80c1d000059400c00d005909a0448000c0061b40e07120b030b4080c11701540e000483c00907000c0e4014010070005455865880c0c5171514001c841503844110f12501c1107130300b1030200740c00780c8403071090004403544107800070202d038940650159003c4810003528072001114000141070b8881400c554810107108040315036404212040300102c0311300034800580d101e480807090000080030066002680c4007400e1024041d004981d820000d0000d6403c080d4240c040841d0211 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 722736870 1250 722735620 722735627
    0xb030a0609030315032d06060b070b01350c03120c010c140d09170d0203070305070f14030c1b0f0f0a030903081e12060a1409010b0f1306 60
    0x400d02c00d54003800480b40c000486040c0116034040a82020085400d582010360302511455001950740d882c4612004152182c038111707401540102100000090070004011060980034003400c2e0210420002d0742900307006491210f8564a20f40115546283c0540d20303403010000300d10701400090840e500c04610840010707031034200d0001104550f00f081d840070b41302070089510300c442c45201140141464414020f14024000c0c560342502d04c01680400603051224100050909034403e42d400360313590500d54001001c03201e00508207801c01000c0401c50110680c441c0c100e008441002450710f45a032290310449c1068450303094002c81d03030f0411132161401000b002c2061828850b00c0c80542d4200d80340052025282c01d0f00032001400549500010f000080d0484041c0c414003144c0301d096564000c0c45404032120768040c030643c403c020301c014100034844c80e08080c3da90180040940050351543d10b007000c00e04400042c01001012040403c010388140b000340c003515280c05a440800b1f81c540d0340c03130344080d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 722738120 1250 722736870 722736881
    0x140a0c0623090f160308120a0e030c1b090103050309010809120d09050f010204180e03040b0315040e010c0e0d020310060303090f0608010b0f0d0e01050a14130f03120b030a06 76
    0x101d900e00444d1145040c030041580f40e10200c03500040818513082c071415540d1403001009051101d0544d80d0f0703903040c0076110b00300040d069a40820300280a8260180e080c0210704610340700c841e00c1030b28484018800200040b0540c0c0041d0000c1c200800303a0740b106100203003004400820103c00c03020105490780380046940000d1171480c0118182c502c1c0083c04d006840c243d105600030444410050004441e038450305501568035203240006880c20151582c00e4909140e00544041e10860040c180d00613103860548205110703c0041c0d402040000c004003005490320b6207240038644101e9000c10f1020640d2404c0c4040d0002110401c03041110350380700e241c0580a134070035000e003c81c00a0051008550207000e600898140d81d40c01800c2e90429441c1030a15140358450049008034680303990003c50b0b684000d0041a004192022001c100c0b490000f407040b1a054000f440146019422543c0801080717401340a1140580c05203000148019603220000150403503c1c80701e500f51040e6400c89090214946c0403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 722739370 1250 722738120 722738143
    0x50601200c0a0905060d0f15051509150f061606090f0b0702030309070510120527030f1204140f150610271e06140a0c062309 55
    0x1458141c50303c1e0300c03000c022503008440107600310003404155000301e100c0003600c02d0300d0751040c6600e0303071000791030f00385138058034010340b0000100a500700d0202c502d4500a04425400045242000100d1003800005040304010304169030055000041d00c1d154820309051348a110303a008002400000c10500d80040300c0750401380b05507003607010280421400b62010080704c0c01036a50600400d081418582000b02494070711342071506010200c10007105400090251621500001c144c2e504c4105241c55460300481e92035800da14580c1040014001800b90102038a680301a40b4080e00c41c541c3d03803854648038090070704200840910034041a510340103000507048001480c122001c40c0343d40c44a2061042c0805607440c0003006c50009184142c9141d10b02d01c00c060790f0344110001c1e42c01d6542e905801e80241e0014403503070000c0c001543e0144110341c0c025010511209040c2c444600d440100300c0018030450010304002c0c42d00d030700c519070100c0000d1100020003054509420005103410310000d040d40c2c0d00002da50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 722740620 1250 722739370 722739379
    0x3040b070303180b0105060913180c08070b0d02090406081c030f0903020604030e01120606090e150109120f0c18110c0a1b080610080709150306050601200c 68
    0x8481103d9440d15000ca030500d81c0c0580038181a9007020b04200c1c1c070780c203c9000c230f9400042890004400c0310050103006107402280300d03130f0650480f040c2001c0d0503d011075006004240d0261030f08110000424080b50414004240c00503110707003c1a0004000d0f1482d6130014945104120781800c5881d401c400f80e03001782d03d05032030070450742c1013001400b0183c0d410001c014000d030300020b0005d40440c0c029005001002d00c1450030741201981480024101c5006400040005880a4043c052003551180c041c1d004a03812404520803c00300b0002807903007565004800c41a103ca207004002c014a00201c0b0201c25402070300ca0404640f01c8851044c103881a8182c442502c0c140134541e0303441552601190040c0e0702080c0604003511030b83d2682c2c44000d4050004104000c0e0390840000c40e081e041c808240180031b00d80c5034901032407401900394607018141e088203c0f07151420305c40c4064215038108a4040704e500071000b14066aa810058030100c02200344580c01520401215030034580108165215010454 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 722741870 1250 722740620 722740631
    0x10806072304031203090c0801020a080c04080d12110d0504050c0a031e39080d080423100f1a0a17030c1b0117040c0b090307050303040b070303 63
    0x1203819451000004080900740d0104002c0c4007080c1c00404484d401e0055082c08640060503550700b07100a0007039401450341e40d50102d442d8224070383c00003403581c111441410860405050000085e2511a200251010f008084440303c03036420054201452000318080003a0311144e0940c41c1c580038000803035040340d0700d01907006090160f10b00640b000b002d690300902040ca1041c0000000314419101000981c1d602104410b451b2066016000c8419400302d00f10000500a029660781c0b2910880c81d0001c0105170071504002c0c1015a212610990181c1c00c03412407000046011400754107041e101680300003a00400d8490050b6070b100307401c0245080c00148041100e024100c1c1240b550500041c07103168002c06c0807404110f10301e00c8404800e104128107060740d01d0103c40302c00c40703440c041e202d080341a803c00846a210704150f03003201314903402411200c403e00301032070940d8800245411a0180b80c84a130000f05021611381c40c1000400701410020301103d076256200c8580c050030b508091000c50010741403c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 722743120 1250 722741870 722741897
    0x403080114010c170a05040e0108160f03050316080d051e310c1503090506060a030f020907141b0c0a080706120213031101031b0c1e0204020301080607 66
    0x200680307580c0030f82144400d0500060340c01000c4e0a64040644d01c2c08000080c00041004c4000f00d145a000705138a03401000c2a000303030314941e24190a29400100c0c06900c2c0c6800f00003003803001c411100c1c0351450241c0c01581100c58584100e0034011600e0f400c20080c41d007000c001d002840c500c0d44031040544030307598245650340c21001c68508148010a50008036a191981244c030041c02410251140300b8400e0103441038549203120220b0051000384800252100340784828400c0c1880710a8002605840c209103881c1151207880c00c20b098100700a01841000f00060006449410480100c051708a4590f03078900391080141007990411403134010b14001c284c0482120b2038002000400c8941c000d01401000d031910105898005048020004264080001d105000d003c81440d2026501c11106101039030065000101200c030074800d00760030064203d4160b0f6203542c0012400043d1039005030146400c00c01c080f540d880b1020400e4009401034004000402c602001050040c441d912581e40c0c01d8400341d41 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 722744370 1250 722743120 722743127
    0x309060516110c010912170f0a03110702010f1b201903020d02060703050c0319020c01080421020705030118050607091214210405040b1206161205040308011401 70
    0x143c542050102c0d100e8801000180b80d44480422040d0003540c0c0300e81c024078035051000d01307035214801c919107d4a00040382c411a6415108400a141000764028203224441c1e0018100c806207070701d004c003480141000080e00c040302001e0003004581c00390000c000c0300030402e030040d400d2801003142d0388142c050802900c00c0d0031400c601c807401ca9400600b45190101c5030380038000301c3e9000d1801503081004c10003d600035100d081008050400800e81c118010220041c0028100041c943d49a410054444280720100c2c1e100d041d808a06c402c106010043c10301022816464010141d10054042d420440d081c85203646061000703019500880540d07a1541d40c01c0c00803a100d207654040d0840c000724991501c0007007041c900c2521322250307000040f106816004ca807035101c40b2246200c24042e40c50000b50030301c03036070410f0300403ea1051000d031048905800d0101d5601d854540042140c2446490000d140e580d10344141450700701d4405403001040700741450b05008080f14400d000304c95000e144a84500c0c0c442d4032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 722745620 1250 722744370 722744383
    0x180c0f0b070803060108090709140412020606091504150f0e01081915061805041203111804020f0d06081b030a030e0f06040609141005040b0a030906051611 68
    0x180850464a0f503030b1500015226118090020905d44c1301c0c80d140864107411502c81c01005100d0180c1c50441e43ca0305140c0807101e54200c0b450b510854012200744501600c607040515000044401e40c80000d0581401140040c55138030325018680360700e8200000c80fa00800f0740d8105458a84005050503a20383d81c40554400b000b00c01d180c0242c01c220025004502c0302d00c1040700000494070003141481c0d8030031040c00419052180d2103102a507400c180420040c82c420b210703101401c5404c0038441d40d07402c500700030000d0103010b8402c900d800e07070394503d0115980d82e036049601d000740c181e24881e04c0303a00101c840d4000740200d0042148030320585803007102a25203012500d0791004004c00502c40d40c2d1031035038100e82c0ea00301031000035005844501000d07041e170b50380c0c0c000d040a4035071035440e001500e2070503034171204045a10819a001d00340344c285010365250302c5012102500c401c2c04010f0b40c3c5010303003582100203154240e4060b246510f41414001080300c00948006000305641c0e4403140c04203801546501c851 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 722746870 1250 722745620 722745623
    0x5010c05090a1e17010e1b010207180b09130507090204121101020106080618120301030309031e061b02060601141603110a210801030c090f180c0f0b07 66
    0x81120500f0011030540e5180d004100300c000056a00c9581d46500f140000c41d00c040410720350741d4490f5500c021410041010002070741c50014450b01c2c0c40c1c2c4500010b51900c0c1c49008000304159900280901031031182c000700c0381c0600251a0346404d18092983e1000d103c8900b0701101c042c0074075100086c0104041c000c1d5016201c0c10400c86680c1c0d2242e0381c44a04000c0652031349410343d500c51400040608003442010701c2154002c041c5102401d00b01001c1f07041208001c1f54104e0344400744014030100768446e9012064036402680d00c1e449000341d42303010300302c0d041c042c200400107070500641200b0340c040b2400205004015408464290301d545005403018103040e1000640d205003440f640c2c0c100203500140380e41d10341c000d0a040681c0f016203ca1142072980d003000607a690943c9490149000d10000c080c0e1b40f00e40301601d02602d195042d036854000c2c0c61458418940c15580303c118040049d03510390320000400e80d081ca200c159001c600d190465409000c0e214404400c00c0340000091100c92000c1100c1015 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 722748120 1250 722746870 722746879
    0x10302090f100504020901031514130e0307060b0a270e0309130b04090b1311030d08070305060f0d050c03070503120d1d0d1101050a0209093d0305010c0509 68
    0x10b07400c0c40244030081d0422140b213410580c4442495242c000b280316038074040c10318106218110300321030092100032360540307824000da68627000d850781c5d1180c40402520b0206500140210310f02d6101c0001030384a62103900003404080c07405080d6424040507407080b10680c84100030a00032940007003182c1c0d440c3d00034000700d130360444d41d50b40081c805480c19500c0700c981240010300028000d505516440b580e44da080f120302982d000e000780e41d80c041c04052045249201805c0300200221791030501e000b094402e02401d186c0c1030503256400704000303994030348841d541c2d95009841801692021b09020380d48121007020907000380580701001c196400d01041300d02c018024032101610340190110440001c2604c4010300c1003030311411041d101c400070140040404008195140c108004a404a5030b00310384014048207600c40c8100003420941d100c200f55658010803200304041d0002034140c0f4001c02540040161030403500e910b4114103000400d00300355007540d010f807000300900c2d800d001003a2510312458014681c030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 722749370 1250 722748120 722748151
    0xc0f0f150d0b150a0f05041509170721060908030c03061207050d030e030307050f060a1a0a03030305090f0118140609120f0d090305041d0c040603091a0f010302090f 72
    0xe40076070440321883c81e003894481d150980d1031813000110200caa0123000010300c644800c100e403004031140c034803980c03040002030700e585460003100d4484555407240054401d411091003000384100365004a14443d00201216074070718001a5030b0109074000c450143c4601800b521a0b60700c100c00144100a460001c3c00f6918164100d440030368001c0701e4200724030307413505c1b08002800004205001d440000c1c46064020b0205040100051040d103c80b500408401342404010034aa5a0762403001c0d0102c035058100041e05403186166582000103c0140c61415800c0c04805e00d0504091004e120340175004121028055540d20f48207a120503003607844c21034680c00f0010641c0e070106044002c0007850700030340c1c0071403402461a400c503050321031b0840c043c0d000c01c070301180410801c082a0b80c00380b6503001401d102c44481c030340a4012942d502850148404150703548040b201040f4215042c0c003440504280900300a182030818481d0517142400f04078015210781010441e003209110302c00b4000c0c0502e00f0381082 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 722750620 1250 722749370 722749387
    0x11040819081c020c10090312020c010b0d051e12040303320c0f011122030609060f05010b0c1f02070501410105130912020a20030c0f0f150d0b15 63
    0x28ad08240080c0400e035580d44100d604644e100d10007030320120310a0015110450301e24800100e0796400340c00c0701505402450b010203d01c56103008640599030706082105019400e2103a4110b060810f144022091229803010b9003801441c10103040804580300440300c0c0402140190740c00c2e0352aa00548610680a1144403c01c545c4100c5201007200c0d005070f0104996980d0f10f405041c1c401d501e20176100c1303964031a8980c1303d030f40440c00b44601501000b0103041c50030520480b400c0c0d492070340d0303040703001c000103051100c03101444a40c040b00c03001c0781c00200074444c44051070b20b101d406076000c500c01c0034550f152441c0e800d0986800c41b144083c0024520607c09940c0c078107000d020000450380c0041c1101581c0746030650000320319924114001d183ea030f000b08505021846d10380d003684409045507da15850b04131b5208143c0e030001d01d80c0000c001c1550410030a40468010454821014400c1c41e40203480c0b81c1d10801c0201001c0c00750001078049041404105515030a004005001c10b0b120020010304200428 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 722751870 1250 722750620 722750657
    0x90605060441040606050a02061b0408100e010c030509070b07031202120612072105010b04020406080a0b06130306020a0e04110405010311040819081c020c100903 71
    0x1e00401103502c8940103004030800490140c000144246950b8502951418503418244103000242c0480d0a1a0785041011030000e580c4010040041d003800000c0103404200c1d244820540c1c008151a5041f00c3c0342040f03107600c00740030340303a0028007c0c2158a030900c15107480f8440d002e00d44c01103070507030301629145040c090f5100c281c2d8000c01c801e80c2407011243c034034030203145148000c04000c402d00095030410300713010301088003601d00c100d0200200d901a170402e00c01c09416551780c10740b0601004008003021000c0c9003907800f401d04c0c000301c60b80c450300c042000141d40b0f81260469100f4562080c0400400d07051400300410b500a410203c090340d0003200007400010450b90082002081c141491129000003070006410780302c0e03115020000300070101c0d041202d5601405810003003004899007a003441e0900d040c071780e51100c18681080403e0741b4209900d00b0301c080c40080ba0400c040c0486d042100e4002000e41130069401500c42c50039038403801d82c02c01000e2a85100d4107111945c155501e00244030541b2055 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 722753120 1250 722751870 722751899
    0xe031809100b0f0702041803020d180b0a020619090302030a03020d0209031c1805030606150d0507020105040317090a02090901110d0903320307121806060906050604 72
    0x341281c0081078000326a100500d00a400c80503243c225059a40f031051060000b03a4625603203240002c003000c00a100001e40100307406e2542000c03403034820404045130042050740510780c0e114004400c40041c1a180b41c13607012440c2d5104075800d514002ca40181c0340082d1086801026010340140c10034000c0c0c0084501c00e400814640c1544000903082c5506500060704203682d00c1d02480301c480660507125402038011190f0000081e0601000805d10300e0000801d8441a008144a100381c6c8080005070b1403a076801c0a071000240038030320806c61841c1030800a03000f080c040d0b03401e8000ca100951502c154620616040c2d1003000207034054280c04581d50b00748041007101418200d41c6540702c0000000b9804c100d000f520f00d100c1180c00118000442d400c000c2c03d609000350407402c10a0b902c40d920813000140341e040707800c200041c041844ea01e66420f1400c60380c241c0803241800702182002c000300034003800840428030060107008100301440d82c40e0222411184684503041d00150b060008120040081402 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 722754370 1250 722753120 722753131
    0x6021609020a0c120906080a090203120f12090a0c0f031a1803120402120d0c0305071a071115150f0301150b0d0e010506011b020f060a0c03030e031809 66
    0x80ba1141d10180d0328130702d60654002114000400d006410010243d0000661b030f000041110308108407a1150082601c1d417a0113251403640500020302400203078800d0b0300300d51818050044802d25828880e10003502c07400c401d003040e101e5003480c280100b21641c0c8004404100d81c0d200c07020010070003610100c5c00480d00010014045602c4090a9640c1c12100703100805043c0203000c1480b50b00d180610400001c1c038108501ca4180e44e0122101e00d800d03d03007000801800c10b806050560b160241450070f00c0740480c43c0c28034492454045030611500715081034070480002e03910f100f030b24500403140110030030f4184202e482502020901030420b0107400d218001c039124060150020580c4000c88850149544e100e81c03045460a0b0001418002c00b0010312800a045000c01c00030300c82c900300640003c000301d407480d00e20b6500c0d00105a1b0b0701c1c1103594100b035528401d4005448181c80e0f140c070031000b90000d040d0171700c154046420320801544081c004011a07189800e110840d881110000c1c00f40074000700300500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 722755620 1250 722754370 722754377
    0x1127010603050a022812150608150604060804080702180f160207050f0102010f02030106080709140f0103050a020c01050106030c2007060c140307080d1a090105131808070c06021609020a 81
    0x44101c2c4110b8a001f5901e0b8609103c6c4801c0e80e4518010005020701d2005080e0865079405082d900032998940f0202c9040b1143d5107010001c40d00d031410034002500c00e0500c000d5000300128445040003039242031080c42040041c4403840341b50b88154071940c030003410412150060300b1140052100e454000614591240103200001d001041c020000080764070a8000c3c50119850008000600f90300941e6000582465040b441804211381702140b1602c07010705100341807640b2071002900030300c0c030b50381500c0c0d1084a0f0340080c030407942c0d98900a00280030640d9814000f034405481f482041180c0581030301c8401820005100f00ea207408011030708029198802c6540341e00d110302c0503a43c0c1004101520803203010f88445a5105103140f1040700304c0d5080140008640d1403140310780d6195503900855411298261841204987c4a0032044010507440c0464000e10400425081c10300107a0b00141a42e1485030051011290303c41c08284d035104408956450300c1d8640742418000b5400d05e4011b0045a14a0300307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 722756870 1250 722755620 722755637
    0x30a0803091009140607050c0c0f01030902030a061d150105060d020910050a0914010807111f0b040c0306050d06090201031d0a0516050105071127010603050a0228 71
    0x180c2c24151a0607070425240ca10240304041076002c000d04c030711034000801b4101240b0700400b951910b600c40c20b111082070b215101c1b031078450106901a0308030881891f801410b03a03040340d01c2450460700602c00613441d25107169600c01c0c8620440000900c50381d014403c100c030448168039050802c0b0840e800010451000c903020f12040350a41c4488a4800000d940780c2c03129600e4884500d0300500140c81580900c55200c4140e00b000240d1f40c000021079088059850060500c814806100c0c0c0b804410344860080b500d800394000c0c0001146078803d00c903011045070144a0b15107030900480c15162580103150740a504a07004c84001586070f88801e2030b8601c10f0402103035684400c1c0507107100d0120600102d002343c125000e800100300e000d0008005400c20441c11205c2d840c14540002c0550050803401810030640f9040d40b40b0300c0c0c0d43e80c030005009507219075030f0030b0195000f40034180800601f07101d00c030301083c10701c404140301100314003c0d41c440c1c58900c540c00b4007100c14080b4001da80b40d10003900a041c008c412 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 722758120 1250 722756870 722756893
    0x609030807110604030c060206130b041101110712020111070f05060c0703020d1202010c11030a050d15090b0a06021516030902120304050f010c120f021e0606040f020702030a080309 79
    0xf0400b9000442c09801001652407400720068104500107204480c200380940944001404400c03d907900300741c203d51041c10312107442c0010703130ba0394640003a00740c0e4512a54000080d42040d24142051851003a85c8400103060300300d426035502d00f140c0c09072a008282255007440340c1e0410030007400e520b10301402250960755480c1c0104600c0c0c0d01c0c10708140d801c3d20414400a6403d9024003800084601074070b49551b041040c1d03c0025102d00911801c14100500012920303180b0f01e4031b406c50809103011240c240c48003a80c0c0c11040005210b120f050750700420200000191160002c140c541001110308052802c0c0d0ba5100729407004000710140c4402450350360710400015851b00500c0041100140f00259941c50421081111566418003550304002c1101071440024580300003458a00c100780c106403000782c1010600b40c1c100700744051480001088045600c031541c00c0010030300d006a40607103040240b903100541c00410380c8900b40c00650540e201c0c00c145400031b661038000f560320000143c10f403012078644 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 722759370 1250 722758120 722758129
    0x15010903170d050c0310050f01030e1605010207062a080c03031911070201020a08032d0106090902070203031b03130305030304020a0e06090a0c12050702011e06060903080711 76
    0x144400030065003000710304042041d41e14443c85400000b0700d21a07500314034241d54a1170759140a80902800781900c2064041030764001c0e00032802c80c10244087c0c542d04d07031400544803100701491080c6401441400400140d640c054440141c0c1d003403080b6400f158004200700c0d620184001c01c041100d641e4401c01041011440c00d2024501500140281144a85d400740c0c540381078880000d0030310b5103c01e007000701c031005030f0300081c030344048641c86101c60b5201c0d86d4000030749400c0240002404110301075008007c0030000d00c90b400c01d050b62840e84a0441d00c40e156681c0710100c1c0240c1c000250036500801000c0d08840b101c180121038150340c00c00b200d01d46202000342c01020780c03559004990650001c8144011441c00c080c515010384090001204207140010018180200140c84080b0050741e900308400c007180b050031420300400184005000c0c90070300c40c2000b4003c00d400c05881d03001011400c41030f000103a007805414115012a9240300a050641d151a103043c6e2011004450018000441075180d44a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 722760620 1250 722759370 722759393
    0x10314071703031e01051c0512030405032d0409021b01020f040504140417070503041a07020f01020706233001090506091303031401240804050615010903 67
    0x501c001c0c648a0801030b101c1010694030ba40e0740b50311641d0350320050055444001c010101e91801008402c00002a4205142072000540e030b070084a2030f00004010600c100000200801e02a0500c6103080078000940700c1035560750400007442c4900200820003101c802030300a4000406002140e0103015124203089003240d00510105c2484500418104840d26081c8160000b00710040c1005d180381c034190765104825004146c6a42d4090800701d40f100a2100403c2690064001042040c04071041d0100e040c0080d0000d8004a22400220a07690201d5101058103811204030b92504c05d1400000442e840050702a0824070b224480240040b0312154280c0f55000010503100d200d14045004014550103a204160802014541040103201d5180c882c00c0712294000c13040440a00c80714070a1508070090020240d4a0300c203c1203d000120b80e100881088545018428400501c8000744140c140c800d00001c641c06005a00104006a50b0508200e03108800c401c1c14035044009949036502e254802c507 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 722761870 1250 722760620 722760659
    0x305120106021e06010b03010b2206030207020406210305033705060a080a0303050c0904020d0507030605120303150105070b07030203010f05011d010f0e060a170a0c0801031407 77
    0x2d00200f10f0700d0044510200c1500d030084107001402180d070511103468624403040c8141c00341c4c2e11000501040605409100b40d08600c403612010005c039584041c014080d4104c00c405038861440d2200004d4450007241c2601ca6111025840306280141c5032020384507070700028005082c0d51082611040d08958100d210000038560741d00d000541c1c0c035080c90140840d20003d144500407481c0c0c075010301881100269041c4c40710342c14500800c442da13540c0c01c12a6035005407244550898004208001750000e1900641c0c443d00840d03030100080c517503420810242026241040569400410101d0607180e4400e00402c0140010304041e480c04141e0340d83c5421b5940d0071110440007a034040010720000b01024840c0c2c00400c0f00f464040c0c82d00d00c10030404041044418081414090071000c800e02e40d40c0a0104000e045600410362500c814000102034031448007100c244021044003000500159103501c035819002d01d0303664411200d6030035542c40c1102c0c40e00d0000b8141040c490102c00080714041500b4246141 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 722763120 1250 722761870 722761873
    0x20315120f070902180909300a0c0605070e0f0639060c2115101211190503090a2108090f0d210c0302091903120c030512010602 56
    0x2500c4104285108103042c0ca0703046c0c45803144a00f80840000001003040c6a0640704a54182000d0480105c50b908000b052480c0c1d85500c2c08a85100540d0300300d00381820b4a801900c050180340e55803081201d0403034220413031560012801c08280e940e400c121024008810b500c000d0f2541501d441c0312030506a0014503441c504038039402842d020521801e1159a40003000c03c1103190900204506000425481840e07403200c013072208001038a101e8001c03041603a2a200030300352a01038100c010380205003002d800300c4042201d00b824550910020340900701d0f0461031180407555403039124000121099031001d03042e20308a210704005400424000303e10090062440300781e100002d0444131002d051034000411100c3c0f940c109031b880c010b400d88007082658001030700385803424500120b05808401c2c0d01d20341d014030310b009250440100d151a050360003030040780404c5656000a05a01ca004440748049000040c59200d0b60141c00c11240d00a0358114045440390900c0d03810200f069004003400d440076486075006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 722764370 1250 722763120 722763127
    0x90302030132010b031801181b0b04030206040b070c0902120f0f10050f1207080115120c0909060f18030e0f0132030901050a0b04020315120f070902 65
    0x216800300c210030b1007100c40101403a51640c5045030800c0345000013014042c0340c0003015040c1c0740c112000c0d40414080d840c0c003c00019100c0340d03030920b924001100980c901103410214000b05028902606690844e075009280c41c1c80d25062410b4400d8503049003000701c0d001d80455030b01050000090000d08860440e4120218103860610b03004980d06502404500e01d48c2d088505010030b81c1ea6a45442054440a0b1007962030000c012022620081000c40703480300c0c600480030089041070041d00300034001c0660840e09841c080d2201c209140d007043d401030007404803191101c1005040e0094006000e01070160100140c040760705090030041d108000050a4035042405510f03041603040412106070075421f0b2901142c201c00ba0001030803100084070481810788540c070342d106140c8160244205454035550a0300c0c3c6034101b07442c1e424060107013035410200450400c5180440e074100352007906c0c8111020707450500e1000601d0f06204070044424412141070040720010b0142500030007040d8002d02c0003100059a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 722765620 1250 722764370 722764421
    0xf0c0807140d230f010b09040b060409080c030a0201051f05101b020a06080613020c070608180a1a09010203191a19051207030305121305060106081e060307060309030903020301 77
    0x2100d01c411034187c41200c40900340400701d48500c2c0c1c0e403a400207059500068080c0300d414008401d0145203201040e92000181c04845640d06400050043c80051a00c0c0c4250800e6105105091414003485800100000c00138600e1486204226007940c1b02c81000b00c07406103250041364214410350071050110f200601400902d0604891140140c49654000c60400704e940e10b90584801c0e4030b03c102c4080004c0d96020071041c0c2141040c00702c80e00101c0c0110b540b25062031620f203904515080520350351651840000302c21003c18002c480c8a60004006200001c0c2840c01c0d0030000c0c41080c41c204120030f400018124079441300c0c24100021400302d1400306109181c1001c108c2c040354034013000200c0c0d800c90036007040000d8020b0240c0d040f0307401c3d884c0560000d60700e00e07000c0c886082c42203402a11038404ca00c0006149030b044400e403400347c0c100c000411529165800e4070347e890901a211607406074000302c41084814843da00194078507120b45800c0030103641c3c2c0d400103802d44984601111010320025200031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 722766870 1250 722765620 722765623
    0x14010935030103060204061215120c090204090608070b090f09130611092806051b060a0615030b0117060301021201080c040b0d0305070204091e0f0c0807140d230f 71
    0x141082c8e544005001c0d104c024002c0d0b12158000c0c0c41801d01700e8207000314003010000442d0414002d8041620215199540d440ba00b4001d0000f07449942c2c903a002d141800f140440800e0100c400602010b801c40d00307001c40c00801d01000000082c00c40340780303298031403400c4002219030007070030b0840ea100e4018603111400d01c030401941c0228940708840300b0000c05840c804d059980b840c104200c6020303061141c1c65800881d02040407041904146100d40112420000080034603400304090741c00340030340c0b40010006c06030b0950840358141081e0b800700b258a040030745955407191900b40d00090150025040c03044488080242c44400c5e08032820a81000d107160505092074403c200e0b00310b00c12034020150000648020306144500607001c2e0159032151039903030502c010700c032083c000342030140440c03400202181030a0b401c40b4011141214040c000520000f200d807000a0481c0c03c0c0c59044150300b01d40f20b1028100099041151012074007240c418000c5043c0700400c40c031051440b47e0b240007424103001c00400a5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 722768120 1250 722766870 722766887
    0x10609060c02030a0b0606160c090c11031206032a18010f381201050a0b0f090f1206040c090c0e1002010e06070c1401093503010306020406 61
    0x200801c03554a1007031000d0b990000308050082c0e0001807808054030344402085840c4100f005103038100d00c2d0188004200811403980c0f0085070310f501010803029030f82d4102200c0102c030b0150100300c0b9520600101c00c541100b031004c107411540080032101015945201c0a142c120911101c0c052081804600040b5090012141c00403d0003407d05142d03941c140342c0c11703042c02404d5004008582001000707084c2c05240b000c07014054401d010140f041d1403607400e144080c0c26404100e241c40b2050448000269509041398960203440300d03a02901d00300807420040c4c101079000240015402181181140b06640f01c95000b0039103c44540080e000e1861309042105c01c068569100c00c000901e45000e24817229441410a1080d0380c00303c404402040307050b50304034050030704e00030305043c5401180188245a03030095a40031019208034000181d60900d0200b240c00c0311301c0c1440c0500203042412074004e42500c02e203c4401000c8640d55481c4c55055404400803160b00244c000302ca50a078002001c1c01001c0e0044e505 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 722769370 1250 722768120 722768129
    0x10605090123100c0b10050a180c0c1e02010314070203071a060109260f010c0e010c05060c090d0b01030b0a0e0a030f081005040e1c14070b061f0206010609 68
    0x703e5091050442c0000c02062a001d0058148050040400c40246411000078020038008150503030442e12003005005c40c40c910300c1d0b041d144511b84a1000c00f02c0b40a176420b201e0103504003500f40b0301904010001480c082c4403001c1241050750760740c81c1082e21510b01c000e140c05001c1c540e00443c0c40c0c401e180380c410010544803070f00510543c0400c0401c60b145ea803155000003550800407222884840c00700310351a2210305d404441240780140f01d865440b06d0300552002c4003204456407804100640d1100540d10b42600400140c03036134000d000003401e0036807850001e00308600040d00b50220100b4a80b200e20304000e080e0022070f240d51082052100316603032030040b00001a0800c000e484400d29542d0043c01c150700442c8480107204200d800a0104030800101100505010b0828440310891100d4180c503a61894080f0319280e03194800c000d00300c1d216500031104450300580051504c102c98541c0490741030000c0c0101d51011001003400350082c0000721440d1b000303c2a800070403455050110151011000c0d400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 722770620 1250 722769370 722769379
    0x90601060507050c010c03051204050604030909110412030e060310181a0d050708121b030f0a0e1912110907120e01180b070201240603050702010605090123 68
    0x102d800030920115800190703003402d09003030039072448a00d001d6406010f1507501b4848400395100300300c188100805c8051040c0e110b0303030320720300310700d44950079401100c0c0214600c041e405400c0c0024003480401c1c4d45420300943c000d040a003049015040043c0c265402280c1ca00740940036020208181c40c551980ca61030002054028856007030012601000f030420300003000d215880481002d4140207040c030214000d0b08000c815511502d20482c40b0700202c1e84100c2d6280c1d0b403030102c0c0254446003c13020064031200340c10503941e10302d80001144106c8406004400356a84883c0d900070080031035001000b45002004d6200c80100e6802203410aa400b2403444941c25000d041a201041180f507448060030410381002c8a0000308450101e140d14010400c040c178104408803090030a03400d01c15070314030051080160390300070f0100c443c0c40c0103040d50180c1840e05135502803004d00c000b030000d03e010380c003c40e030300c80741600c00007072480d0b038400000b2000c81b402e0744403c1d038000d1080b81d0311b04a0032072006001044501540c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 722771870 1250 722770620 722770627
    0x15021e01020720210d020c0d0209010510030f020d0902040f0501050102070b0f0c0d170114222a12181e050f240f07030c021002120906010605 62
    0x2250040382d05608450304207111180403c400a6a84003940e081050998020380c002120201c00702543d602c10340e2800034054810080c0c01300c90741c6004044500030a50180420240b0b901e00070034081c2800380e185200041c5510744810441005051009c6c0c5200040440d000c42c9006142c014401100c3c0844055070205062000522450342c002441200f2036101030b00d61650307445080003114541c001d03508141c0c0180aa02e95152200d07070b0110b050000d6030410314510070113980e2028a03215408035452201d070080004000000324240301c0078403564681c080c02010400380440c880814090f4510b086110416007074024091109510a1850140841d03011003007140b5601031007403c1040d083d0543c018480c076800014154558503003410a0080b80d446000c640c0140070615403551210018001030303100c407100010f010600e0504102182c080e612a51100c0c4844e02c4220741280900707107c5049109510540c020088018160320040120201051440031a4189403d100d401c3c00d6060380810104802803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 722773120 1250 722771870 722771873
    0xb070309020a062f190b040b0108030403111302040909050a06111c090f020306010603091106160f03090f12150524012d0e09160e0a15021e010207 64
    0x191801040302c44502e030907411400c0c2400e4041c3c0303081107502500c00b06170706810f08141002a074850740d0380554454007100e4096a00c0f0280a60303030b80a2480b0141440d4544042641c490900b0104c061b44101001005842c0980740d0f10310001f91040d1410441c3c5940c06402080706005403845030f41c10a01c82050329a02c2c2511f50b542c2d508400d0280100303031701081d41e1181c0300020050b80c4070100c1e022a5020301524019a91000040c0082514010030784582418024100c1c403071401e94111050740000b007281202c41040c5486d100e40c81c09443c00200c082c031100d0100842e0401c44c0300003100c010b05419142172159001d61078502d040100c4616030341d0340301e4100b4061141c2040e01d055400c070b120a1400c040a10205003000407102640c2080c0d00f888120035110b40c03100b0400c410b0045108662160711254084213040050002070002103d40a114140005030000b001d403040f240c060502c600105a01001c503119403400101d400d00700c02c1c69000d64070850500d45503840a11600b2002141e005c02103007860307000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 722774370 1250 722773120 722773157
    0xb0307030c0e210106350c060a0302090a030b090d1205040506070c06140a0c0f090b0d0f24050901080a0c14030f0d050903011d100e03070b070309020a06 67
    0x9240d2402d00c48014900744500050f801d512250041014034000a16052101815101c10443c508600301c44010040320318541d140005503511a00c4000c0c243c98904212030320110300035044400c120b80d01c00241640040401d10700723210381c0e0050fa2000050700c1c0740c00c0385030005000114880d0760800d0b0a420305040001140f400f15001d54400c7c1c690410b80001281444d040004140a0b5441c507030b28103049041c0700491495910404410881d9143c02d85512007243e400d441d00e44c0e80388a03101441404201a0b0030078540c0e5000401000340199020480344c0e500420036003a4018202640641c0c0c40b107000c10401c51400d1400c450040c031102024060801458403880781c10005030140c00309160800c42c81603880d0b10300f00421080791250340140c0e0349a44c0d080e4001011a0702001800d4800d6091078a04d860a240078001c1603030000750b6600030045a50750030603c0c0003a042000319024280814001d00c07000c51414900180720f94120750700014074602034410451002c0f11a0803a00800c040040d80604040c0c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 722775620 1250 722774370 722774389
    0x6120a05100e030d111308032701050c01021206031e03030703200705150a1a0418021306050108010e0402010c020d150f051008031c0203070e09010b0307030c0e 70
    0x650049082e00045000501c0c5100308403010501c14680904a002a24070b040600782d8036428120044031256203100b0769949000d04000c0541c007040001126004200d041c224841c142c0060400d541410404c40d242c0782260043c0c4040b4402c0c4803200d04010443c50180040004100c0309a28030200340c000c20100c035603070f01000f005d0406042ea01c4203031a28171020819100182ca80c2240003030b60f51070003481c086484502520340455030581903008a13200100324020000b4501c1e001c01a01d2600c10750300200000780058041140900040d220303000c0150b120700d5104140b68910440c00300d12140341c58001803000e10141e0000310a60032140a020050303a000700303400f1045404840d80005280c440c10032042945260101c0001107142c45502c4052039000e4110610554540310000c90303081c0d0b91035590b500d91041414100c00d602c000f440380400cac07201d658003458002c441448c1400141007074601050000c002a00211a58a4080100202d05a00d03004541546c8940c2c0b501c2c0c0e5801c02e160000c15413405 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 722776870 1250 722775620 722775643
    0x1e06080f0a06020c010204050607240e15040620120c04050a050d0201030618060f0b040e070f020c030a0605040510060f18021306081006050a1202160f080306120a05 72
    0xc0d000121202078644c02d4056a010b040000c26242d901c0d1010318012038082130101c910001c94605280809844006108000b5182ca655020b4115400c1b0001c100e42c08940040c004c03a02140d07100d08400e91810790b07070281c11401003410111595062400324403600000001c00201680300c0800040c080b07922082440401c686017a955442041d40b14401a00034016070740000481c2c85c41d03070740880c0340c1c010f158000d41c00306c50322007041c00d004986456028205101e68001c050340303c410003000c114940c0c80341e091240c040c1d00c2481514810306c02d050010f03040400c041170a40394075859200f0f100a01400780400b46026179115030800005103000c01c1040d000801e0f00c0303800c1008191746028071140080c0c0d0125082c100010514102c5680c0712800500fa080c0d00f642e0039078070000145408903800b4081d10450b282400561900c101106000780148040d41c0006038100c00030000324250000074010300c0c1c01454036446041a140c4925142041c801c18803160041003e059114581400102c2e001150001484 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 722778120 1250 722776870 722776883
    0x200a0c0c0b0715020309120904020c0105100f2327090304031202012a02160e07080106020604050601051e18071b021c020406033507052e1e06080f0a 65
    0x512308440000c00034007480340340b6000781d404d0608110320401080c00e000306a420144420000d039844a0030744610f841801c18041615680d0007401c1150302d080800ca540e400c800f00020700c0c96185045c14840040c4007502c84400340c4d84041018030800803903129909105481d440200610804000040b0b00303030050111420b005644580f41050680c424086080c2d048502e4601c24000c43d40c5807862a00440200c0d40b601c00074241200100b6003500c04201103028a4001000f40380c140d081c2400c00a04040c030250030803074550240400150341d00c4960142c0d05a000c002805074162411701ca000d85400b801080f012015421034050304010b9560405a041075440013046181c6030341188007150040c070207900013502103891090200288034030000b80180400c032100350801c8004405000703c0103400380da0002446034001c4620b0b40a0160004200588040799010202108980f5603080c003c8a5080d00d000700f200c113101d041d40c003100489000d80c03802409280002c0002130103075240c807611001c1b03106004010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 722779370 1250 722778120 722778127
    0x3080708040503090d030509040506030115300605060102011109180a02040306060807081b0d02040504020d080429040803090904030e030106062001200a0c0c0b071502030912 76
    0x50200030003c1d00e6000001514084185c80c00c0d04003e810b039007040302000e110b0f6081c54002021401d041c0510303031603d001c0b5410240050300300000300c0300070180d292200342c2e101404081070301c20641403e10102c9842c09140001500d08041c000282510108000600038000800240b010360700d17420b262843d80d0048400700031490311040241006841a5400541640c1c1007071808221110702062002c00c0729007090458901d040401c038920b0050784407814295000c2c801948141c0035041903045164040d02c01844426070f40700c55039868109400c260081407261244940140920003c0f0441d84203031204e1030000da0030207150040329070303482c81980469802412a90302146c1054050442114805401802403201c5525218020322005001c01a803e0b2580c2c2c10100c492003480601c54016650540c4914020040c1da004400d4002d5119007088002c120003110050086481440464058000054a141d0714485400d104c0b190384201107c0c00400d503c1081841f00c548030000b03070031407003102001c2c11549 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 722780620 1250 722779370 722779373
    0x3150a151203091d0108100207060923010605041118010908010504060b01030507180b030613150602060702070e04171b01050a0609060501090311030c06070614060d0308070804 77
    0xc21110030381c4049058460440d4035070801d900f010544003034481c0310a58070303100c0412560071030311403d0a1080c0c0c07100307400c1103e0088000e404c0d070700148200c1c1d010751000320307101c411070b9114010025041c1030740104158040303125001000a0094500600c82107405203c498151f1a50100902c82d05440d0454601c00f64240000c6900404a410003071003050001c102903d490b04165000c0c00020030f40c80c1c0000d15100004441d10300030207955a500d1340c1c0000a0807040e040160380c4005900203801e1550007050400002020801801090100c149503441521900d2a00d08040c0c58254042c10070025074002c100d082c448041203907a00c030342c081c0c2c101101c0d03014032901412a81780c9210b003804981200201040d0004481c80c1500842d0180002c5031003000380b07581d64031080048031214040c2c5400210080402c0002c1140e50611b00f06142c0c00406070b40070048680e0006115a0001c43c00b01c0340f6544402a0034241d44d200e8201c3c0e54441070954401c00c1d4181169401803000f04000d0805007030100020100e030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 722781870 1250 722780620 722780651
    0x9150314070309020a05010809060a050703020412050307020f04091e080d140f010905090d0804020f0d0f11060a05070201050c0c03010c0c0501050c160312090f031d03150a 75
    0x44008034060554006810301100007009803802410a07401043e02c42c42c0010075500c54801a1b11400c1c25001409441d1554401c6202a2201074000d00c20507809000c0072480b4040c0070307001021144204011039444425105010100f005501400d00c04c920745002d61001c20780c00c00010544240c0e0720170300b88120b94a03180030326442c001c80940f01740f590724114a8450305040e00440d20301400009a2441c0c503683c4c0d0303042000070399000329019074039500320f90703058071140d8001d00441d0f030010b00c002d0411320400d105a0200d008030f0050603054881101c1841403a007441a614849510540c06880742d5241c01001000941180718000700203041000015541407408018884d540d080742c001002840380c050750410042548405040c03d40d0907510740004196451051760840380d0350504403050748141c091035203082d00c8410b108803d00e48000d80350040c14000900e10203541000c0c40c480c0d29041940207103980391240c2e40300b050301d0450003907000c00c0518445030084251540c1c0480002c4000c12210020041c49 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 722783120 1250 722781870 722781881
    0x1d01091205130b0f0318010c0e0d08041206021b03190c0204090218180109020f01180f0902030711060720071a031f0614130b071203050c040303091503 66
    0x59001c83d501249481041c40c0600086008502e060400c86d00c1c0a42c100596003203401e50b18001c008104000b24800c6c513814401d501181035802821000d00b01540c81c005c030450000c001000f140c02a50018024090300580c0310103501da0b01c03000c802503003840c0d10304100404000410101200740030101d81c038001150354582024480590280084807902c98030440345000650513940170303442c03c2040c3d41912220f58144104090a60000e01c40403088010f10019208001c810540c001c951003800000300e01001104034a100a0008400040c1d9a2510311401015441c441c0807200407500282c1c02d10400f194444640d10b40410400b00560001050b9032109203880c0d41c65010386140d1800b03208070204469504069846036400802c0320401c990031007031890f04012140180c1d0702040452004019054020b8090203104507101c40c03c071450b54035921440406c2e00046401c6808820b02e00c440c8110a40c140030701034101018603a040d0900f41540d4000e030901da0305015004041000103510044a840380c0c024 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 722784370 1250 722783120 722783129
    0x60c0206132010090302040b010302090f210a20010314070e0111070305060105090f101401030902150c0d050a0e01031505060301030b01081c080406020901020a0804091d0109120513 79
    0x8030000041440400390200e44c05201c00ea01c12807418503000f00d954028002c44800040040803503000e040e01108000c14001d00880c01101d0b44020480380b03212500402801001d90300480c5280c42c0015080051100d00c44504420390415082c030484462258500684039009541814440010845000100d5000305621803481c220b11401c840001400004180181a51803c0d100940940d45000345801d10711800d4501a0007856104004c001048070641908903091051601291075001b80d00003c2d0382480c58030700d1440080300014414640e020801c04068580b0890800c1d07410400030000282c441c3c0b500d100c0b8241850b458840b8400100d610111100c05000f00a1500e41c0340d503107074200882964802d003ea04114803610080e2100d110004035200e06003203d60740c450078107546590310040a03401c80f00b0301c28158407403182c0910000d00c003500944007510040400194108007040d103d00b0b070b209040c0c1414042d0b4036001d4034002041304041652800d800a00304070342d4a45415000260204d1035602 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 722785620 1250 722784370 722784379
    0xd06120c05010309171b010e01020f030103030804060f110309010e070806150117100305191113020705071e05010e0315071106090106051002031c200d0504060c02061320 74
    0x90103006e002904540904200407600200401090405000e081b0701c01d4041006c18200d040c0010800030b40300300c501a41c4103108030390200d0900d507504203403000d036000070071555051400802086460b642c01d200340210340c0e8a0400810300a89030902c82038840030054171180b141c0071404a84109a40240320f0a9501038002180040900d000121841403450301d0008442c02d0203003d10105034411000e02d49540c171600113000300304003072410303007042070302441c2c9030046240720703001d1200348085081403000500402412183e40c02000b140360071a1100c21281c2c00c070394144581c040e00c80c55546c4000450100038114150070f503400362924001600c18880c4000b586080388200020001c0b05c500c10b401c001d0850300e064410402401c14040160380301d00411074612104213040b003011400172040e8008072030142c0b8803821081d440640401e03055071913021403c000782644d1184180b2007007200f98810701042280900c0907000768141100c0822030f100c84000060015036041200f0702000102003016030501800a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 722786870 1250 722785620 722785627
    0xa0b0d0b010303020f060c03070c1103030c0d080115120b060c0d0225060507110415030309080601050d0503030f1b030a090506060109050a230409080d06120c0501030917 74
    0x1510002440003400203c0050154030100307015018005a030f05d018a801450550866507504803c407421720301035505480b4105040581300381924240002d010010418025014201c0100000f500041d0182c0c0100061104007044190b04e0754060861058103040d144042005401800015840d005184031100c890240d40c3c03880c41d00980001d0300700340b10410303030803000b4840241604d040b910002c24400c520205508100e4000060314500b028101c00100070400180300e0300240c01790194a502d034000f10f001c15075031581440b481c201042082e00414003141c2901240c0c00710390b1040d4882c0800f8042c101004006404070320ba03120b00820b84040030300e66004041d00e07803a0440f40c0c80080c0c10100b800782c0c1d00e4054a1f002c19000d5219802d8101612400b601d0025143c2c9040c880074140d80e5803040e0b690f064103c03170035420482da07120700903045104e0180c0e040c00d4403412060303001800c49650390b1040c03078030660039080c1f48009940402c600c3c089820908000500c440f441c00d060507010403c200c11030802a000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 722788120 1250 722786870 722786873
    0x204020f0d0c09050108011707030b070906110a0c0506070503070807080d0b040c21020f0a0e090f06010909021c090602040f14060d0b03030d0c0903031d0a05090a0b0d 73
    0xe00103841d4079a6092028464840260400e9540d11041d00541d4000b8030000300510288002a101d45480001c140445802c542d0b66124403c041c0700658200c4001180c00070100700743d542c450380c0600c210811001600744107050ba80d500d40320040340d02c41c80d802554041090b4060101c03d000752500a0780000c2c11036a0b9503040e10702180d1941c004c1d0f0610008900e8856009101e003894480c126141d00c4586591002c00d80361311501404c12000070740020700ba50200000b440c4003150401610160801c0e841e04500001440b08110a090000f0b05d5086291028410030400e40e13440b501060460b52602001030742c5084000002c19800d41c4000359104882c100641c003800c00060b54000e108560300041ca900185480e0801100209068404183d01000510801c1481d20385580551a1840000c01f228500801d014201080c0d0f44d40504031008126005800c1060541001c0301807038941d070f00c40190300114440746c0041c1c510702e0701e070003094050307841d50000482c000641d900840c001c500c0182034403643c0019 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 722789370 1250 722788120 722788147
    0xe01051012050c0d38040b04110d061706071b05060f041115220503070807080c0405012d09090f0c0e070503150303120a05060a06020309060d090f020402 67
    0xa88621880b05150450800e00318002c00500c10b080c41c00d06190105c1d418011103c040c24000302c540c1954071aa03944041c4215545620410000301c00e400006520741d941500203004485171913003c0303641d0140c0d800d5004510030f00446e407141e12442c00c2c1008803032010300080c2907403525903801c0c0041c6103110305014090790300c141500c04c61003503101341c2228206002207401d120f8600340c52410203070700f03140600500381d41e00e2010300d6410480c040c0c82ca40740041656240040d00d071078210360001c1c842d6041482c00f0310030ba0310103102c0e96180120030b450034051940360001600b000000c04a8108005200b070000d200e01c000d03102c100c1c0d4000c00d0030400034002d000c01401d02640078452410215040e291000c400612070b255401c200d0b1054000c0d0310344a0965540e200780010b29026a083c00b60700d070108009500b00c1e95004e036070342400f8103541000062185007207400e01c01e10750880e400810956009000d45009980c0360340443d4082410310001242c6a011783ca08285581c1c5c00880003513103d800890108441c81a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 722790620 1250 722789370 722789377
    0x1120203010b011e0815030a080307080603010b010806010513050402180f04050c0301050904111f02010c02060c0a1b080c0102121f05042301080606030c0a0e01051012050c 75
    0xc500800c01c1040000042d1960140500303058440b03103e250000c2c4425018041305a400b02c4880300d400a078062030800681080048501100d0b051000310501501c0c0c1c0d0f10017100c0e81c0c840c005a0080250880d400c0003e4503011000700b28504000000a103080c8490020041a0080c100a80150f40314030031110711200c0c8642c4c04a10500814540658446a1a25002d42801281c5403420f051840e42003406101242400400c03d642a01500b001000c442e00e85410a40d103181c0706140c070b880c141045100003400d448401d4202d07411540032809000c03482c40c115049a070814201d040251000b045440128071541c200c0501400520000c40c450000b803206400a06140c407091462840a603944203007241460080003031940b10706480704041c406820580e000b910601c0610101490103080c01c108180010700907005401150819400c0c0301c1d8608041000d9551010700b180c030021594200003c1203880981442000d01c5259110300b80402d80f805500b004009800b01071040c002460030314050318440c0d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 722791870 1250 722790620 722790623
    0x50106080c1329011e12110712110c060d0c08090a0503070b0c1c140603030a021c0513031202070b0a080412090503241006140d140112 59
    0x740855594500e2038403480b0311502c1c0b81408000d102643c424490405111201102080c144290741d855115409410321015a00300c149640e00604120445903802c2559240c07442c035501380d141070003c00001818468030b0418000c1514050b5504218400001c0c42c4c10031600d005a00000001100398000d03038036030040c03901707060f0b03d407a1788903251128007074241e40b035007219400341c0203401c18030030040080c4c41d0f40742d420303008178444c25890f06000d002c00c81c100d1020107a14000d207910303a50340c0500d0030a1311114100d5601c01703c2200a0f50802c041c54001035107e140040e00a051f1164a0342020700c1a4010b005440c0540c00f01c10b0460607841d00da140c00c84000382d0803d100400742c402c100300014003505078011911045015994242140c44583d0b40200381005100d1960a01c07202c100301040c80e071401c1190142c155041800c0d004007401c44500d81c40c040c1005017244090802d014030900529401041030000305025410095441848200240007040c5d0398034038000140000000043c001022500d00090300e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 722793120 1250 722791870 722791879
    0x1020304110a03050a0f0c0e01080102070c0506040b040b1b031b0615062b020a031a1813030309020604030c060e041406190e09060708010f0302031504030c050106080c 73
    0x1c0501010441c242d241848020256404810080d00242d0168200808540b1179605010810344588075810804c030300b608299056136022800c0c03414010f800c00c4010041600b621160b16081c24094070703040d184070364003481200c0300c1c000928000704191866110301b806007a0064949443c1d034054000d0040b440d04604c400140f00c0c00010071203110341103403202140700000b08018a00a0410700840b0004108460803003c00c0384802841003098142c0024807407514070340d40009648000350f00d0704201e0301e48001c2050082802c210707182d0b030301000071101c0d030b800c81020401103841c0d80c40d40c5412009070040c07100094210700b020400000b088401c1600c2d0064400e50389610707480201c00b80610040700e81032016110940d000e480401d803d410300a08400e03c203204c1c098010601c5450b500b00c2c4280342415101d40303440380d00402c02c01210302d07442001ca901509068054980051a50300000d07500c0580044007030500000c50042420140244060032005a00500034800190f40e540b2304e43e114280d08034203a004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 722794370 1250 722793120 722793143
    0x70f021f09150624440103110402031b070f021203120105010e060706060308030a060824070c0212011b05090d15091b030201020705010e01080402011416030201020304 73
    0x549540103100c259520700e001c4c0e030b00b040b0007461180e060045200c0c4150502c40e44142000c02c00c61581003001a1000c54040200014800b000610340c0805640198112a40300401880050f0f11800300d0001140c1c1241d000d81c5030380b030700004080b91060043c2c2c5403514000000c0d0060800c0446407100100600884618040f00700303109110751a48070307003a581c900e000c01c100018001580a130422420781940a00110b0078440941e4559007107030025001512040000b08c200a0103002c0c50103244050700c40c2e079003d04080d852241350b1041d01f90f4600c003660380080220f4005400180700d07613608091182c00411807100514030400d094002d03c8100703900d0100c00102c0c0000402d49018404030b60f0101d40281c106000c103151511680c02406a1003c14020681c59120b0600403881048941884040d841a00c103c00da20710b00c000383c540003150388054180442008214040d03070304085296405038080c248028015070520000100340b03e0209110003040721a4014414150705501451180f0301c5207203401d2030f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 722795620 1250 722794370 722794403
    0x30b030d0908062d220b0f0601090807031106070c060507030201050c160611090405070215091f090f0c09020a08150d0f1e0f0201021014070f021f09 65
    0x21510500711543d41c1038003030100c65142c181113441c0250320100000340c90469440c81401c030f040300b110006040d102908003009001c50701d010086402e801440900700004c011345018030082e01c0c1d0f8507903c0054640700440c03e0000790741e242c6030101c50810342e00030f158030340c07960b121030000c4c10700d80100c0420360066113400c2c00603144481c000112a51500b0155401450324601e84d80c841c060310030101c0711659802c0038803800d180740c0c03140d00407203009081580240c03141c031000004049041d00002d005400320390012141003403011000c95003d41130380d20310802041301c3c041030030048040101102d0040c80d0545003440000c000c11190f000c5d00b564001c03a41d4103961506c0741031001c0e2908083c0180030350700420801d0200e0010f100100f00001c201e00c6000749100500d42d40801006607038150005035400b1030501d00303503021583d0500a908809080b65001c103d02500c402d10780824180050003007013070103007130340101c90351074000c12487c0c807107050079110041b0241e1104e00020203001d10744011030b86400804030707114 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 722796870 1250 722795620 722795641
    0x611073909020d06180b01120b010503070f180306060906140a0e041403040603050a0e0609060f07020106091803030b150f0702040e06070e030c010306081c030b030d090806 75
    0x4010100065210340c149920380c00290722061041c928203569420020303046076444c4500070048001d50000506410490003d00b2140c1c2d064444001d1914000c490b103602c0e80c00000f0b403a00440785181c003900003c9000c1007070701d0200592190494030b02d10405c0010421415400035425a040c40c1d20500c282c560790368070501030400d031310081c82d40302682c21024405002c0d00d0300e42c1984140601c3d10241441e68a07000c59013141d10070781003540080c1d142e9082003001c98003402174035024001c0c1d400401741498000c092075117408000e0002c95000909202203a03500f071007504040c0c050300340a50100b04651130040c0002c1a1200c1d55800c601203824441502068513100c6c40781c000300d61010700c2581c40e00c0c128a410380303031a61015030101c0e8131035912820810300503420010180300f02d04644500e5040c80c6214201450955a00b9070705040500303000e01480880c2c030200720901c000741d1b0440014084c549255003034003d4090042c005030144111a044500c803903004c1111030840301c0440075111280c50b00500074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 722798120 1250 722796870 722796953
    0x3020f0114071e0c14192105030c07060206040209010b07122d03051b03010b0702041107052409060c031302130c0309020316120f061107 60
    0x30701c81620700380030031008511504042c0501c004514500c03490000b0981c0d035040003410540040d808640d802070f005d00b031400d00400c40101ca446031411040e00c1e0b49450030140c0105c07080c07050b140701151041c0d03035901082020015540e0601160f41940d550702c3c1c546100170b690318022201a80f04149803000002c1802070181211603071340d041103c944003014150300030b13120404a0507090000700241401210b1032000003002000c2da8030565400b2429013032602442c0c3c05401d003407002801124081004128a11070704086854169058801040c01154148242c195004000001d4218000c1e0f1007400f00c0302c103440d0b60f60145240d582d8401034442d00c421080d80d40e1403100302c0305542d0400080011030704003803141520b001340b0f13440100402c4002881480c19803d45a10802c044003082c0c84014030403c615092007984040e10703c440c00c04014920b00751180d20b00840e41e04002d0300b41404601c0f1403003840340b0340c7c205083c03010100014540c0c5800700d2400081d100001555154112446000110240c010a010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 722799370 1250 722798120 722798147
    0x409020a2d110705041b021c08130809040207050c120609060114192603030f06150412080d0b031b0402030903160f0605060303041a07030302070209040c03020f01 71
    0x6294031140d8181c001c0c1c1c0d020180541440790762040c40c500013402c0d43c0da8000c1c541d0300c0c2010310741160780302c59204010f8507054456003042d00c5401c03d4880c659196a0210348160712100668021124000906041e04184246034446810074000034411050050018001c94010b8095400912070074900902c0380d150981594000090b802c10f000402c05040601e070080c4034070000421480480d01070040f800d00318421039128001408003040340b2111082c44000d40c2a1010002c00610300e903180030000e04103e084000d000601c10200c140c407654525100c1e02c262400303803a0898403003404126500f048406500444102c5071200e082c030300094602d040100303e1000c1501c8000e064a0300c01d9000301044040c0d0001080700e602c9200c01d014903089001d07e0200681c40500030706417454811818185a02510070040a09000c5d910400040151120f041d8174000c00401d02c800c6551a5404d501e002c80191083c4680a5130080c1c4010038002030081c8003081c04100c0340f080391601d441c81301c10b10040d50aa40c4070050b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 722800620 1250 722799370 722799437
    0xa080a17070b0408071a0f01080607020f07090c020f0f0c1e03030a0e011b0c0305070b090604091509060308030f010e0c0f1623100b1e04110409020a 65
    0x401e0000e8100c402034400c02e0b114000d28030841b40340070290352015004540d0450f420b210000104035500c0309014440c0c1210301c51000c0c0c444003010703900b101c1d510b00591040091880d0f950040c0c8401c1d43c0b00303224a22880f40d0510644030f19a05460b02c03e070362600741c1d4801d1881011440c040045099a400e03511010b1070001d4040c40c04c09818950580b02c2c400c41d0000c4a0501802d000054604240031140b00d10091080c42880c0030030381941462454450650041d01c1000300410020025a071914169400c49c0d803880d8000c110b60443c141b0400c540c0c11580e00c8503002606101d0301200300206035010310710415154486940311780e44c61001c0301d603d01003951403071882c42c8100011202c00d0404030081024240403060004003481e5662481540c1200890302c480b640c5400141e41d094000c03d100e440d00000b170305d1700e0a019858940380000c0201852021580a42e00c41c4030002a0549443e0405007604032454103d540b21079446800c00c01941c01302d0b0751400002c1300d1181c2e03001808806030030b02070f401140e0034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 722801870 1250 722800620 722800643
    0x111040e07080402010e0307080d140a080f0a0204150f030b03070302101206180b1903052e0f020903190c1e080f0307110306070f030216020a080a1707 66
    0x1075041e40d101c0c1d00500142e0400000039510066038800b0844000100200ba0040290b12044100100645007500070214180020400c505000b584030350032070381000c50500c0b03100d1140c9401c581c01c002440342da44004040b100c5c0034181e4504582020541c0d8601d803103901d041c8400ca401d02c0825441e461940002940601d10003c25081c0b90b10034014a0423112005000045031615407101e140c00b0721520384841d11041c1c68a18410722800c12140c07050500030a4900260722a0a5030b99950722030040000140000c808055100d243c035806091807411a81c1103402040100c1c000b0740705402079807081648901a00c81c0c074801702081c5840118002d015500554122503403410070480b0a0700c500111304550840055207008036040100740044100509500c00079a90b4100914194440002900c00c481c400d070410410880c050740c004070b502c02c0701d440e14900140d8031b081c040800c5085505024000c0d402014440000c00e17903080005030060341c54000d80f506403120713060144104c0301c2c3c4079085000b4182c05c0d868 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 722803120 1250 722801870 722801881
    0xe090901051023060408030702040b060f04060302070809091602160e04060c030e070b030105100c0201050d0b041e050901110405060409050a020409051608010e061c05030712050a020111040e 83
    0x1035012100c3c642d01c11160007120b0545400040b0f403030308107801806407074000140c074504501c0c081c4581b0484420035640c2a040494170145035215018610501e818150006014000c11007040102c0d4103210300144032120360705014151035242040486500f015108410410030440c2c3d068110340200c40121000b0b041c15900c541d0345c00003405007404032005050b19507100c1540c0d01828081c08001d0017111100f80c4c0c90750f2522003049030404068032030100303222107848410003507684482191000703105c03140085442c00440000c5001401300c8181e0b000c20705510707a20600e0b00301071600181c0c0034000744802813008250340c00c00301c1c0d01407140380b03d406e80c841410001000140507a4100e9a442120b1481c01814641c0e00ca041c00141d4404036906035000c0b4418040078559034000f600140901709007000c1e410285410000305d20a04020032607416201180c425030010004200210384540ea400081100380501e904030140c0140c01080a0502550a005020f80c8140d424800d50b000c0300d4200001c240d2503101c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 722804370 1250 722803120 722803139
    0x8090a020d02132d0204050607141c02010b03100b0108180f010513020913030e060c030c01020a09150c05060a0b0f1504080d0503010f330e0909010510 66
    0x81200300d070080c2c40f1044584481c2d00c1d510641030b01c01c0c83c000c9400d80c03041d05044042c5202544142d1016002d1050000f0300c41c4e078499409031360300c2c240d00c0602150900404042c0515100c50003605000e00368480e890706480603819000003402030707029012100d00034600d031004400e031110100c141d0300161252f80000c00400f61580d402c280b0854160507501185d1001031980d003592005c0f5592054003020140050450078560300302035020340c131a0004565500306039001460100440707001441198003040000060405000700d980c4602401c0003156035001000d00501f2100c868420805010321115000108074000e02d004200194043c0281100d541c920580d000241525411036801564a0481540c1503c8100c240500c144070740c1c6050b5211885c01c05680d10709141180d5074001c12200b480100242684010701000f42d0300064003e4010042d400d41950f035640c40c1203000303112100691100855240c02000a001582080d1458003580c0c2c0c518122500386e131020390b403c821400401c4000c0224050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 722805620 1250 722804370 722804389
    0x103050606101701030305091809060109020c0f160f050d080702010309060902060a090e06030a0807080904021608251104110c0307050601170106030305070609030c06020c0609010c08090a02 83
    0x2050b0500140c0d00b91400040007203c48244c0044005c2030000402644615080c003000c6800d40101c80650071524061aa01e0f0301c2e04c10600c0f0342c9100e25004100507414070001d2100b00c2c070314205402181c000140c0407007040c440c01e0f80c901c12107070b9806190101080d50f0800c0e41e0550601504101c910340303056a01c1d801107000f80b01054040d207241e0343d20a0300d070b00165216002094184a00c0c2c0d103ca00c504d082ca100c0c0c2c106c80c030340544100d00c03990201844400040750309042e90102a041013645480e40c0038100800c02910640304d144032482d0058a00780104000c0760041c0c0103262101118410301412140701d8500d044104d40e01070241032001040601c9032601c0e030050b00800041200311410545400b20342480d40d082140100c13a0f0f50000030041c8116003140240c010018420741c02130003c5071560714040c04500c56004050701664444d20f05000385070141080e15a220f9001e201150380c0c0648440c4541c0341c0105030380b1100c0039420038503040200343c03040c0c0300c00d4040d03030152005c3d050404860b82041803000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 722806870 1250 722805620 722805649
    0xf1204020406030c080604020307150c06020711060c0a050c010c2f1e01170c0a1209080706091a090d030905100e01090b0702011b0e06090909010c1202030103050606 72
    0x60b141c0401000143d020b1500400600c0705070001c100318241841054103060942c1c00140d02e14103218001c240341c0e84e006c0400d01d01581c1021b001640c4058500307204406101c641c0b0201d800000015841d100b2a9002030b0820495005038251540a22400c00440320030120580c068884140300c035545c6401c0d89002d02d90802048980052074000481c4000306400e0404400d803940600d00030704d40d80007a560803180060543c1c114514181041c50090801c3c1c0448c010703491503a0070003580780c1210713000240310b0340080500e640143c010742c0c580103286009009807101040844d01100c0c071001000c1040307407000e8514000d407900ba010f403560010604040f40100b007181d100340c5052040414031640c1c001288135510b92000c0c8200080369103019824058090b200140c925021689040034003255050b1903078009500c11040d1500d203641031034000002c0e00c0b84c000e039003101d81c3c03000221090140161056000c41c12b52116500c034007840d801181800e100300d000910010785140c00280004655280048120100b007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 722808120 1250 722806870 722806879
    0x120c120b01021c0e040b0105031909022e030b010302130e0a0609060f060905220b12011b090611120f0403170702040b0904050a1202071d0118020f120402 67
    0x1070840c40d19030207503d240c01c40944082062440b0750340e120f09042c081d144403d007080c2402d03455030600700652010725100440302c148540d6515491401c6680d84402984441c012048035802680d060700020500040c070050b0601091410490f4000ca501038002e0707664240030a00b80e4845189032841000824174001e10201e041e5550300d10118050b0035921900c400b400d040c11091815a0030b1143c040d00025103500f2062107100610000c012800040d030304c000f042d400d441c0000c94460320000108041c6c10b240340c1c0b9441d0039401c0003030320000400d0042d20380030020b41694401c0442c1e680c03140f0549100100c0a02400c1c1030300042c030040c2e068840d01001f032045e918101d028a10786036880c0c440241d0490211031107240824005141029450301d070203980a1034200b2160003900c0d0a15940f655502c8058100007401d07010f050901b02c4d1a0703070007071110000418200c004187d61205200301181780b99424025501800c8035540003036090b095901c00d580307000e8203140c980c0303180c40c2421102c405058001070049911 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 722809370 1250 722808120 722808133
    0xa0f021903020d050a061206020c0a080307030e061803040b09300d1d09070c050715080a052a16080a0816080105011b1703010303120c120b0102 63
    0x50384808111a408a9641c006071981c0030140014240e420103010010805d04000c0280710300407110440c5a9074550000e001603507003294010303403818000c50050290030302030080704000b11b03075805030440c85d11700c144501941c07140c3e500da09010030843d0064102d402c0d0303a8011711003480801d442c4001000f80402c010b100c1c41c0d05111740e40240d081d885c005400c40d013004441600c080400b10040040200b003501c2401c0c0801080307070184804c3d1242c1803249500f88100002804117498138090600c006415402c541070b541343d0b5840e1a102840e100c004129000082e00400029043c000280314880c0641d8180d01c8841c148002009500c0f129082d054901c030136010204220507039241448000c0000340d1050ba0082c0e11180480c80142c0108001000d16904072003a03c49002280e910404040c150b0f80d09081c03111055003800c030340e0f101d403c0c201c0d0300044c007006c004807005030304c59200300145048038030a503101c2c1c0c0b4811690b01c0c480b066035041998100030030610981c001c0b009180b80c0111201d04410b1040310403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 722810620 1250 722809370 722809387
    0x70f0513050a0914010909030e130b12013c0915090507150201020a1403150307030f020306060a0e0412170f010906050301020a050708071b3005060a0f02 67
    0xb044030940c00100c080f9500c00400d0000c8008a000a004100c41041080104803680b40a401c1d201c20b000210310522865801102e19542c49d80205098100640b000740210049450103000340b003181132000b03108140e45444a00c00c13076180b08007460b01c1034000b0032040c4406240006000340c0120401210390350054030052034003900760320031038046d18008d41c01001b81e20301d8140ca24030b111800b0b40b041c50071a40108000090385401a4103d000310500c0b503002c030342c1c9582c0c000301540020840d514099040c020702600105100741d034907000000c580214156151a01c401e0100160b401e07561194410000584000401150021580c800041244e0403c0600011a80d1130118405e4080b074030310700d245080300c00521080c2090b20540e80984800d40003189099000000039043d4082c07080001c1950718001070039010000049521103030001c034188900815070b00e40464100d03d10310296034000452201d42d4001c403252005c00c035900707041d8000c80504026101c0952450180030064804440c4503000c00c40880e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 722811870 1250 722810620 722810629
    0x61b0905060307033806030f180102090d06151d04121b030305041109100b07020a0911071401020a09060e0103060807080304171c120f0203042108070f051305 69
    0x311748142440d02080c03a03410000794414007220612103406483c06000708406940002c06440d0001001d01010300450100c1e800d00d8064860b080920740c004503400500f0040180d160801c1e4011500802e0b001220760f01c510f80700c0d40f01c00c21680d07200080038481000c9408500c2084c603615081405181101568041c030020610050a61404900007582c130b8042000b403000010003442c01c4901156104518202101c03081343c20005c81c01500c14000c00018030804654890340e50310010a0800c0081c40700a00c06100d040054000420540380e007800c2c0020140c1002040c42101c0381c06249031150b030191401d00f0b80840300503514001c0941415030740d45d0046403c460411000004115807001503a40380d040c0012074110030f000e40451300880e40403174035144030381094403a520696411031924441c079240da100e12802030a030740c0001040491000003403200380644a9840c411180d8059403400750440b1400048911030307400c8481c00300140109000e20300d41481038000b00044015280765001813519000040e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 722813120 1250 722811870 722811911
    0xa020105220b190e0405070815030a0b0a060e0a0209030d0509040216140d0e0306040807170a0825080103110f0406090213050114120a14090703061b090506030703 71
    0x1104010540f1198040300c43c1d01400580b259542030f40c0078403031803c1520018100c03002c041c1c030480703a400700182c080d44c440d00d00300510206541c020104d030f10103003804c1a10170010022800b070f00c00b80f0001040083d084900f80c1c004c642894030007800400c0031700d21190003100c40350800000d46a1107034003045042e50f0001074a00c00d00c03005000e0003c4440c1e400e1402ba00d246800c0000f0f044106015803c20513a6181da00450b405a01a800031240d60341c61985107005000c0c002d010b0703080d4541034008100d102d80c1e02d0740a080c103403007803041e50303444003440c82954000010f1180c00e13014500012a40e50060001611031617407201c215801512402c0d600d15510001003d94419400c900c0c4060303804154241046c00300070010b401890203003415400303140059254070345031007401c4030140034407000c038040b5010103c964800b002c070320240c1c002040c20b418500001d41d200c2030307540310035178080342809541c0400c00c0c91604110303036211b0381e51108950380d8178110502010707400080122060540c1c1d4034a2071644e081c02d0415 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 722814370 1250 722813120 722813137
    0xf0a02091815040b09040f0201050f04030302070e0a06030b18070b07030e040f050903070b06062b060609062708120705010f02040b0f030405010915021305030a020105220b 75
    0x4201440c5054603489030803407030540920780f08608101004406485002149401c00c0d00160b11050a0855000681c0c4030711903801016210f1000090004c145980450011f0a641c1100b2100d03916844210025003955141d0001030301e220031520200300055140302901c00307800c1b03411058a80c616903500e401c1c58075401544d0150085660a0360b1001c0d2840c0910542c020f0048840c0c04014a0038200c207040d40d2401003020041601d403441001c07460b280e4400301a9209004c50702901064004a00c44041c142000e0358608546a410890040740c043e01807050f400669219039100c1004070100e00b41844041e40c0000242d41c61100c055020803111030034040841050344401c1050340c0c0700c2152909500712601e4009020300315106100074070881a01c0030840b80c40c103607011201ca440381c0301c0342802ea004003c4042c000340038011004000500b0021a00685260600300c0008107a2a40c2c49040c0740e283c003110500240050010803590b00c00c108000c0300c5d00030707407500120350130490b030b4880000700041d5000703485 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 722815620 1250 722814370 722814409
    0x203041e11031e07120b04020907030906020304080702043909150503040512160f0203030c012919090908040e0907090509031e1606050406050906130b0f0a0209 70
    0xf46460054000c001c200020000046071800050498a075040341e03c2020300002d103c1e020b82400708030341138881d40118012603004803007150b80e400e10345400019680042003c0380564208502403421004038480c1c52001c40da04d40c03081c413032009030140f080d8642d9440e8000c001030200322000404d000c918680c03250f24010307090301c40c0d90352401d080c14601e00d404055480700713602d80c40400040640d86e01800d03009038496408180402d40c182140300003402e5015441c003070000da40c03901501e41c504180b5021107024190410205030304092400302402010030340703403100070140c01c06a1010018086541e00c000c041600440030641003a03194008520407032001c0e5000703d0f0b42d60010700280003c0c0568400e280c0c1001400000758079040345465100b000140d2080d00f0b010703611000ca44040042c0790f52940d01452039018a0130846450070b4609032004010558001841d48070b0080000c000c0b001140c42d060103143c105003981580d0f030f948810b424190740c001f040a80c60f540c081c016038019444620000e07684004414 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 722816870 1250 722815620 722815663
    0x180c0609030a141e03131401050d0c02060a0b0307030c0e0703020403020d0326010806040f03020c040f0f060807060c0b0907033302090d08090a031e03120203041e1103 73
    0x11001310420a1400003540700e03041080440303803121100880c103003110348403540e200f80c507850800140e416000e960701d80b0190354100040010380340d0380030540501c90103070031208101d602c04280034556145260b000050990b40d1003901032203400700c41c51849030320032420f15000d0303d03198507030380820562404008102c1c003095080b0111416400c111103000440c10700720010303036020342c07411f00c819507a1140584040e11036007c4100d640203051091001e540520720140003070040052403020000101000600d10000510b002d201082c49000410b902040310361640d100402c103161a00c070020351400241c20b00e505d0b40b03d40100000002d8002c40407010440b41a8101032513454012038980745800004070282d401881000408c0aa50790700780060405900b10060070344490080c40400c5a030146504082e281a180e60070f4074291085c91110b00d05e42c28460b54170414400c01c500c2d11803090303000c01da030300a092000240244d200401840760b07039402540180010940b150301d0002003410030500ca14013a025a10a6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 722818120 1250 722816870 722816893
    0x905070806040b090a03091e080f0c180403092102040504030528020712060e0609030a1b02060405060306060706150914162d0206060108180c0609030a14 67
    0xa003c89621420100181600b141150b4005102d20a80d00621040041c1c111502c540032030400241000f030042c010403103000040c982e009175034425507088811300c14582c551100e400701001c4002180126410f407121812107040002081d4110703694089041101400c0054502607034413409103600440c000c9c1c4629641b99152800c010441d051071075900d00c42c120100d2441034032540003868004440400d00080407801540c6003500103000710042c26016803050200b80720340f04c50040024102c0c03c1c400d40b04e0b44c0c000c40200e001d40c40302c40c1030444040d5100c1400e100801060802c04011a403003500100641d180c000280e4800c1c0446181c031101d4205d8440c001401d0041c9038180c420500150100030000d209403904000c0f600f168072640100401300001c8650222450041510781905101c1040c0d800021769400d9200966881e4201d5450340010410008614060b444a4901c18400003800140484000d400180200382d40510801601442040c0706880403c41120304220840c1400d005081c0305500c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 722819370 1250 722818120 722818133
    0x3010303090e061003110c0115061e120c14030a0905120f090618030d020d020d08090d0806030304090603061d0114070e1f03021b19060f090507080604 66
    0x7580142201c42100d1040c420965903103040c180d05000b0600d03011444088400c2c1180c1c3c540211644242c83e5070800d151201f04004122a000681c2c41c10f55510054041d61700030050740301a02c510100201d80b0403006c110004003603400c5655000c02e5130801000c1e400140c558016141d00c121303075145100d540c07080d0884c1005000c0c400700c943c400010083c0d6040444070320703c004a0b4400c0c450100e03c25400018541464082c8843c04071400e807004003950800d00201d400a51580c1840790400c005004401c0b500040c42e0140e0907103406130038154010840b0040c142da0940d84d10744007422301d070790604c0284130008181090307004540103140300340400f003001d110180c00400b034140c2d2000f90140e9a410b01104105030307000301ea000faa01031402c0c5040e4581d603804c9004108407185030901042c00400400e00b4803845a0141c0007480c08001003401c0340b00240000e01900d40350800e40d801c41003070f1451309000e01c01040a40e044010f45440004000444c94a150350741407a281c02070b4440010f6400100400080c09003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 722820620 1250 722819370 722819387
    0x191e0206070e0415031a041a16030c140c01020711030606011719180210081b090103020c01020a0c03090905010f1802070212070f050105120c07020d0606030803010303 73
    0x150000309501d0920050141c4201001050315004550700d60701c07020041102240d6400441c1c00250b40c504400381c2c02800100d142c002c0750281c070685440c03417440c0007a912600314240f2460008203440c1105140702801c5000d40030364003d0300100001134002e202d25a441034001c0c5114a003400c001a81d8403070928258012100442c030725841317604100c04011490f40c11085030a1100406203400100307a941282580310809801c40d605840c6180001505100342c10744545100c803070003283c14510224204000b102d00000803210541074105840d08541c03034001cad050252100c0c0d0814140582058001c3c8d82090890b008800000000703620a91450180368024007282d0160a91080038000f0751305045040000300454494042603001201a0103070103080f03075060365240c1307034010415040a0120306400340c0d568128003503582d650203004d00000e641d41c011803c41d090004402031001d03003a07403a038a40311850740003031b4400ea03008512584048001141485032902031441080c4103600ca5040d420020301200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 722821870 1250 722820620 722820677
    0x10609050114090901061b080301030b01030b0609090a0210030e0312040c050111070605070609150506011e0c0f2102150604060b160303110c031b0123090319 69
    0x4000b00f20079001038541c21041d038113440341800c0008190b0b14180e540400c020b075281c2c1c00340000385c0100000c420041c5130f00c034003030407070340259502c04994036180d0400002d0382094804600560203815807030014145a000d0541d00045030134000754510303e5a000c2d0b81950b005000e04298030541e10108402c0004808410014244c00c0ca81041e403c503014403159601d001d64080c8405002c8003040180c10451150021402c4592003082c1d5411000380c2c40c2104d010b030405842403800301d11442c030f429040040004041180303030125070b2555220380b119210f405203c5d540d04d074140c0d0201c0c00c01320107440100695054460b001081d46c01403c9042c20b001d800c01d42800302601c0d8503c2203080c05010081c141d1034100344c1d214650982c03421050f003011351405900608611040703d61401010840003115903012000d01070349031030940c000c00c1e20388035181c0050032200302042d002028150580342d4000f020114071140e9108103244103c900d000ca0381c0341c5900300395031500841c0c8001035200f0084002d000d5100b59018154 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 722823120 1250 722821870 722821907
    0x408061012021c050c0d060b240403080708090301020a12050f0717070c200406120b0c0304060216060e0c041a040b130c0201021b03040806060909150106090501 70
    0x2800603800a150b0f840c40000340e1101001d41c400c0442404000d00c52a00c020301c0013003880301d4514287c07405102a00c080750380d0901c20301d40c14001080301c114500311010400905002d052800341107070b40c0c424064010340000c0d240b0400c00d014010070f80d10700f44014010040c40d51150102c040d0301c84068825100c000385038131842000d041c1401034264028003000041006034009450799585c02408031031401840c1005003900d00640c4002c20f0907201412520000881641c040c8a05511404900301090324250024030780c0d0003100001d1303034040481026680061003040098a4541d045251806102507010140c4910382e44008541a540c400c001c0da0f400a00c00390b405010703840c801c10710300d4450403040c0103a070b000b10b0305c40600386600da5070503d03c01e006e051040700800200c14803560081c001d4014040c0c01144140c0f04c10440400c00000058030122200e5500070701c695501d030800e0241e2060083c00300ca140384980c041c1075500c281c0c03441c81a4080e100d59525052401e2400c800141140d44141031403949 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 722824370 1250 722823120 722823149
    0x9150b07020609010305180a0305211306090c09020c0714010f020a030e15040b0d2d1802030a050124051c020a081204030c17190809030304080610 64
    0x5840c2c01c0c05a6050200909002070300780d84040a0354500710003031030100a14015980501c0c20560800080d08104040185449901071001c0c01c5407501c19054035092103c440020149000a0094000c0603a15116514050500355203142000c1a41c000c1101525140c000140a0084003030504604150100900c0d20b18003860352501c01a444002c101400340c10840400c454501a07210401070300f0b18140b141c40010f5072035175a8401c080c015000092101c00007030400610044604c8540752080149054802000c01880f030114410000c1c6650003031032f410740400184100140e41d080c400071440300d0140c000842c588401c2404069040043d4a0500399032205440a00c100d4071101c003107552880c801c8010441480c040e00000e00c1b001055031001a03103210b0103503641e00c41481000940102c0b441811811400c58540d01400880180603403000b89913030028000400e040c039030b14000c20806004032103240c0b51206d03107404241940d0082d001720b0203d90200c4180468004103500200090241c600d01d0442d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 722825620 1250 722824370 722824373
    0xe0c100e011e1205220f020a0f030b2208220501140a081e090a0b100b18131a0901150c140705030d08040218010605040504180602030109150b07 63
    0x22041d40f000f00000d0b081d5580c0300140b04003102c40752481540c4029a4000c10000c910b117010f44650b42d4040c001c80c0500503043c80012030041d0041080152944450341ca034860f5502c4200b4440386482d500d0351055605404032000100b90404001d00d01052001003880d00d2520000c0d6120410540d6840141040783caa0b140217a01018102038441c1c0c1d204510346501c2d140c5070005020601c0c83c4044004405ca43c0060501c0380c0d118001a1003941e10b449140080071550f02d000410101200c640b14901078240c040142d0f0301d10311141c22400b890f00718010440541c0700b41c010b10718000c60760034407100c28601c0e15540c440d03140ca02d0300030382c01801411400003070821002820742c000c001c100c0080c0010256102100300c0c010044061003140003510001c0c0448840c04000e400c0102034240680341640940750f5440056541255100da06060300d020b13445081c83d241c0b40c8002c3c0002420455504280c203803100300d330680080c065000450003800c40314400305044405a07201400c40d0034543c0701d000c3c1d44104110010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 722826870 1250 722825620 722825627
    0x13050904061b0221130b0301140307090e06061002031606050601200c210a080703030e03070f0b09100e0706090b0304120318050f010f0c0c050a02040e0c100e011e 71
    0x20303040360103844c2803502c0b01088401c80841c440c0e0303a0000d03200c420002c0008103443e201803030680e40510b8201c5c220b03885941d030380010b1001c40d100c00305041e095401250008456080108040409070181d204583c500500c180404840741d0000304116220b81d191030601106691154402c6040080c203022200b00341d840c00744803665068613250981c01842c0181c8414100d4450250140003201054141c0e005513805103040381081d44117403400c401080c50002c10303514041c4004207503540030340c1c03085020300341480c0e980b01e1a4822000400804491103400400c00080d1a5800b91440030400c086c02000180e04102024050030815080300d0501c00d800d0040001203450991000c6071000a82400a9400060660030030f0042e04000e0242080c49880054944403a0540c40b0a503400e01520b03041007001611402110a010b62000103001c030381c0704480c000007502d803692001c07404041306022070390010001c002049081c2240002400411010f504087d0301c1c2d60044294aa152107044509110450494015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 722828120 1250 722826870 722826913
    0xc0f0306150a03050d030506011803051905100c09030c050d080f030402011224350307060c05030106020105090105010501050d15180209040605091b13050904061b02 72
    0x14021026584401070903101c06a445000c0d40e084030036036812403040c00010300585000c0d03403200e00150304164519060b8502e0909482506d902002411550380c084905850315012000e044d42d0034080c0e45140f06161816201e40e03661068542c07181c031050342c40c5080c0b054200e0310340d0307004500602c038040481d40010705020031111101462100141c6a454600040b1412007140100078051890b1000c000c109280d0502050444071004080340040c035142c0c4600c442e00014421405105001c0441c2205000306029965003001c401100312424600316803110b00079148044140b00100320000b0043c40499828003039160b1148403540244440d5240c600001c0c81071040310a0458183e96800c842812031005905850003040c40d03100341c10940d206100810002d500c600e0406114501c1c00000150b40c1c100418075a200e8822448429030403808115100c105070b2102c50707400422000404081281c1e42d80891075401580982400100c42d0424003920076108260352900b8159441075082d0184032f88a0b5446 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 722829370 1250 722828120 722828131
    0xc04050615030f090a02100302090f0a0803090103020f07020904060219020a0c0501050d090b270109020a060813240507170402010f050405030708011515081f0e040506090c0f0306 78
    0x440951340e107084990518401110083d407000413440034800340780d41a0062701d000c50301140c9020b0301611000030440c10780124420200142c0062001700c4041d8002d07800780446a16603001303585400c400b0782c006041c207402128201c90702036000c41c0504440e040c1e0380d0344c820302d48501e0000b0031180056494a4082d07800e64450340d8104200011102d20000558014106456018a2545007403d044842c20f0320440ea00100b039030344d04504c541001c0343c6031050203004c0074140c0107000141c6550400744125407240008001c200007030010103150000a07405603c003a0703d001000e030590800c98002d0241d03000d44a001d403c0b2000c20800041c2d1010301aa0b000c0784603040784d42402c114628a01c8058103031124021031740850b5140c02181400940c03481d042d00000000326050460044090300c407a051040c402c501e084c001d00040444000032507000300c070401a49030a0802c001d040045584010000d441d603000c80b000c80b41500004140541d003e0300300824070200ba41240c0c40b68442c085000401d0382c0c0d9030001c20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 722830620 1250 722829370 722829391
    0xa051501030f1211010509070e060a23011e020a0b160e21070e01050a060f1409031612060b030c0d02040506040b030d021513031407030315080c0405061503 68
    0xb1903540141c409032003807107090000388120316015007215200c60003440361004902702c0000066403840c10711030754401c5d1040411380f2403c0a800034006034041d854900782c1410b1110805d8003124614840c0c448500b2814560b00610b91445941703020300714803102038812a81019241c15487c610f90b0000203094100320247d4403c001c2c85c00c004015000f05405080340d402c0c4c1d0044542c0400d2581100b100c880c1038500c181c1e4000402a07440ca0101c1d0820340005c06800001e41040d948a00d040d42d07a070050109600040841d2040640c0780003a01c6510140e5110b680c4d9a40100000d0b03040058600a05410344d000310082d104200505022a65180d90a42e00034801d40d901c00000701c00da56035034410a00038201500300c507904015031002035550204800a8045036590a000404400780503c2003515950305550303001101c10410003038075a43e00507440490038161610a100a00c02020118900426901005000c1080d540e02403104862010b80310b00e004095038000c0c4095a0222011203410548800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 722831870 1250 722830620 722830643
    0xc050f0703320d1a01020c0d03030f060b09030c0108091f1b17010e16140c010f0609061d0c0c07090c0503010f050603100e13060207050a051501030f 65
    0x1200a04141d14000c200595081c46040d4840c180d10190701511015403c80400c12071001d51401c00260036031500c1d291401603000c02c1aa20450030021f00307001c040d904c070341404241c45044100c514151780c06a007022409100101e4801c0130703403604100100b150751007800d02503c2401c100c1c038490744504000c061502011f8004802131000c070f02c3e50f8071080c030241d081c2e00d0720462200c142c01c006203142c001000c0d0b40400c81d00030001003002203030004407a026441e82c0342c0c005d41c1c40407401e80a903191400f04000b640d80150600654641610a0090041080f0616000240f031410700181c9011a0001d400042c04040c04080702c4510700070620146411213020b50320306403140d41095880c0d04d40462a01702c99a140c1c1400410f03448550410003131410ba5412a21132404541c4903400d008079030008840b2121801b504034402c0042e00c07031031290035401c215146c02c601c0700020a500c0c2c0205070390142c1c100715626400003007004140003040c031034880d45811720000041c595145071100800315400c0003003d0143c070040b2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 722833120 1250 722831870 722831897
    0xf06010905061c0b06160209060607050f0604060e0d0203040b0f0403080a08160318021908070303180806040f080a020139050a2c19090c050f0703 64
    0x401a0100a000c02442c1556512440003110111a1007040103c0e085040052400032482e0090130348107800400341100b00680c865400f000380c19240030b800580c00c6001040304a0202d64144594806075014000400d042c0c10280b505604071011090900080e0f0408055440d0980c3d01008682c03c131400c41c101607843d00d015507040c20851040382d00050040500181c85401150840e191500c180083e980303071b40d85550685019815910303450f0803104000d038240380401c01480e200030102d412800001c120f8400c181c80b1006246050200d0300242c0201b402d114040c034404540104120142100e90050900342c1410783d1504007843c1049002081c0800106c0d000500754804d41c042c4c2c1c0c0480000703181001881c1e5801c411404415145000c51003030001444c0f1082c014000c01c1203032402c0c8a161389000440c807040c101c2c0098403800c82442c440240036000c401009940e440b2606011007000003c01451514240d40b036000c031226074020405008050280840b0b61803a08291840c55405050201c050180c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 722834370 1250 722833120 722833127
    0x1605011718010513030210060509040b13080a0309050601080c062a030406030b01020c0d080301090e0a0b0c0a08100605041502031905090f091003081b01060608040c0905040b0f0601 79
    0x40040410796600c0c08041106240c13400c900781d41c0c05402a025191391101501c2d500c4141c40752030184503004000d1790b020400113202c1c68121036215030303030082c02c2200203915a655140d03988009480000651120810b1061000c10b203c0d1600501c0031100514410200501240c100d00842080441d272464410030510002121280c40f810042c4a1090300d686684803503024004001803080340740144a441140741c40d03801c14129891101e40c0220b01c1d681140c9c07810140c80040c01c054452070180f801440443e4000450616205004411030710401c0d48406c107d102c010f101641c01003c0100d0701c2800c00040040c180c100d01103800396580112000c401c4610f21b90240e10303620414040c103050031440e007154064154440301402c10510125103c0300400380310b00800a140ca41516030602100d8265001c000040c00ba00060001c401200203060141ca02d0b0030f140c50841d0500d41c440008107601d0810007041006010340c00c0003a180805080000d401c040e190010865002000c0350105429400801c1440c4e00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 722835620 1250 722834370 722834401
    0x120b090411300d0305011401140a0201091a0f09030a1b11060c160b0a0504050d0507050d0b1504020703020c191a220b0d1509060902030916050117 64
    0xc6910822040030502c81d5401e56030000c00304040b000074074080c00440c40e46401e0803d0414510146c1d21008600034040c0c16060f194065800c04056669400030580050410035100c8003107000625140b00382d24143c20584603904004094a40c9900200002d014098000c0d28542c03102901d91200010f4101c80d2402525a15084124039844100414038407429000000e019100c4c458120b84100d00695030400310046001e0304107400c01007070003884280b04a003480c03560200403501480807108240d5542000c9034135268640c2080d2494600c0f40c041141e42140e07a42c1009800308280c404501d0404a900e009440315000a803042c0700b80c48022010f080b050310500c84e08080d05000c0103e041c2108141390107102640486450440c00c940c402c03488040d01c0c0310251500480d016030a10310b00d0000c00e50310b401d004042e60341040300c8084000d0000f2034566500d01c00c1d1005400b07101d1005a980c00c2103c0a42e140690760015020a090060814040d0b0390344401084110b00f03000c0d04110807a124556003a09540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 722836870 1250 722835620 722835679
    0x311240c1204090504140718020d060b07030c031116090209010210050705250c0605130b0a0807020c0f0f01030b0103291309030207260d120b090411 65
    0x1040482c000c90f2251866220b2805144141c11503c9000d102c0c9801036110001845039000d500d40e03984024504a405400609510304002800101c103904d44520030708a0704080c4040e4005443c00300020101031b000400700c03403042503604c0200221040500300b007040c2c0c001c6003d0a24000d40100e0503030b081c0e90003080010947d801d00d07003050203946880302c80180741d034100d508a00b400840b901111136040c01100080850240c00181d41140141014010340f0713182e00406030140e13032180c245400070f510095040a00380c10401ca540d0701c1d103281450b500003407402c0741c0c041c0001d1080300c451500c00c102d5510402c0c1d803286400f0070308004c02e481c02c568005030004c0c505202643c543c1c260b82201d428018400601745040b400003180c04182540400c5203e10448488550040c05603011004c00c1c800c92141c1c03100749d07028020001c01003542c00130340000d050401200c05081000b060300700c000c07600a4001070003140c0e0351308421b54000000340f40544903015905251301c16640a6078805074401040e044118201c65100e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 722838120 1250 722836870 722836903
    0x10e0f090703020315010c02030627120a0e03030c0c0405090316050a2d03080c04120303051801021204060f2a0201050f01060e0108060a090c090311240c 67
    0x51416401c050065801191400095007030031004808a601031001c100c0130f9a005401800300380c0d10390256910b1680c85030301d0f614844850341320810001c04d00700305965000a0041070b485d2290032201003d0203a80e00001d260b8841d410501940c001c0c00000920304a000c0c0c07080350041440c4e210340100c00d0452046114038014001ca200100d000d001000904400061141d09801c1c41c00d42d1030204210001401030003901022515000500424400e0000c0da800102c01a400c520b81036842811a0804080080407408243c484040113180c0380c1c41c0141c00340d000e11000c020351903c2ca4110090f81d03408001880240001e5441c4121011580d15603c011148400c803800c0541e590072a07240102c00311042624100158240700000d140003060491881c1281c145407640d01051000c9001034542e10030082000360007510031540011b282466005480c00d54400d52200380850f41142410090f0451102c4264015501e03440c10800c0b1007020340302c00c100ca0246240030703501c0c1d20000c4a100d0409880ba480311000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 722839370 1250 722838120 722838139
    0x2e0906062105060f04020a0e04020102070509160809160b1b030c0a12180b09040e010f090c080d050405120f01021207030b0a1a0723063102010e0f 64
    0x2100001c2880804034000d90444003607a50741031189101040850f402504a561003e0400048042e038030b815400134030500584915545540110718003120454546542c46801d0460070401900200229000308444015081401000b21400b038050307118420003050030000200011503203d032049a8281d5180402500d42c1c2d06480412103076140260b8209030340c1c00440d000034400440c0241104041c501500281d002c01c9071400585905075081342d8641a0059102d6140c01c00301e040c01c1c440d16003078881b1a54005140f45007800d00040e245800c2c2c01010866000080b944001030704a0103a0f8101c900c201d034940642ca158810483c284548400c00e10050b42c00862106260b80ca240021841803150b513a0411403030704544104901c0d07003007500c90900034041f240780300c440d034078190310042140d1809038003211801242c0d0b120000c0601400c20340a03810f90480d10605c03280100290100c0719282c4c1d52540340094a01d4074405805c83c11400340028140030300d002108803180c036045600004004010024000d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 722840620 1250 722839370 722839409
    0xc21070608040317100b030406090b0c0a02010e1504170706020a1e0201140a05130b040605010e060907021f090b090a0311070803030612010e030d0b01022e090606 71
    0x180c92002d403011004200c4003422102e020040365080c910510342400c03584041ca180c5007030f211450703101410a84000751503400407004102f6415010307004000380d84480e551400f40a80c02800c4a00c610000120358001c2d104d191280c84445d0b8400c1d4126410910415101c1c0800002074407504c1880001800a400032903c04a09504540e084404121801a00000d2142c0c407100302d080ba40318510344d030041107509010a81c585080c1d80034a620000708059031070b00c4002601c65400410046070203c0da280d403180011b109002e000d880107500800240d45051403030500c03501c060345607a2040c02c80348140315030b401e40911101054011342041a089103100c000d0b8200301e60215150041c0c090180c0124055011034441c1042c0080c241c021520a18007650958803a4820400c03d804c0c0441075803903030340d20703100d10203d28102030000b0030074000360341c07070000b10200804006810b118000400d1008400c4c0d492201195100d0401580d06401d5602d0001036a4041403924200070030f03940d045800c1c0000308804051 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 722841726 1106 722840620 722840627
    0x1031802240c0304080105191104030609030507020607050d080601020f0d050c070312020d030b04140c0c070e1314061003031b06050f06090a050105030c210706 70
    0x2e00e0000c070b074500d4038a1034025811011032655240c040c00000c10740c40b00c08070b2546640c0803042c820904001c0054806011300d00c0080c01c10741e102d40100041505c100c00f16045c1d581e00510554403011107041c4166030307102c291300c1000458040c9010a441e58000180da00c100d440820043c9501c00c860081200c0d250400c156180243c4103080b408000911044500300901c120765005001401c010380c1d004095460004516014a282404044101e2120600c2d42d40c09005d0003001a900c5040c24602c514159465101e166070751103420901c405032a840b40705501450240d5100040781071100c112584500050b0380d1100941c0d81c1c14001c2000074041c0030100c1840d611000310301103044d45515410f0070f0f100100c900c1c02d9050440c03410840e142c680044c8064104a030003004001075810000420b41d243c11032403e41c0e01c00c440004265103070310320030039410504000c10380c150ba540651354903016 = true := by decide +kernel

theorem cover : BRFrame.Cov 722661870 722841726 := by
  have h0 := BRFrame.cov_init 722661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 722661870 ≤ n) (h2 : n < 722841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
