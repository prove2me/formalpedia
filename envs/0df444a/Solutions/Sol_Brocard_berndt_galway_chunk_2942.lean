-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2942
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:11:49.929395+00:00
-- url     : https://prove2.me/submissions/066f6dca-e086-4bfd-a3ea-745b9d6b62e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 528956834 ≤ n < 529136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 528958084 1250 528956834 528956849
    0xd0b040203270706090b0c0a0b070309021e030607030906020c01090b0402010207060906050d0f020d0c0e03010614090c0a0516030903020a1e0308180d11030c09090303070f12050f01 79
    0xc4607452400c105860388041d0041030f003c1172254104004d10301c03999004001c3c002e018800c4d5003440071240c1d5508543d400c1910b4400020340c940290038294a401883c0f40480a4214614030044403420302082e12140000c010700185a6a684144284500d58044921031003901008011030f241c07174030340b0319400b8009940503801403141d41c60100f00c290041e0307000c1042d14041d4944c1c03410a0f8462001c3d4014060b2288400c8030590240b1074451720b0411800b0b50311a10403151601c05041c2d50000038036084860742d41c8540c05941100d4041140c580f0760b1901d2581046800341015529124564161624421380582c480c10120102002082c90361104060041d03030b200b10b074030305441079445020080ca010742c003c498000071410360041000482c0d03d4020403843c195540d00c54066403030407000456a4800000a86000d400440b540c0f00e5490305000400744c1801c203d03644125403c02009c0c451f60303400010050fa00b0312207c8000f440200d4025106149c400000c01c40511071440c01c4001690788038420320a080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 528959334 1250 528958084 528958141
    0x161703100e0411060313140d020d020106060503060d050a0b07120b0607050606010804032709050c03010f090f1401380d051b0a020f0c031906020d0b040203 68
    0xa01d01051141080c0078030b0b0440c42c0c0024a00506080111a40c400340030300320700700d110f00d001c44001801c0320701102160040901600001039110000790419041c84007038401c40e45071000030720000d40c000c0309494001c4416a5502e04601d4076241085c0351965080015000000550411600301c4d44008540003a80c0d5000c803d005101c82081840007502880c880104650130001c0043e2441d4480c05813a903105000745000300880703034425280280c0c104035400120043c1c000350002d2042502900503280c10072091007644d8a90f625044084031035800f2405040245170311610001409145500f091403c0c000502c141da409503500e0440c0b40f400f030715540b286030512000580002c000002e403500b280300511a2a2510f00d00801600e9280003410000c198a654411540c1000c08016520000d85420000f5030014144036039a14100e40c0740403440c4140500c03c1d800703103e98a000840080b0504840f613884600561200203a601200140c10803280c0c140e0418800b0003000342d00340107544202510440c2c2a80304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 528960584 1250 528959334 528959339
    0x1d1306180e01061401030b0a1802250203031b0309091509100e280c050901090e060303070311010e0f0c04060f030210140706020a0306050907030509070b16170310 71
    0x302e00381c9181d84100d0000d980c00c1c0c14802c000354000d03041030b018030b079008010341030b017a4a400b551741e0300c6080b564048402950100c0e0720107024495501c080e0102c1616486003a1006003640000e80d00d11925002c000c0303a40682010702d0f41c0f4a03040003034070f1415100802c0c0c0c540c4c0e450070980202c81d00301400c0206101e00a00000f003a40411400c85460903182415800d445030f5443c0d440b27081e540c01641c0d0a8031010b03511020502c20551130b0340700b0444250380c00e5680c16600d00b200400140409020380003106a0500b5000f401510b0b540001124141c4d941410140d8510480d290800d0050458030040d08040c00386400b01400d00130702040c881c0e000c00d4200c0f0200b083d036071148001c41081c0f00c0c81c00025027201501300076031200f43c00340e100e03030310001080b00c44a031801505a82d002c1c10303a00010242000300e6141c030401d00c028071302a410603038400210301c1d040166107040100c85a8441e034a1050b0300c184540042c040c0c032910865002c0809142c1c000c100e03080d21880c4024021007a62003110700303480071015074201 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 528961834 1250 528960584 528960611
    0xa120b0f070e0d0204020906130b040e063a0212010f05090c03070506070c03080d050f01050904050a030305040507150806040506062704020d050106030e0c04020a1d130618 75
    0x5410850090f024802000c0c0381d07803c3c04002d61200c0c2c0484d0348070000b48107c402e6004401da140010700080c403842520f85107407410700c07640e108010304201c0c4100c100d014800903142540d003107034284070103074040d481e0900800d070700404920313400030b07006904040100031746129a5815009210150f01c2c092081240d07a5410107a55100c2044603003a55043e00035a000308020315002002d03108450050340c103075a002ea500d80d144e26880c1c1c001080c01032520345660400c112058061030795030040100b560801c045181c01d5480d0b580310740284c4e100406156540e00440d0501c0b40410480c005004036000b81041d5802803040945218412038900d0300c100d080100254440c1810030590b82c03220190203500005a88004440441c0c50409107290f8110741e080c0070000f000e00c9140a005d00801d86600d00107804d00c01404a6802d2941e0101c02d103001d540100226411541d0000300c0303842d00c4520b03186100e00404001c0004441c000380300c643d00c0c18141001004034001014590000008000140420184020419 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 528963084 1250 528961834 528961847
    0x417060a0615080406110412110303040b09271504060b0703021e030f070c0504150e1503030c030d060608070810090b061209031e030105030613020a120b0f07 69
    0x26402c0120080c40944030701a019003d000c0d003240c4100400325111101000001071034200c1e80c013031a91510f07070400403810f01c00c0c01048506100016005580741c68200210341c0028414219018050316282036041c03000104600007039122181585006110304000c100201e43c1804181101d202c0c51401c5400160704640400f00d90b105541a00034011400d42e80001038003030724030a240c00d2a40c1c0002c1001484072100c2c10020403600e841092079017000b0703050009000131500352032143c0070200c51600c414000c041040c036841794801c60740c1e84440070410404001c41c0c154000c0b034024000900c80803401041c0c0d00013a802100a0781c441d641c5400c450380d40d2000440340710400b0b451500a91010050900030200303160072840103908060040c42c6441002d00a50102c40c03421102e00f10540c101007203240e855500f8800d01400961041c1d100c5003103504010000c0c2d12214080c00b00106000d0704040c0c00115113441f9134050003403050f1080c200120b40141000f01e120b010840f0398044190b0800006040a0702858 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 528964334 1250 528963084 528963089
    0xb150d0b0a0311010c03091805041505040f170730050703080105010c020a0b1309050601090f05040c0c0c06020706260621030a030e010c0e09150a03080417060a06 71
    0x546010f00c224600c1c010350700814400350640410205000100b2a031401c0d010018a401034290300041500c0c203403d0485440c0c0e6080c0755161400d06010034030001c01e04442c000c0c66a01d41120103004106500f03502d2001900c03542000030002020107000040b006d00d941d401e1112040c1014512041410540d8211118032800e140100810216001840654031843c0c801107007502c05049109125242c3c24100c03404d4201012094900c00c0404013800281060b00615800580a00b800c0405604000d10700500d40c146029440c02030342c1e5810206c500f40e10600302c045034150020004e40384103844483c001e44501c0c0e0b80c041e10010a003045a240d40228076072484201c500c03880c0e6542d5034941c0359001001000002007044010744080d502110200407020b00040800040b41c0c0c600083c0c180c0002071080c00d50f040d003041902405100b0801050701e840f40da80c1a40e0101d0000c000e04181d403010000914a0035054002810030000030401007002d51226001546101156084461f035583e5a1100790640b540360 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 528965584 1250 528964334 528964343
    0x60b0706060e010e04170d092001020c130f0b150a02070605040b040b03090c130e07081506010f090b04090506011101050403020c211501031709010c03120b150d0b0a03 73
    0x20341c001070204000d420300d4241c1c0c00c03489000718035042c07d1081c2c0d441178030761000c0305a5188030038911062040701d0420450a014800303002070264114204001000001d1880c002d050268485180c8900b070000b40e4042c001d000300045c8001855040c0b00c5090145402c03507400f48000d80325402000c20094000c9060ba4100d5080040aa2805080420600b01900050b080042921845115000315590001e80d05c0703214148034400070340030640500350b41c40c2100d0759004440940000304400602c40e41e80d84055840102804c1404c030b10340b921402100c0d00c2046034080b0307102410210300031420b2141600110b005074000d80c4c400e000b02d071130310354203508851080c2e60040c0564081e510744001414401e0780002c0d41241303002e1910365500c1060001e403c100080c1c4040c210846800c0050080000000505d14010800543c5c0c030f080c20304180019080d11400e04000c0c06003c04999000180307035041c2c000d0901280007401d4149200f2410419600d039412246480e0502170410400c0b41c0d030f0307040415040045a402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 528966834 1250 528965584 528965609
    0x409051c030e060c1e090409020409210e0612070909091211030a0206011a070b090f010c1d13061e0303020d02010c05030406020304020406080a120f0801050603041410060b0706060e01 80
    0x20a94161003a40c441d50321b142e0401c0d1142c01c540d0150382c96124000c4818060100350301d0b466140146e1246d4011030002a80601c21042803550160310b9800076a09006403891000c1d149403140e500c04d80e91000e641c4e000200060500c9401301c10054860541c01d5154056210017200302141158503445c0d02803003e005005900041c01045a0007500364036020b065000e5104030f1a00c58103848000c0b450070210b0f100307c3c442c0c1c450030150034102401d00c200c0081802520703150440c5941c124090510b041d062a00a00c120940d166201d41e07400c80d0b0b4885401806000c000391010140c200e5002075549152009801502810014040e101c4c018003500b0b4440003d0341c0c2e0f180c03a51340d80d03907034180c0250030140069800580e50503003c00e1074281085540c0381c0c40c0c0110721202031150740100092807640d40d08020001c0250503001040143c0b10070301902c1c1c0040c0d00642c2d4040358401209914900a0401c2604e17000509003440040c07514100001000c1c1c2c28020325050040d20b45416081c160a00e0a11902610401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 528968084 1250 528966834 528966877
    0xb0102060f04031d12070303020705180f01030305251101020f01020c3708040e060a060c1e020a0611060901021e1c0507030b0f0a03050c0409051c030e060c 68
    0x11039134040704411002070805884041d0144000d213040c28542040380960b00001c000c0c8a14034052940c0d5815440b540c503c0300039072404621003071103408184002418018041a81464800408119030040b401411848051030742820718284502c4400b00050244c0600c200c8440781030301c103001316200c0c030344c1c450b0042030340c1f0850100010040c070150044404032002500240e45207105108221001805070351040c0c1c4a0381003500003807a40360054880b9120b541d03850810000240c00c003034404040c68000210303080b0400015403107074040c010840003c0d4030408006010401e190001e04501c802c4198104036070380d40c5c1d100c80302d560803441142d00000a4a030001c20740341050310024001c01e48a00c3c0e54a084c0a0304d842200070308103850303080d11048003080d00c41200c240d072030400030070038580c8a4045038201c540a01e16100c01e500c801c0142c0205004a444103d42c2085c0001000035852240860000580540c83d0700c800400070030213032004611a0282d0004a0001c05008081c1c4030091003440030044011f2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 528969334 1250 528968084 528968117
    0xf030601030b03060708180708010204063c0e0d060903030203090c0a051e0102030d05010b1b032d04030503030405010906051602060106030f0609051006020d020a110d020102010e0f010b0102060f0403 87
    0x3187c4002d0407030184100c15010914140a0010b40300030300d0551a44c1425010324511f00c030b10115080c0200284900098010f0a8900200d034540310300209405c0101c0e00408500103d1010000d02300b0160007281060f03000340801d60b155004503c1030814805030b480c11141d00080104000e0140b0904e0391180540662a414001d052002c2540720300500490303250940000056055401c01d0303101c004007080c0410011410100c190000001c820705402462800215218034070440450320520020141012031019580365188111005143c11600702e0762203140514000b800381c0b40300d0b07c0031200e40d424440859124900420780210301c14807034000e4041030b82032120440007007034074511042045403565000501600c103807080d180a00452869003000c0c1d4242a4040e00e4038441d604c01c0d20444d4882d841e900c011450ba6000b500303c42c4022503480703a0306419400101e0140039910700b946a1801220100d840c4d0400540c44541815400c0e002d860950343c3e65070108030024000c0707401401140c480820808000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 528970584 1250 528969334 528969361
    0x6150403110f0a080106030b0a270501021b0618060c1209071a0d140c040311040b040203070c050c0108040209060d0f1e1e0f080a140f030601030b03060708 68
    0x710001d010000034100b10800261924441e500c074070f070a41d548080900900031005070455010071281c4041c40f18a0070f02510300c0305c42880001c80690000070ba00c540007040f00a4046510000c07202c814124001ea441e9041500d0751005e43d034200401058004503070102e41c1c0070800a00c41c101c0c41c06240d0400000d040c140c031000400820000040c004d034540400e613281844003492902100c1c0d1741190b110b000c43e103601c00407500e9915078143d888010f1001c11100ba525842100e040d00d41c0300e00c001840c2610300c808500a4925180c40035402400807041140c0e00d540b080e541625180558100d6000e1410000191640c000555000e90003071401000281142401840a14078502c80c2400340304036001602c6d4040b20342800d0401502d884143e42d4018103001c00048120014511040c07203034002c04c8140d035a41c0401c403601c40000c01201c000300b00b400d5601d00404064242e081000040381c1d03600c1041160641680c070803204c0c00d0100349004501c4101c0e045c0065a544148002c2c1c81d201165200c40103041c50f070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 528971834 1250 528970584 528970613
    0x60a09170c0121180303060e0f090718090804060c020a0b0703050405012f0309010906020f0312070908010e15090606150f0d02070804030506090d0206040b06150c070e06150403 77
    0x4142c996541084120500001e21355481c001c4e6400540c80b410030105941c40c60000e00b1b4050161003500c144003210300089424022107a0110b070844201c00107210f40b02c00b80030b24400140ca903140201d4001200d6810502d1205102d1088403001c000c1c980b296060304482c0160900600044c10a000c00d022550042090212a002d020940d95099218810305200b000c0b030920380a00940001c2018849541c2142c80c000c080c1070240040c150308169603110680c0d030b00031940850030440c50600851b100d030b17000d000e40c0405401c2210081c8801e55050501942d5078841403031280000c4518000105a10f802080150141e40010316244200000407250000e035000b0700910044001d00b00a5000440c10a2000f003118600c41c0506039111403640c10300c84e0414a000b051100c10b900249190242c1941c00b045150340540e2200e68000c158031424045420503045a0000d00400400510381d40b407100c0000701c0383d00301c0d1042c03410328649990305001c4c020740c0c0c1180060022008002d000900005401c40814883c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 528973084 1250 528971834 528971897
    0xf0b030a0b010507050f16150c0f02010905181006140919081603060e0307080d021303080304060e06060301020f040608090a0f0b0411030105041a15060a09170c01 71
    0x5151045c1c5a43d070070145140c0c9610740c942d20020b91004120b80b1101040004e00c100c581e0640c2140070048003519111502c2401400c010321408140d045a011b15400009060090802c004982e0009080d440c000c1041d900801540c01803d00040c03000d1050340712941d00221a00000d003400000024011a030404028004c0440754109000c100200200f00f50500590030b4012090701d5807035030915900b01d0f400342d600700e540c941081104c040840e146c0d00440704032050300302005941e041c64074082c101ea11101d81006080c45400000c0c4014040d090b0400d42c014444002507510325200c140415081344520302c000028010305100402c11940505000c951201c00c0c0b80c00d903209910303560745426030488800310848050502c02c050100340300c8011051000e900042d0001c0106041c00d85448e030303034140300421203221020158009800005000010504a5005000540c03501e0300800c028201042034042d5210713100591000f415618800a210740d0070721010b07101c0300488031800d0911104200800404d02 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 528974334 1250 528973084 528973087
    0xf020c0a030f020121020c1e060402030a0807060b090f190c02071205010605060a0207060f05040e011401020f0d050a020d02070e0a02130b0703032711041e180c0f0b030a0b0105 77
    0x5c640e2400350000707101e1004243d014091160780010741860001c10480007002c554014400c110060310009070b0b16030b00c5078000c0c07a1591261042d240c05005000a11326103508040c2540c20700c026840c2904c103141c051009420003c140d8100c3d4071108080300c144184a03801640300580402a000c95810485030042c060800454a2500c500102d40d80f903124524a2006a005100401005511241d00c3c0e60350492460a145024540281f0208090060046400058450b07101c0e58550b03000300303c1905610058010b0710311402c80790b440903281c0e8016800c81005802400d2160000501c0803032030005a40c100d030031001e11a1140810a0020f4101c0c0d14080c140703c1c031035038010400c00300d940301801c98903100c0d9801003181ca003900c01c0144442c014074420003014a6500c9000e0006200034690b0680b15000d860014070700007140641603007800c6009d401d50825180c034148844148245510b8402a400703005400300d0f850380c401c10300c0b54a802c1485810b882c0403042c004155401041d82108040c0c801c1498030300d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 528975584 1250 528974334 528974387
    0x11d0402090910060906020f0a03050a050c06101a0705150a09051207110d2a050409050c0a050105070f0b15120c1e0607030e04090609030f020c0a030f0201 68
    0x340000402c3e1a5840c80d02e000503000c0103110303032118440014281920142828981004065540b81c4800f44024240940402c001e90f40380c0c820300907a0314030801a02188e0940c20301c00c00c06140c5013000d001d00800e006219044040d40d20012017101e5929a001c4010804110101004049030001a0000c1e281715100d03491140443c20820190407981c0044400e642d459079a4039011001c07040e8441c0042c099859808030402150a42c0c80c484a10550a00210b0f0b8141b80d06800e1100c03010140c01265100b8500b191703c806001c400190480b8440c4103803160b103100c6849038010741d03190203801002481d03000c1c00003c01000580c00c03027149800507865485d007800e03a49610009400e410382e42042d90030541c801c00e0000564a40207104607107000c04e0440c41c8160346240004074203d0710401c5400f40500c2044440c1a10b00d0310f450780240d00054200c102041a21032618009028070141c807a29401071190340400c48a0f4545418120116540480800041b48607980151207408140e0040301541c116031954 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 528976834 1250 528975584 528975589
    0x709121b03050d02010b010816050a030b0a0803040603050c2d0403050102120f060a080d030b031e06100906050f090c0c011a030d030608060109361709011d040209 71
    0x140da01a510400c06000fa14140c00c000030700f1100d40055040c10000e41c01c042c0580c030041d440074505000424600300b80d461041c698160060722461259641101031000009800301c03010029009440c3c1540d07043c05542c0704e0300702e030307440b140902c140c1c1341c902c12003040d07092002101088160082101c8002190304050ba42e803181400c9802440444280500c140200001c1512600516030300c40300c100c1340710308070505107501541d132056000020310515a45103003800741070781d0400180340b003d9942940ba0190000d0490002c1d125a0161561281c0c440048400310317000c8054080c41098038000b0b0144103910039140c0800103130310400382003540a484100208400b162080c0242504e40e10104d45980b42c454046040c18607054a500e850000c0502e031210601c0b0001c0702065180c115175420a000c290940c3d00702031500c0740c0d018800340e0310040411402c98258801d000600c0401d041c051040308160010307560490742d1501c074003001c003400204208a4941c42d58144c80e00492103003c0a030005040c41c803401d02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 528978084 1250 528976834 528976883
    0x140d020d080409050402122d012004060f1b080a09030b09070806011d011502030f0a0f080a18021009080304030303050a0b040c02060112020d17130e070912 68
    0x244000f5031940c0070002541080140d80011206400040008520101c50710030b03082100c40800f50b1051642058101c0c8840941144030100c075040c01d0541522601c4042d4a51a4018030520740441c8803646400c00042c007402c0a41132040005c02e500c041100a503550a00301c0d80641c030003d050140044c40130011030321a28600e07200324082c0c4002c003000e03801d0405240c505001684082c035903140700807914904c40001e5a99504481d82d04441480e00b0705000401d90840c0034100c980810200c01040c2c140040d079002e2002a4100103c0d2103403806a00d8005020050390307030065050042400152082c0700509051000342d002d0011450b00052503500c480d85a81142c1c0b140d4130981c002074070740051242c00000c0d07100d5422001d404940c100544010300308041d4031100305100341c955541074104140117644940318a0124154421031a00e54140590300d4042a030304111401e80d00c0d17801d1020040703902d2540c481d255022b40265125121442d19000c440700b865490548101c5900300000310440d40c02000c01c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 528979334 1250 528978084 528978089
    0x70e0c1207020d081f030807080d0213090b0102121c060504110c0c0d0b040807290f060306010303120f09080a020106051f0e010e06070b070503070f09140d020d0804 72
    0x90142001c3d07004050028201103003d000d44401c5000221209901418407100000b00c1c2c0d40804001c0d2920024200b00285000d0907032810255800080c414201280d503002c03800075034103649410087c00700600012641d606a034000d500b80c64100b000f816034000f905185101c0e0ba2500e241d80411100c1d168030100d0103480ea441c40880d146900850101c8041d041441518402031059030303a1050302811740c80d9240040c20160015104810000f40707081441101e104044204007400c0d408510040e00c4c0442260031401102d2202d52041e4103c04a0028075022074901e04a03a0555a43c03031060030001e005500030030700314170b01c1422203540300c08600004020310060080500540c0000501c1d41c0f80409101c641c1c000300d046030811000303030303401d0030b50343ca0f0000c210050286080c680f10303203101003210220b403a40c440c800d009407000900904002d00ba982c400300442c41000260744000008020702001d95080c2c0c1c0034041c0315000a4054102402406d110300190b410500041c8982c60b040c00741d4503951150b60064 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 528980584 1250 528979334 528979337
    0x11121005070207060e1807090f1401121a0108061201050406020a03050702070312051b10051609030f0b04060912050d0b0f0d03030e01020903010f0207020f12070e0c1207 74
    0x900c1040719168040c40040c006012904100b8841c3c0280000100d403034400c100407148800b00d003030204540c180300d803440501071300c0312801550b002510750485801c06020a0402400514554001d1811110790301640004000c64004810044c0003040103443e9060001c0100b6000040c6c844005d001400901031940034502400c401660b440780f25400900b034601c020710400542d805001c4c01c00006040029030001400c4da40b82007629040c0e45500005a421440515001c5104620401c0c60341c4400b980024014403400001c610296107000341642e041d102d9100181090344202412404180f8200100368018414400020101c6035540c4070700307031400d407801d000380015804138200c45e465645104548104508680e40c00d00300c00040f0000b09240e000441c006d00b0951200070059106d0425016150310071070041c0240000a00038400388001d402480060340b003031252090001c501e0402030141c0070036044c0c0001a0111604001c0592403a000c041c0031b9020f511810030254000840e030000090140c2c030316 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 528981834 1250 528980584 528980591
    0x24080f0c0a06051218010c052503020717010f09030f031a0310050a020c011b0207091b1d0303040b0d110c0a080f04050306010e010501030e01060b090d1703130203070e060d111210 78
    0x460030268078041d58081082c142c410707440310880404d4001076013008952103140a60075009512371268003412140790300310082c0d81460031003030805070800040c66024120b5034041001081c1c018a140128444489081d01500021070283d5400f4a5421440d44140030500151500402800403402c4880b0b80c0101d080111403145050a007a5040c0052780c024180108244103041d49070070ba00591a0700300d21001c0502118840b5070300c14017850950501141d10050503079868a654840c1d0b01c41d140e208907400403030705140000522501000106440c054020f000c010102c4503125901c011030f40d4480842284455018000083ca6607410450240a800b01c4210b298a40d4540343c005403d460600d040701400e40d041440c180000003189050b82c15101c400c60b60140c4012300c9080104200040415203045140000200710300d21807904d030082d85940c0709800b11100c4a60b2400482001750080e1a40b50380241a060700e4404644111080b803004400240010400e41404410700e140c80c404007412401c40d6107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 528983084 1250 528981834 528981847
    0xa06030911060415080a0507050331030210060914070f09030503070c050f0f010c020609010306080609060105010e0d0b0411060f07030327020604050424080f0c0a06051218010c05 78
    0x85c0402001d4004100303140611160910440c042c105000c010400540c40c24441c4a8412554004c1d41000010541c503851b4072811619007402921003014105002e82c541c10131000280c00c0595209040c00c0f40304114030f0b22201e4585150803134602d24050b5442e000c1000014010003c036006000400f4024402e0b0303150840300f440c1c101031121070194540098400d14264281d900300340d0304800c0395000d03c0e030b04840640da152203140c0180c1c020b02540d0000b1040d4441e59081280b684c0c40080c0c042d041c6c03042602c0304a62a51181c0400c46d50795103003c0c000301000c035894049400241c07848034180c01d907030004006a0074060b2901d20407443c0d80004c070050f00060b44a9500d00c95000081c41410350a0200074114011404640c01003061841544074080c0555680c403001700344450a49009000b504a012a1410300e80ea100001a61110003818500e4103004141d1341003030030700c0d00ca101039049603810380f1046d040c1000060700a178103400051529200c40102070b400e02184038207100312011303200b082d00d520fa2030b030b40c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 528984334 1250 528983084 528983087
    0x3110f0a02120906090d14071215020a051903020409020f090a050906030c0d06020405030f0a0b0c041809050c090a140c0c0a0209040606030b2502060103020a06030911060415 76
    0x7401101c00c445900002c01c10040661148402c65041740300a070f4000c1d00d150700070b25000801c0b141c190840100c0e4001e44101040580107020200c50003800b60b0710701d1791142200c0740c250f0128440c203540c02c000b04808115040100c00d80c4281c541410429040040c20940e81300001000d9038010280b4a03483e040025151101d85040c01d032090103003074103071641201890b11001080d603607000b00d03100d140f143e61550745000812643ea0100e03805403d010341900c0c00d900e070100d06103035200e00d031240072038400d000013001400051f0403034150ba003241c1d0b94145000014120100080081c104503109452a014103040210b0300d44a85800c113011303082c0888009010000c0341082860488045d1003951000b40402032448014800100500c0050701114060300c4c1e81c5035442e056008041940c00100381100b64030030010720a62114544d0900c01e81619101c18035025190202c2c3c41e814240002588800c0c0e0b10010300c8903503c00d501c00001544100700854003e1115400140260003030340c085880f5035441c061040409 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 528985584 1250 528984334 528984343
    0xb04050c090619050730020a030206010902070c080d0509090a02090a06050309030d15090b0a03020306011403160303030c0912020907030c0318110312210a0f0203040317010b040305030708030703110f0a02 89
    0x6d07280c92000e45242402554001d444041c10701c12202c40b20307000f09a003414841c4100c0707040010407040b0b046030098285c1201c00790482c1c001d440024401c4d4074040c0000c124031500c1c02100c1c241d00c402403800001504000041e1400e0708050074840f143c0c231046c004040340e2203051091800e010b104480f0100f0891030040940c3c184c032400b88100e4068003103040704000580300000c1150544400441d80c4411400d514080b0b86840019804080c3c14010b008000003455010303400005105e4450f41c801120548428125400c4140d0404c000d41003007a8400180d40c1c181300c1d900000c00c3c60414030300400c10500315014280c100d82188000e07594202c00e00c10340402e610f810001d4400024030031300124140191a2041800c003e810366208688003e070b40000f0780503400c40d0340480c5440e6810380d411034030307402c203810700070051042040c80316000400d0311300128039100610190b404030380e4000021071406805a6901c010780e0000740030401456117500d404040795840c20080c140400e2b6010711240ca50a04640c000d161 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 528986834 1250 528985584 528985673
    0x1215030d03060e010510030207151e0605302b020f0d030209150706020d0501050a14060705010b12060a0b09060a03020108280b04050c0906190507 64
    0xa0616002d0200f10b100340b1840140d04640c802c13105840400300c1c0c01c0341a40a40b1403028018070178101c2819104155070598444008686503148072403020b03da09525034211803480c05039542c05032041000c81c4c0b0351107442820318030801d0b4070700071108051020501c151800740044548901c005040e01484d80103030480351404140c5c4843c0c401440c2005028251903203440d0380711031800030542c0004d0083e1280d16105503003003810084150040e940c1189042c076600941013401400c0020b410500006403a103810707010700301940c442e0781c075140d0f100442808005096000c81011135407175488041c5020540d8400b60041582c1001c0406460700c4d00e003601408040751100c0c99624030480c9140c00f404a40c0c0c0f45d80041c0b909480c0e080c02c4c0440c0c0c40e101e03007600180000d80181b02074403021104156403c0f260803900100418441910140702d66141c3d040290f20078003a803041d1135004241803101d1034000110300b826000000650501c189000072944803042c00001c541001c0b41140c2e10940710100c00d004400c0c00c00071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 528988084 1250 528986834 528986837
    0xa0f1d1e010603120c0309080d031b2318061b0f07080c0409060e0d0e010f0311070b040c08030f04030b0601080402090a0b0307050a17010b090f04030c081215030d 71
    0x682c50450b03440000342d6482480580c00c0216503480703541018080c100744005043d110044980703c02034103000a018040d65108201001561600d01c881d59000d4807802d00c0f40030201034060704076840d65002c040690090014001240b4031502c8049054a900f4024000b90842c046941400d80342d100419107090000080e900d00c641c0710040410060b5004140300459000c1110041884161400d040300688a003000b1400140905000d1510090b00050142c8207800c00782c80da071105481c100d4003a0b0031140c036140c0c401049042046100009020390107442d0b409446109958007003510b0354030f40c0c3c0c6103402080402118480006040c0184681498825400282480c00483d1803426501090941780003804003501c071516070804480c2941d040c803a0b000a07140103003039082c4241e0f489810441030b0b690091a8220f40d480c0c00c0b1188a10301f0818001c902c00c520510910085407a1a41d080324007005400081e24900c1082c4100a4100c505242079401b510030f0792201c51110a01c00101800e02e03246450120 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 528989334 1250 528988084 528988091
    0x201021b011a100e040203070c06150f06140d0207030908070e0604110f0a0c0c1703030a0c030c02030f090d08040e06030601090c020a020f030309060c0616170a0f1d1e01 74
    0x1603150b503004248000c214030a0705c0150312525940403c0d40e80c0b064211004140c00e041055400c889421200024200c98010b4680c0b07094580c0c6000603245019140881000e0031800c200710020300a194000740001c80c442e00d0080c1083c3e603070b22000c5003054a00d4120804e00034008081c420361707180902440703240c1da40c00b00031103141030070076001c442c55881003441307090a121591107100b045c4100300420b0401840d488080d40b044c4c4d0400c0c04a6600da520440715030244516000041416611900c0b80030614105070300114604404ac603041c40d065000001c020340e1190140240030b0009041c130019100800c1104a48445401c00c101003505091051300240d1855250007078512440d0707070009100042ea501078400300720b100741c107501003411440307070380026a00030300002000391146800107965031242e9000d409030000d4503020703c070886038241c40e0391020072180034060101c2c00380c00541d801440040c4901c2c10000b4556107504901c3e03640442e841c2c003440c442d00b00c00d40b10200c252401c00d00a4010f00c0400c000c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 528990584 1250 528989334 528989359
    0xc0c010c020d121e0509010b01031410050105030c040f120521041a090603090c2106190b0409030807090e01180c0210050103110a1e05040c0201021b011a 67
    0x402c65042a0f07035006005403111000c404a001c0002c40c4140b65a0000061005280000c800c138042c00003010050b00003844c020201008240b08150301d802042000d40076030202d882c15004441179040a02062030094042000191618044c0320502c01050750340c290406c02250750809034108000b4103c03600341242c02c50f045c42d00b81440e4400306e8096880c64614083c13108a58201542c090081e1540e41c1e8000300d00000f0301c00d49400004249c5855901225100c1c1072601c0c4180d14070030842e40c2c4244800c035902000205a503d42c0c0004980408070b2041000111803a80c000010103490714000180c010035050401d0040c480e90000c03602c000740680404c060001e52501801c0c4440000345030807003102070381c0c40111090181c428003072a03a41c4000c00105001e6942c407402c1450070212845007051007418040d000083c1400e20525a00850300941d5103200071034070b441d0030f010162500000d10411558200550380c1103036050040880c1c0071000d8000010140e182c1d490007400400c040519900c1190b002c40d01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 528991834 1250 528990584 528990587
    0x30c0e070804170d0501180510060804030804020f100305100b0702010c0209041e0501020a0e22051005120312150607030c0201050d020705010504030e04050106020d1b06050c0c010c020d 81
    0x402e4205074402e02c442c1001c410844030001601603140342e07846550400e000043c40c200715908010102100000400c030356154100c406120021600c1082c01284a00b000200800d005000d0550f000b40058441501c184500300040c0c056140c00c000b5101003982c50090051005061102c0700c0508880000185000001e03000a051940e404500034801c003032040005040148052900380035200341800c24603030388600c0c9006030107500040c80c00f40002d0701d02201c000d10761401d403040c58081c5a175120118220001c046040c805848014034100b2681e20301980050503440d100c1c61107400c5c40d8410003854580c99213210455403250040d01e42030b2440c80704c089000040d5034a20859016a07410306000350480380e207200685507070040040c0164618400b041c0102803001c10740016110710b211f07039178800c2e424800d0420402154000c6c0100401648603841c046c517440d000300307441d00e40c2036401a990360580700039503114000e5400031907400c0402000880c0181e0b408809020340340d42a0420300241000b4000440c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 528993084 1250 528991834 528991847
    0x207080705130e0c09040302070911040302060304020409051c050a0924050a0e18040501230112050c040911010f050a0806060a0519021f11030a0b1f09030c0e07 70
    0x107502d901692403410841c02d22080241018603180130f09030701e12504d014240a034880046105810100e82401581e00e002c0d8250302c1242c00343d95001f070400742140c41e130740c0034000200304c9044111158400c2c046104000d241c0210b1203e42d04090f583c803e540c0c3c410340c2000078040c030010b03441994414520b001342d40d0102d02200e581c400c0558540740041d02c2e01c082c01000c54006507108426600711001c1311525130080c408041740c44c440c41c0244000d0000102d9400c1d582503005005102c104288004001808254101c484041c06680184100d0f10038005c0003002034103e0704c0c2003400300d80f03c01900300221036550b04440da1100d00413050400c181807400c054400390282c400101007600c03400b4005613048580f80680182d80000c0c012a90510405c0c6100102031b69842e61580b40c07804102810503650985030301e60103a00800c1064040e00c5056450f074810351805001d10020941e44084156004482a0441d032044450301200b0b950f03441d103091079410860400d14250f080050024904010041aaa008403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 528994334 1250 528993084 528993109
    0x100b10080912090d12080f1620030d050c0d0b0910030201030c1b11130b030a06110705060907031707020d021003020f131406070c23041b0207080705 65
    0x707035034642e2003000800180104840640040105450115003005e141c0c0c408021071107841c441e01c01155540b203050002441c0f621a00740c520010300c2000e64041050400c0100c1d15801c14120100c6e400c4c80c038203001000c00d81e201125150b044032008500b04031954154015082e81e65020b481240b003600b03044e00b007501c0d0303c2e1090201905040e01e900464401d1407185184c0700c0400c1824114828400d614944034801d04500602c0500c20414602e001494100511454900d171800400a00aa1481d42e8410020b401e80f085800703107543c024000140460000c3c000c0c244240c6450014007041815460003141130f0b02c4d100350150090005001c03100043c0c45c0e422464042c3c0c0d40469411607120055181203000c0d2194031050744400c2c00224003203006a06012400b0280d40a00382c03940f400d4142c03030003401401c0c06652406401c03a041d8940411a055440d03042c4c8414148140c17208625042c0000814240c84165003841d61000c0103000c5c41484941c1408460040e00105001d0b0003010310302800940402a0385 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 528995584 1250 528994334 528994363
    0x8040e04030e09072f070e0c04030c180606030504020a0b0c010e0d030b0108090f0c0915060a08040311160b0c0c0a0b03060a0806010b2a100b100809 65
    0x14046824503000d60000d4502c5600203010a9483c940800000d055015081d442c180408522440401c50750002040764001074030706000b48035040ca01700d035030840c580001d012254040780410001c80483c4030041498082e0007400040741a403032905407500708859840d400b40003014903200a0000580c0c4a0040804444108006076101d0504041040c01028585968250b900c204d0f1460310b406030301600101d81c0c00a003620348130103990718030809503140c40b5103484d10019a001070340d43e000341c1d01d0580080c5401481e10080c8482d4024080d001c81e1666100040321070115805804006c10554004a18001c94051801904401808101c0d00000307044502811090720004180c02c0fa200c2000c02103810034200040010032959594580c4070030b44d500030354116000b4a00008041007620000402034120307907480e00304514120403146407451070802c448144428a500868600b0754030010000c80b041c642d50844000341e03426080003041f0313221b401d0410080911010314100000850003085105c00751040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 528996834 1250 528995584 528995609
    0x302270d03030c051314010e0d0b0432030301090f0b0f060901050d150305010e0a0302060c0a0507060c02010b01020f010b06040b03090a0b070201050702060106031b030e070f1706130804 81
    0x9010f010354950141c01109940071044442c00614a204100210041502a02e4410260805505000d00844980b801800f00c08542002c580010028030004c6149413681c8202030342d40340401d500c2e1007080b80b603c0001010b03510101c010b211262151180c8010213840c03200030004e40048202141c1c00816685820b8402e56001c141802664001c0c0201c400135000c0030800c000c0e1080c02105a51004403c0c0019115580f9004c804d01c10076034001920500c0d07c2d01a002004282d0715601000030316444407418004104c002c0c4040070001d041401900c0492102c2d4002180891034000024a40610303a0b11500040c2c0c144402c1c203c4903280c0c3d0007220191401d0041ca140c1e00da80e10f00c18542703480c0c1c010700002c02005641040090f02507041d4042070046903c0da003603800301d0342e803901c00314162509070013540310100464400c400e03030364040d07400f1a2054250310182c0b031406030340700310200924003180d1021605404c4c4d00620f0040050a11407140e0040614090341392035101070700e404040f8041d83c01001c2d180c01f035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 528998084 1250 528996834 528996851
    0x3090105061815150c06040c0b16060902011e021c050324060c16090509070308030c030405010f0c090f0b03090a030f0e0a090b13110a030213030803070302270d0303 72
    0x9604044c080c603505400c010b15520b50042c10400e1350307841c04490641e21000d01c2e60002c00d1110341d800895002900301145e02640c0301c0980c5400300140b030011803c07814000d80c0850090201d058140e40c040e03408160300645840409140c1c01000300c002410300b60200002001040083e04c481198040d0450441040e05203201d107280102c0ca0034403920a903401c807803064010045c0484131111070315007541c1010400b07202d140c507a90703c0e0070b580324103a00000700180000d20018001c4410040550b0740113000d000003090340f840b030010360401c40da52282d511002800302e000c14031a4030b00c8001840018000a58264a146810042d0a40761203c80c44020200200f240c1c00c01c41d002c1c0702d45140c8802410090111104d5541da0314400d000f400c0c8240d0b02c902601c2040300d4500319950922402e00201c401c18441e80c0343c41901c8004500a41c8605402d100c084a5448040081840a030142d44201d10070785005a8440d802e4044111741c0c2600007035001400f08a0b82e01000c503807a40c40d0070184a941c5070501284103078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 528999334 1250 528998084 528998089
    0xb030d14040e0a021b1506062a030c010b120604030e062701090803031006110a0c08010504020301050f0c04091112090a02011b11120a0f0803090105061815 68
    0x8140c0d40715206400e4003400b40b00f00b03928540c0c010440d10825001c4d80000380041080b064603075072860046100798041c68001100c6040142c01403400c4440d510311100c040180441c030b08041d2554070011503541d880070038090003000c0244541329080d84100c0b0242452100e40d654180d884030000c00c020f0411400c1d01660300242c403a0700c00c5d501442d0700d0b030503051103602d034402c1c00300800482e980100d40000c2c41144001091071000c0700303c5e4000d04034500c52400107410003a06030f940c950600710202c00da210b1036600d000070540070001c46000e048100004503450400b401018203440c00a008203020640140a102e2031114107012102104d940302004610b078240a0300210300b5001d4105490010f1810204008020901141c1a040d65200740c03a11001000b0003080d03e00c415800240c01014506c689030b100c0003501e06410a203a0710300401044981e400d00559884026004110040b1b803082804030900002690a0148079400501501d140c1111280d503e2160100c40020307013410f07000c1100c84003103400c1341c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 529000584 1250 528999334 528999337
    0x30908090609180f060a0605030106050a141c0f060807083c0307030201112a030904061719030807030b03070807060914121509160f0303030b03010b030d14 68
    0x120101e2400c3c3e1603d40750740900c0200c402203881c240b0501d103400340850183d0042d4103490580300159102410411303142c0056907802000d601203519500203200c104401da900c1e00c190b1040d0800008040351804480103044280c940c15001000990807020080c080d4900c0000c410120004002c1c0b0242c0e400540d000d1484841e964111400c01c0d15407800441e00c0051001008000c0b00e0b100e0750080207141800b0001000d0fa00038100b00b410450010071840c1e110404100c04e100100480f0300c140c03481c0c2808000040c08541195004d6241d0521008a5094200d41071202004003207204140e8841030055070350003270010134001c8c1042c007070641e80e0001031003a0710100b0040d4007402c1c1c21400c130381e1404c0c0c0355980503051038030034844c1041010541d100d03000c06052035410b002c86d11804900038844508101510401300000800c203103c2441500200d440c1c8248001406000306200e00141a00c039040d41002816640d034120f400380268102911460280c50000e030901c0c25800074900b140c68400e02c0c107580a103030b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 529001834 1250 529000584 529000609
    0x70506191b1a160e03190303020c010e0a030f03020301050f120a02040c18170a060914010906020409050109140103060e100e01060501031d070b0a11030c0604060b01030908090609 78
    0x20454201040d03400c1030040760186000c2c42010780303460721024070342c01d00300c3d00c005130064034503059004043e0031100014924001c00030750344a801c000d4103041c540c4c6206400c4076200745078000380d540718003503610525400440e889a6103ca0b8034042d8915030400002c50038501c44440740038000c4c254094055000101030203071805440e0300030414083c400346150003d04080d4504680502040a10800912420720543c94800d04a20710301500c81080785032190070040900003070a64001c0d041c804200c00d9000288034400015204050040c0c5803403c25503030408075041600252080e506c3c1c03c040d995a80d132080c41c1d030350440394000c002281c020400b400b2a400c00703601802505000381003010000078442d045d0000300903900203a0f81003041fa5115070b60f00c802541d8404087c00c00307802c0920180b0070b030810f80d0000c040d250300500b041c641c0c0c0410721443c507280da0300400e00c441e02500600240030400507140201311010900340b8090000c2c081d80d8882c0d4000e441030813010740c842c8138001505907150725a40d050498 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 529003084 1250 529001834 529001843
    0x6030204021c0b0f0102120309190302060717070c0f0302030f0a0504050f0d0f0803060a120b0f09120a0c0c03060207050a0b070c080328050117070506191b 68
    0x44601c18031008882e080c150711000481c25080c0541c211241c02c20489141d402d1905900030304801c003200003048002d50015103a007615024107034150020020865158068a200b94002d000920b44120000d28126503962000324070f060f050700b4015180ea000c440c0790403542c2c100007030145060241c07030245d02d584100395081c120000c000c280e642c040790b0414068000c031001a220107941800b48030030401c0d0203211001c000c000d240c29251001c0840c111501641c3c0c08940600a06001c94070b600d010b1400d0301480c0d0046900c440c1c0c041c10020490b200c3e02c10542c004e01094000c043e1020300211140b1180191031fa102d0400030040039540030701900c04050002150000e10440d0341700040e040441d140d450701102510700c0d86207440822a694880c1c41e52304403a6410030002411a29500500f64a0342d22551500021034000c5a02403414074142c8100b40c020180420318000010a0021007130034218183c1c041132003140284400d98500101085841103d2f24034940308100075096240150050500c040242 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 529004334 1250 529003084 529003087
    0xd12030e1006050a05060f030c1605060a020304050115050a05010c0813031103060f070801091e050c040512062a0f0c0304050109051f0f21050103020108060306011d06040603020402 79
    0x100824254082000d5503419104e049200340c440050013040c2c1705820025000d00c0081000443c044109805014127060a20210590441c140c80b01442c10703a094402c080d542d6800070a001c200502441580601c40842103024009031900d000a079508840d44211030520100c000401c0400c22442d04903103091001e01c86070f048054690810110301035404000078028440d08020845c48483c0000c0c00f40b04901030303a602d001683c249000e00015001d44094613900510810b040d0000e512940104c070300c22901641a02d4079a4508010050b003c0404810796805811100070b118442c4a1588141c561545220080307031048002001c0d54150320030f4040c1c01d2020700002c22450003898010000b070003211002da0343c4880c0701f5214804c10480064000c06000b0241141403411510384c042c50710701018174894209252031000c2c48580d11260182103949040c40c07039a54005004568109403260781241c0141d0003040e070ba41c18110800c090f80d600304543e0a03600040c0000944030346c4c0d642c00c544e011712341c00362055 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 529005584 1250 529004334 529004353
    0x60109091d160b09060a030e0a1a10030b0f040f080310030c0603060810090305091201091401021303200d12121802090c1e07030f020c0d12030e 63
    0x22901090705000403207a01038032440d6140c42a035070340e000c41030b50b11407002c403072a00392007070204181a40110000402d05231601d0340f120071800148549407000d4002d23100207150440c107098202d000c10004050350208a81d23460144041503420381c0c101c1e400510441d0a868a0701c903420b0120710102a0742d0003c2c0003080000401058424034080c507030450f4850022034070b22075120314042d0191030140c040c1801590100040e10025000d5410a4480b036020b410400d103001c2505d00032070f91090140314144120380d15a44c00c0810410309440404e001c0c04440000c40c2414504c92034600e51341014400a0204110311000c1c0c00b20804c05104031420300002016490112041e207070041000942070001c2011a072119621007542d41e150085405030414130840294558551303003007203520b00b00034143e005101d01c28060503440d0f0542e100030418140c0c41a1040b42c40d07144914005040035032010701d030300c11504012265200358448066203d400c80c0d00100b500c14800350705908a0003000c184015243c80d20078000d52 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 529006834 1250 529005584 529005611
    0x8190908280206060306040f0b0417030705072a17010e01050406050f060d030f030f0e01180c12050304170f010c18090516180b19090e0907030b06010909 67
    0x4081d440010703001d480315991900f00b05512508101c4014007143e10f04410100020000010b05501c640f00d1054021000000c2a8080c0305400032140c0c0000f240b070000b01c030020301611909500007411503102c502c00343c44011010400d072104d144601101e00c00b2284a1180c0c2400a4110b00d03120100000204180d142508110002e40340c00c0d18000f03000b9001002090090615460b00d03905540c0685070070b5044a1203050480040c0b041c1c0103914000750352100180c442d80001c0c01418511001d02140c01c00075031590a002100c1c16003540b20154034a0502c0700c40001600c04030583d0b003204c10209909005a401040c100d085c6201600543d6081d4a0401030303040d110b030090080400c81d00b1004181c0e00c00e40d1542c1400b4210f4a00351140c1c0500311291034012241841203803c001d03076a50210001c800544c2d15214a030942c0c21442c1c0c1c42c9402d8403003942940d0025401400d1400914081c08110750301e0811145098030b4801602014014400c00400120103902600c6804000c20000b00c1c01c0050440642c0b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 529008084 1250 529006834 529006897
    0x406030e0a0b280216150902090a0c02280602030a180c09110708070b18060106172404090303020c030714060a4d0c010c08190908 57
    0x6071801000043c0310301c0a120f00c443c400c0d20b00e07880c400c1c00c038140700441030341b1400c801e0136036180030300c0c00c443d141e504031030068686140d814051056500e003c510800343c101c0c0a424003070f4030411503c0605949000c03151204410500e868400d80090b0010703500e803191072283d00908000802cac42d00418181d0940c130100003110040504680c2e500900300698070182c0390010301c92040b000003421300700003807000c13034042070020b55000d03041501c1e00070700841005000c080c5428600b090f032001004c14454400140751491300e0519079808101030040031890760802881c8503003102001c0660340625524250001003600a60444280561740c604481d111421031418000401c05a2044d402500843c40400d00d803100d41e01030380716002201c1d13007403003500c210f83c0c810080d1407242d002c8070b1303241400c1e188515904040d01c40d05007a058039024208981d99405103150a09440c54a8018801c01412608010301030394004050f42c000d003c808008510000b15040180c030b40d00904c0e184070701101041c040300700190702200c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 529009334 1250 529008084 529008121
    0x604120c0f0617090118080f0d050709060201060b030601301e06051f11281211120d020c06010e0709090c0504030f031b0506060a09060b0406030e0a0b 66
    0x3030100c8025030b2094400b6080c0c0d400b03840300c9002210106506e1001429a0014050022210703a955081c801000c071f14105541d030079a00c11000c0b07204500148915a030a00495003e0074007031918500d14107090740002c207050108141400c0c0c0c0300c0303030315403550307490554409a20003400140c20510043c0344c00000d480a81144d141038031101c502c1e11400103924242465517043d60080c0842e168080c41c4510010798400640b04580d81960103900c1105042e10b0080e4200b0840b03080ca0807020001072000c1c90551100017040060070140456000113100c200000101c01961a2651806544820080c041030010340142c5144100030300860f40007180022056113020310910032a603c0080d15070303485180804440d00020400f0004a00b00001c0c408680640302c10403404d0301c00d02c0d0001a6452801c01c1000031040d01c0d9048a443e00420706001441c030348412003c010b01303e140010003142e454542074a080b032040b84030301010f01d030b2070306600c122007881809420049500305201425078500b44880700070020681c1c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 529010584 1250 529009334 529009367
    0x30f0304030818120315150403060b01021006091409030c07031e0f0803090115080601031b150206060f0415140103110d020304020a060c03050702010c020319050313140604120c0f06 79
    0x14001201441c0c100501f0400c001c00c803070814a8141107864020152240341c1d505419885035100c40e40b8941e403a07109240050402c40c00002d840d1480f442941e1181901510200c0340768028001041c10f013002180c1c18084a500a440301e9500c403000b0100c0081007202c0802a1900c25410392503014018030b0801144200c51340d20003000190801826000c11038a03500880700107070701203c014030004104c0f5601c030900301c1100300c4000c11143c0c2c43c40611541c0c2500390303040c401a04440240040c0d400c0c078050000096008030340074000d071701d2407076005030070064903105040c00159601e5444000d80d00903448801c04151002c940c2d580c9100d881c0e40c4001a49c4151001c80c080c194045d400908140724502101901e0b503d81d580c240b0b000515001180c0802455200ba030f0b16000b5400002d01400d0040f4072800700c0c52240c0081c50b200c00c60f1089054111280d54000a0001003080301c030060b5554090464059030300070748440c0034110070380c01c00e0707150340001ea0400c400341e4903001804150550402e0a2a1905000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 529011834 1250 529010584 529010611
    0xf0f0c0a06090b0d0e01020d0231050303120a0e0f071502150604390305010e0c0a121b0e031c0e0402070503120f040c08030f03040308181203 62
    0x41d407600300ca002034184280052188140401c0c0c1e8420341d183c1180702c00c4100c2d4400503003001c101c503803410220390012001016103850381e0700e50301d21000c02966600d901c14500700b0090000f490b09001c03035200c2c401c0e94400040d0010100008101510561190020440d00c904944020340320805e01d598602c00d0b4050500307881c079032080303200100344002050a40c4411007141a0901c0c0c07034040501000c0d0450050201101520240c1000000764500681d4079048065282000c20400f80a001d411030700180c01c05540703031041c0c0e820000c5240145049845455891402c0c2c40340c1d0040080d0b100041982800c1c000d01d1205802400e049182d20544441c0400303011003d50703c051265170700781d0907018090b0400802044903071041e005e80d03160503800b0b0038101d409070080d40d2605404207042c1e110300c2411109002400d04800a12080c400c8251600001e020303407000461415003540120b88460000400007400c2110705400290301608071024080c1d22002181120103000758a180c1240c41c1c4c108849400144c0790 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 529013084 1250 529011834 529011839
    0x3100c022b0840050d02030d1802030c2806020606040b0906030c0105031b130303030c2a080903010f090623061e03120a02070e010302010e090402030f0f0c0a 69
    0x10f8600203200d04a201c03206a004081108586072100901005a074110000014010780403650074000900800c0072580075595440f692821402111010441d83c406002606400c03001030b2000240151b810400315111010b004441d403919560510f81449610314010000c000103400380c0004000307002c0c2e0011101449030080103c00e02000303c0c001c0f07800741c0c0c0c154030848810040d540030750010351700906008211306900b080c01100501c00d41c002c00322440c00d01c4c0d07181010414103078144164a906c4129141100300c0d034219000c06070024840d440000310900144010703908010b85002155000c2d00040c000b44442c002144603800100040c0d002035130054100b0384021502039500ca080c0c0d8400c5802288910310b038a86d0001c1c441c0742e10010548000c00641b0000c03800c01550100040c1070b1650401c40c14554400d00c40b00c0007810021294424021001100010300c0140c0e08600b810841040540c0c49001d10b40d079600000345000481c2c0c009807140d000702102d444000c0c0c0040383c44c0d0408030084c2d8600c100c139503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 529014334 1250 529013084 529013101
    0x80405100b060306150c0102130311060325120c020c010e0303192f0d02011a060a182d0e01050d02240d020418050603100c022b08 57
    0x101e003925801d50000701000010403a107004450745500c03000e141d00960030300e2600300b4010300b2a801030b10f52400ba140b1100c41041006428082d01c82d00160551b803c40c00c500300502a1082102c2840d6400e001043c0c41c85110740451103807010b0340c00c0304079158042c44009005130001c0c1d214075a5040070350008403500101c00c0c43d814004122455a03462040682c820300c481032013140c0b036070f40072042c078402c0c1c8078118003030080c02c00c403841000d0034448031070081e00205449110280c03c50303000f6040302c0200400711031940182e54600d01138861418032403c109205401030030750454440181e81245110762000c140000c42c41640f82d91980c580150040c40500d6580c548800b042c1a0409104140c0c3c81041c07012500010304148904000d03040211400301b80c18821240e0325500c94025031100c6034441c0e0301040802807000401c3c0700c45541d02107904d080000c0d00b0310354040390702c900c6051030410101c3c0e240d00c50441c83d54801c118401410b01c5a00341d070486070380c9050400041c44880662000040e202a000c00c407041d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 529015584 1250 529014334 529014341
    0x31006081308030712020c010c050901110a1205030a0e060903180909030313020a0b0315010f0c030e040c12090c05040608121204061d0106080106080c031e0a080a08040510 75
    0x11504002d01c241150754402040741d82011001400321115024441c50701e0303410090065410300d6545803142e645501e0407100051240400311900039055101c000444081081440c11040c4101e41d0b01c0c105503240c0d01c10902c50090090351400c001d44d4450b0000704094078401201610703c2c152001c0340c072011040b60400700034000030181c0d40003034bc80d00200f020031040c9100c0d982c000d488030701c09040503d505540d640412000e4100301c03100d0812801051903040b1039079014080340d003030305018180b03103900c41d055407002030103255801c07266409030755504501c056150060650740c0d6039040f150010300080c240c41c60001c01ca40a540308103405541070907404500400007103146045042039001c07142c1407018880c5503800841e0003401c195176940c0d03a20446444400c090310072041e080010000800c0f075514203004542101c40c90f038803001ea26044034071540e48968010501c910b01020941071106200c0c1c00c2c00c1f84506004c2031a200819040c2c0002e8a0010796410110040c8220300500503900030a84401103035056 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 529016834 1250 529015584 529015621
    0x70209040528031b030201060b0403032102072012010c051c0203010513022506150807080c011206080a15181106070c05060c010212060d02060a1407020603100608 71
    0xc2000041040c0c035664604c241c0030b030198040d20010488036a0741d28002440d6100e9042540001c110145e806182c2c0350701d1301506441c0a907400b0441c9444000e80301c0605010001035400c0700c41524030302e00440c9680d003402c4841d59a4400740200580749100e10003404580c08540e900c01d82101c00138400b40703000030610070303641250005414400034900c90313480740c0001c2d841445008110f84030384081b000591011038071114806c1c80346600198004944c64581d500855a90140301d855100b6241406080320100701d00c0c154803002c0c241036800008540d50388018004a0b08484c0c4107214100d160f01c10b00980d00c807580c150249440c020459040384800740e12000281c01405415080206020086420003000410105010304401011f4075181c0c00058038951003a211594642c1d0040345c1e2800c0b10032000303012074122034101c40c841440259030340850428013800200a05001c0d050f10190500a600d10854007040d40c0100090b99920f410b991000d200c10240c0103500c0041c25002c0069000301000c0004d000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 529018084 1250 529016834 529016837
    0x15030509071208030702030c011425120902130903020115090c05030612030c0a03020c0f030303040b1b0f07050601152d1110020301030b1e0a05070507020904052803 72
    0x5109691107880c03030744e4405010281144001c100061421f03030284030303021980c078603070032a4000b909000914050149040c800e141480590020311403006400001015030980341e0700c000720b00403207980000703490000c071301d40d00d401d00e2400e14030194201941175020f00b030300c50741c03185a41d589070751500c40c03000446001c9401c0401107070023000802e80c1d88c0390031071a00d800c0c142094200d9190500b1403600500f460481c8004801681c0203010056030b1749004a503101d04210154003e508ad46815220b104074800040c103010b442079144c0c1f91025100143c11f0403600d04030042e41c000350381d500c40d0307151059540d8403d21a4011010481488661440c0f0400c490b024615058040314841700001083c030a903400c0c40300c294000d001c6e42d144c0201c0200014000b8140320f98106c14010f84035891800c16649800d0010050031400d2218a50070340e0700d9903640d0b0172503000794442c08000780d184d0721060140c0d46481010406980090a403007040308201001840c007002650741c81c022446000389107064070f40c004042e88020f0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 529019334 1250 529018084 529018109
    0x70c1703071502210103140c0303180f0603071d01030504112e12050106021207080706061d04050705010302190809030405040c080901050705071e0303151503050907 72
    0x1000c42c02c40c40080c41c54100303640c0018601400240040602903412040b88402c0295030b004200b40040c0d900041282d001d0b66018100259449000a0300c034030500a003d280340700141c00117540b9403240c0c03500340c200300c07000381c1107a03624241020301515000c403104410900308640000700300594030034080e5a0040da8045c2c0f090107400810010894000400c0100c028440321400c0c040c0b058110548000c900d031031705500c90103d45910503006100f940d60580080080d9440281e40802c0b0103403103400c0b2048a60054809600c60380703145400b00160a8075800869582d00b00340c0e448980c0321038292003d001c0e52140c0704890303620303640303e00540a078051204034410000c0454401203249000d020701943c04a41e0b41c00b03592400d5156000030b411140d035040d1090004038640100540c46d8400d200e490381100d10382c180300c9c0c03d048140d9500340ea40c6501c16069070260301e00540050401d8041c0e000100c184003d040840310980e21403a8980b8030300ea00d04007800020381041c001c05c0364000c000c00c45230b0035100c8100492 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 529020584 1250 529019334 529019347
    0x120f16020c0a06120f06350304030201050a180b0910020c06090f220209100c02090a020f070c1e060518090405030f0316083711040308070c1703 63
    0x291103062031400c28115454641078014988045445440d0162031f00e10b0505404c20341601d4204030200003104c07d80b00120114800c00d40781d44000080d6811a9030910700142d032201e07015012542c9807080c8210b000740a01c2c0324030101d603002038400504040b02c1d00791005191980d080c0800c03603036911342e0743c00e140c2c1013141002030801c1c0d0b04204000b520390780c00160100088031844810741e0300075920756600954066010841d0704081c03625100864500c00d0f5480c01c548100102d4002902d04c5901412041e02d9550004002032920b40e40703410703039048a81000c00582c006617642e03c01c03e1f11004000110b143d052400303034049206c90042c0c0544201840c0c00b0390310104d200381e081c10b2100c26180a0000d903903920080c054034012381004802544581800b0085080014044c071002e002c600d03002e49540d0241110000881c0c030381070500790b849515800e010842c0008180d130803150000301601650100d102c0d00002e000301c180101c3c1e400030300c1c1c0740d44545002c0074a5982c480c8840032602210302c82d1040358000b008031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 529021834 1250 529020584 529020587
    0x30a0c0201111504080c0601060801060807030203180d020607030b1512060109050a03080a0915121e0c030203090c04020705030a140904020703030e010f0209030a17120f16020c0a06 79
    0x22000c1c1107030030b000c540202900481c0803400d5002103504580c030b0440003a50244241c070600c03002d401400c0c6410103900d19410b00001804ac2c0310004c200608150740480000d9110041c041003400e20702c03c00050341d521102c0160025107554080b1142004079080640300d80c081c0c00e0100300d071044010381d60406810000110b441d00b0b20346a002c0c05003410010208004101a500c035501800250301c00c1a0b20380c0c1d503010f502e50251540c00c2035400911804220000105415000fa21038240002035203030001d280e60740c0303401e840c22080c3c004d45540a824a05a84400b6090301030b0300a6000341c0e0908120b074003c10014080100780c0c802d511000380160404d2080e002d020340142c00303210303486000c5100d450a0000180c04070701241c003e1001030300004e03203e0921100c0c035142803003103002c01c60341401d040d480e200342c840119560f01c1c50f001340288a8140c520101125046110541c0c10900380360000780e646041c1040d42c90702d225415079134101070403460410542e1050000607440e81c0380d94041d02100819140200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 529023084 1250 529021834 529021847
    0x307050c280f0501320702061506090109090c050c190c17010609020d050103020910050a05120a05060406060302030d020d02060106050304030c1401060f08211605060c040611030a0c0201 81
    0xb011203456495402c0c0302d81002e000f400802205000440018080040208003a0b00c81c101030480001d5401100500114644901c00896800d0f0242d4100380d5a02004004035444034043c1d02c20006c0c03d1501104548582e800b50062001041c41341c1210f02030691141c5003820041c0d460070007072120340c10540030407420642060000e107003104500000360040c1ea620002c0241d03406100032102e11680c1340014021403800d1070b00d82e078022004129040103c0e04140c041144510140152880380300040c0745d002401004000c5121400c0c2d000c416619242010f103040c0c1c3c082d00e1140402c922038000c0500040b401440003a0080c820086940140320b10b92801c1002d5a01e44c0c0050025403c0040c0081c4c0d020101e904045044050380d420000056444d2801113454508901c43c0c0045002d60405024651000110355082c448808803004441e0b9658212074031001001801c007004005000d080c0130000b4243c0c03240003800840d80c040c0c64201010003004440f545034030a1254010110300e80c842c07480c026520648 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 529024334 1250 529023084 529023113
    0xb030106270e15040c0303080112051e070909050a050705010804080910050904020a09061211121003050d020312131a06130f0209100e09180c060307050c28 68
    0x8103583c4010348003400c01032403900440d4140d03142070b18010100101075001581500601d51f0308100100001940c0d546034a468040d80280c032100010f50440003204414085180208200c040030000b0070900e2901940b81d1109030000c1e22640111100061294010040d061243e88e20074111407030890107808014450508210140400c041848008843d0b1a42d10003005108a15242c1c05101403a00c10000c101c04018500080b001d410060101032180e008000c0e900c0700c01001e80c5e040020303507400c060740400703140a5101514900c01d040601c907a0307540200003131103d13500100c0d4180d410340d109250748524426110700202141d1180120b42054011034440340d800120007060002c1e0045d480c404001552020030200b0001c40c0c0c00111110240740c640b480300406901d170f080021070f0125060016505040091910710711a050b078004d8002030074184400764100c074004000740c0c2c403801c08040040c01900000d05a03c517601c04c0c9588507002c0290f48200200c01750141110500d80003c540d2030301c0d014240329 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 529025584 1250 529024334 529024361
    0x6140301181103130b060a0b0403170d150e060a14061b0d170a060e1308040305100c0318080315030c0a140306070f020304120807060504060b03010627 66
    0x504888111109040c0254025100010401c45154242c20540b904a00141801f0300c00e8546420402c800c4402000392400c494015000c1c4410000040104842e0306c41c100c02408120b1400c510819480340755240f003c10baa01e440b16488150b96940240300c2c1c10091030203100902049004894010300d07000008086ca4040f20071610780c02802103400c903140c84c05040f00c5001052403a150300c80340300b42e000c114540c8039061038014030405160042038074404201900d111514032441d0328002c00d2000030301c1250025a0310400310ba000000a0140b40c00814101135054001fa00b088200002d0080740391580c464140c1020825146440f681c44154081881c190341d039805001d04840f40c07400d540c407588101e004000d002031945500c2c211782e08041c10300e28010301c030200b4403070b02c02e80725045994000150b80540380381c04000c509003c21420f101d00e0500900d880101424203140170042000000d400564940c04281d0003031142c2510380c140140c6080c256a040349070303103501b85801740b014680c68010f0065503040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 529026834 1250 529025584 529025591
    0x1205090c04151a07080703080705070f05030405040c0507020f040f060f0807030308060909070e040201110303070c05121204020d1a0a0b0109060f080a052215060614030118 75
    0x190001c03405480c020741c905035220003100e03070402418850903507032001c0c00e030443e0505281552568841d4594003400602500b04010780001941d002e000d0b104440303807242c201c003000c0d43c00e5103a45011a82c92b8444c0c042c2c50300031402c0810400700140100c2c161503005d58014050b220050684082c0802000f00ca201c1c81c8503140caa81002951003800a01b0001400c0c009000c0e182c15815424050005940a0300c2c10703004840c060104001140042118000d80714803540100c400c3d122800100c074108403401c1d82d170119000010601c0705407600031007044103140c031540c2a80c1310b003c04002d5034629130040400c410b8041d18200b0000c0e00618080c08110f072510b200e5070b00c1c3c05041c4000c002c1c00700c040c0780848071049556598081d0418179a08501108001c00886c940344481c8a200d100c01010240c0c0a014001043c0c2c0380c80104c0c14454000043c5c01145103024000c040241c90f901708540315800341c0d800999510310f040300c0840d1452158a41e510540707458603008ac9980d213848200c00443d075802012030b04043e81c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 529028084 1250 529026834 529026853
    0xb0a061d13060602100c05040506030f0601140c0109022e050702130507050d1107020618010c170d050f012105070f1d100305060a02210907031506030201120509 70
    0x200340c4600310141201d9802030614080d4402060111007501b141c05082c08404e00c42000f065858100320b80c1c1c071004495002209889000c01070701d08545010180390303a18000300d41003040340015032018030498001c0b20b880c1140548149541000d03c1c102500c900d1640241e214090214001d100a06920740b01404407000c3c1c100c2540e82c14210750080e510710000070800160a0840d51050180e503c2d00c0c0030030168280351004660005480d031090007030340c4c0c07540008142d4a28542e80141045801650000107007176001805e44d5544d00154400c0090040302454600818100d80f400d0ba052f505940417107050031440c642d007070f038125480e04820310100d50724410240041003500e00c40b8280402001c40c00b10141021820f402c8410b03902c3c80081c8800d17040c0910350000c00100d040002c8180d0891140280107903540350303040044549130342000d2801150f26801040c442090400501d6004580c0904622074528041c000c0b402c007922058803000c2c4c00104000400100c0031029030009800841c1071045404025 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 529029334 1250 529028084 529028119
    0x18100b0a080a0c050312130e060f0916171b0f190903030e030307030906030b1201020f0901020c1c0b070926061f120c17010605040b0a061d 61
    0xd150080803034010600300f20130070083c10100700c959002e02c8a04c0701c407410001c4083c0b005102080c6441030710030904126010a075103468200e4030006003000905a29054900040b01c0c600b8098440a0031001401001c00e030001200300c2030a550203080504400030000c00d000301d0380d403029004280d22081d62030f8200507402e00142c800300001780041d020f4642180903861130170050030240401da040c9000e5002000321400080e03100100b54203650039804c0001381c0c0c0341c0f85c4000c1143d0303a0312150001c0d820741c8001031413612981400060249100c0980c2201d229017800380c18071041c110443c50704a14040c480312420002285131800070345c85040c2d490540000342c1d90728010300d01041c0102480c00050701d070060703c40e5801b2080c0013442d03000a0220170707200d000750301109540420204c5e21624241000351025142041042e02d2180014240300c4c0d0312440c01010801058000c0140d4802c46100d030f17184c6100d03c156414110041003c44a40f82c450a000340c0c10707015104c40c019001240c2a500c900051203460425 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 529030584 1250 529029334 529029343
    0x13151217070f0c0603050403200309030102041d090c031c021504150614030c040b040207080a110c0102150403110f0316030e09150d030c06020313020918100b0a08 71
    0x240200881e40074400d0b00d041ca0421480d483c0c02080403d82000100b002184d00211440c031a403890541d1140604480b031210b5041d80101010a40e1650001800080d13600540701404122001c00020000760f451704540e45582d01e8550040d250150440081c4005114402c2c001e510040c1c1c0702d0040d039203540154000b141c2d03006801c440840c1c14407001e007029a180c0c0b0042c410b81c0041c001104071140405594070001383da90103481000d80c81292900ba11a08a03101d50b01940c01490380009155124500d96034003403c242190ba98030305040c03061294200840d8400a04204c454070700411b814000d031250b1310115000c0c40070041e203a0342c5204035003070703505400c200304002d0000c10401c1020384440030b86403030000c18034070810191500c9582c00500340882145072100c088841e01c821030b030590100100d803034282c840b44550310001c4e20660ac007000700700e00300000305900140203200306c495175851ba45031030310341e04900319000c294090b40e8002e201c9210100115030000708034010003030000c000c0e550387d1002603140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 529031834 1250 529030584 529030597
    0x403120c0c05092401020d080c0c0304030b07030209100302040509072601030506240f0603041a070203040302100c0f1502040503120a0809120304031b1a0613151217 72
    0x20a4400c071681580c03c141d00c40b00041c448070906c06850004440c0100034a1b0050290414076a0000080c580125440030401c840046501c175107090101e24006030050000c1d001010b00b580104850040005464400e10071941990304c0104655074649070b4200c01c894800b802a121528012000644241400c500044a0003588207000411207460320303001040d0008580343c031442c280c01440c1507444165880310103262001100b5610251640e55070301705800500d04010398000f60940f24000d0052031603000c40140260ba000b911141d0050440b480c00710340207a603102c40039100d4130346542c519000851154004807200e5820a0240c02c00d511800024208035038060404412000000c40920b12500421400e81c0242404003030000c001454078540c20f9807100a000900300141812030a2020340a1400014020780202a41500881a140d401042e00041c1c805610448000342020665251400313400d41140050b81c01c400c00350f10b4041004112445540201c4400c074200740b03118591851100907020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 529033084 1250 529031834 529031851
    0x42c03040f150c051609060504060f0b03100f080703051e0c1201060f060504050405010e04150203100f090c09150e0d0203101107030306090b1c110a0b0a020f030403120c0c0509 77
    0x1707070103152a015004071616588554010350811208006e1003126041c00801c40302d00109050f9a80e44800040001902da41c0004031700861032a404540341c1d10002d584000d6070302c104121080000312004140402200740780352607070b0380d2046040d4000360401101e940d40e4920700c04008507d980e1211246070b004882600a01e00242c40400c1c10445440c05024050043c00010200d00c800d0500342c8074680c04000b06e20f13201c24050307000408913440310229800d40d401014003402d020102500d0716484406042d00c2c0020038009590a8004242e800703030740c4804650032003a91034101044540105112001102c06400e03a03040c05000e400c0c254040e22401002e0400d90032107a0346903074034003910780901129002e402c645410707450b00704008a0798459400d40304031034101559440285d080b0389040010401e40c40d98064001d2000c5100168010b440b00142088024a800703841da8a002d80007850360fa8000c500c405400b54001c100103d9080740100021881503000d40040d80d02c1545030008101d900000791079000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 529034334 1250 529033084 529033123
    0x40f1716081b04061a1608030106032a05030118110c1e12030402130f1a010e010c02030d05090109031a0106090506070f060c0509042c03040f150c05 65
    0x1040210640902d004082d0450b400c0200c0d5040c01c1140e2500c00c41601c0302d400180b80099050081303055003144508850340320100954a40c0c40d80d4000b030190001d66409040c1c00592210180e00703226440308805010b01c160b5506085138a0071400d134014907142d0b45030340c0c1d00c0355560400042d40440c8400901103110100d005155501c124600d8100400340e0a80301c02c9542c01202c0920712001840381202e412540407215441001c0c0c08244803002810380b0705031038501c40c0c503142048030450641c045141030204240ca4450311400814015103080400400003175140e042000000059401040901002941072410061050702c0381d0310300c5260165015004240d54220004001145c0d000801d400500016500c0c40d00703004a80e035400e00d200300c000600800d40c6071618135030b10032284200d0903a81702d0500140140400c04501440c0c880032605500f402040e00c00f843300e000810900002110308403500000c0803c060b40c0f400181214039032681001c08100000707600c154011800820030388000d003910a9004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 529035584 1250 529034334 529034353
    0xd050109050c1503091c05271e0d020d0516030c0305100e15060310060906030b0609060d0b0601020703060f0e010501061107031b050409080301090c0203040f171608 72
    0x310603600c03a100c40300f44060080041140402c00421950b21400480701840d01d001441c90b8140e8050040c1c0c10540ca2a5550280403d140d00c00c110380000440c90603500184c01c905c80060100285402108450b0803801900414005040c2580403007101c83c0684160307411000f00c4140c80001e520103a2041d0b03401e5905501c01d006000082c0980202d10b40023200411189010118103074072070070346659914000c0c80303100c005025610180a04444105c24000811074540c544407404002c0145020603940c0200300390004000b81861070495000d110700401c0c5ca001049980d503a503c4e84207004041d03a045010301080040003402c24002c05c0020382c0441000708051001e03090850854105074803c900704031400b0303841018000c1c041164000c0d00e8011130340070f00d03821030420881c51810b0b066000079009881e01c0680b000703001c00e103405541600c170201c406011022103174904031380c1c1380207a00413056000d04590b420070000400c0c95681300f08403c01401d980c0b0040c40c65400c1e10313041c003003548102c03d250042c8004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 529036834 1250 529035584 529035589
    0x312060609030f0f10060f170106050901060207032105030c0a140a030506011e09060e0f0a0b040602120702060405040b011115070e0a0e070f021005090d09091a0f0d050109050c 77
    0x22544511700c1ca50400817949840f41074000701c1c4c2540f0034184500a800040c0504600079003168001d800c0260170010903507500c240080d179070480752009840001d8030141e802100720f9441415017601d5030301d986d1581551641c00405a09030f0001084005014401c0b681e0070904030018080d101440c11524001a10303e40040090f003603000b0f14003501e40308134003001e54405007030308003508a09032080d40c071b01043e2084c24030340404c0d05981c0560715641e21014904000458402213001002070358910740c04d5514000c8054020b40e004e015a9400a50040d010320040c00681440d5001c400204030500d010000c074020783d040070b42800210440b65405040d000104481c05410105100350380da41134030b210481601c7e01c10711030380128018011504004640034807040982c03080165101d10055040204105d04000b00a2030740c4170031a50700d00c0c0105000da140043c0b03110390751056017081e030001e101c101000350218003000741188d48ca4100390b5002d40d4182000001c200c0c24402d06200c14410402401141c40c210308 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 529038084 1250 529036834 529036843
    0x219030504230d030e1203031f05091509060a09021201080c060906032707080601060807050a05090405040326150a12120221030a0e010e0312060609030f0f 68
    0x2105848030034a281d40001c0ca0f152094021402034042c541342952810220005003507009083c07504017648404014070116007000c961642c2203280043e00c00340140d985000b400440041203501a98614040f51005400d003080701c80c1692048004003400b14150301c500c41d20701240c00541d00c072040e0f50041d000600046004000101014078111381d42402d01c82c114002514034400140441c0407609556422050301c10480070003401e141c8900181c8070410784903004a50345800c24400d070000030b000500861003140c0110222910454540d4a84d858401d1400502c0041c01001d4421802c200300312041000841c1030450103250741d402100c404102e428000b803024880ca07072000500b4411015040c04202c1c11000c8060f5020362503200c0c0203058015032501059007021001c600c541003906600d03115403080180032004522440c0c0390a0100b2940c0e0a07840342a0813030318400ea07040d4043d44108800155144160352040d427000008001030f103004d01d40c0b00402e05180f600c604200e1546d100d0b01c42203605e00010302 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 529039334 1250 529038084 529038119
    0x90103060902030c0d0f090f031d010912111f0329060307080c0d090b040312090507050111010207080703200f07140102030d0501033e060a0219030504 66
    0x41582581012454400a4403c000c14554020f030344d8120034441b10302035002442c149401c81640520b000c500e081c007408260540c0f0107010a5018451246038640c02400c04c03609846070000070401407080d9a07226038941c84000c0c1050381c0440640f19078900055000d40c4158030103680d90b40411245140c14026a0320504030001030340010321004040404d480b44c02c20340c0e80c44055840c0c0035025440f401c240d0a00c600c0750580f03c2e07400d1800c01005400780b03d04841c031785000354445d6a40b0711500c0417a404e00811113504440050498003c3c6a003041950311664075603801000400c00181340900c117a0340c0d2059584a14070441c04140716120b10750005485408240090210a01408040c00f014012a458149a0252030000e60f8101341710380181e4800c10944150b0b82c3d080c8010070255031a0308050b192082c01c13812501c04d00740060300c404c600c2d402c900c010f5054240059000c0e01c07003140b142d00704420750700140001011841072040307805500781046091b00010b030290b16165991424408551002064003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 529040584 1250 529039334 529039349
    0x120d090602011a0609010311041a0316050c06040b0903091905090702030c150c07120309020f100e0d030302131403120301080a1112030f0c06010f0602072d080309010306 74
    0x2151205068844c01c0407030f15003250910340000c3e102000f4050320190701035904406018811703002403070707100d012030340044d4040d50341c0001c1200768001980c02280c0078411040c00401c00d404c041d01082c00924040c0f5801e80100d80a42620300f030401c0305001c00d00003c0e8804405c4421008001c01304814203000d03030010341080380c0340b02551030711040840b840e59070004115444405050382d00050400741c43e810584a045601164460f40422406030040c098401128180c0c4100140c800e05140d5207402e00c0081e0f0400101d454010304012450104102020300d9034054091503002c0001c0c60350703c001000108090303c041d04a00c4c1c0b1b504428000d05140c0000190110f01d10402000188000c100000d0300400c1541c2c44018501c4c80030420f404100e07140d69000a04460340b2001c02c500e42411110b00c09003142c00d0045003180c541d03a0fa1072216803401d100300d114503009600203c02c14007100d000d090304001c04c815503020941c5031140032900d8014883d05940401941e4002191490f81507900d40211401030489 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 529041834 1250 529040584 529040621
    0x62b020406050f01080c0a0201200c0d0305160c050f0106120302060a050f0f190204180e010204030b0c0310080d080702010e1c18090204030b0402090c0705031602120d09060201 77
    0x3100217401a0405428903080020102e1090310692003500015204014a01886a5143e1416415007241c0102d40100e542d40100c000254102d44a4464a4840e00c52081c100500842001003030342d00c0d0408000545090041d03448009003003109004002c0107181600341000d08041c40c0c01c00a0800340017902c070010b80c0b401c0000f40600498141869600a5164020100b90f03849000c05a80308015007961070050a0000c1400070754269818031034000760790740382f406001c0840d05600c803038205c0c810b03804010494100720b004146141145801795502955003080809600d44407055145007106421540002604031010094403039421301500c0c0c00c0721010390062108142041c0c0486c1c2031501803060b9000c02c40601c2d640070a24807800540001004909030444d0b880c0d0b16030404812450044030213a001c0e03104000420300c1142100c089801264109001d10b042c89080002c075042184000b0741640c3c031100500e1840c10003441030000172294280c0751144452146440c40280c2520074064130b0401d250f84 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 529043084 1250 529041834 529041859
    0x21804021813211101090b0c0307140d050114030a0302121c0f050412080403020d031a100c030e040c200f0d02070f050901030206070b062b02040605 65
    0x160781d69807503110454110301d441c0603514440d508000615941c8040d204590080e60074203503010710500741c415040b0f240e03102d090840b43c0e5480142a1081010004d00e280d40241c00039950b02180d40185820442c0c0c0e150803441101c960490003885d8000c1441c62880c140d92728010040d005d06d401e00e03101e0b0b550782a4040c000081040e140603444070310407907600b80c1030400007480050860080c80385000340c402c0c1c800100010200c00788081c0c01010304882c110b840c5880c15100200c100e014480440c46544d041e80104500d0070322180c00c42c040e000600030a2000090f2a403245140d0340e07140240110a15295078100380c2e02814100104102c01c603216090182c1d20304103022004c0d0354800d010003e403038910801484010030400e056490101041c940001500884c141c80500d1680802c04000304c4000038100d0042c1c035214030400544a400784402075000004100010004100c001c2c01c6520240c001d02e01401107c4170654414114089501511040d80980d07030007007185028450b070700207080d090f84c80050080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 529044334 1250 529043084 529043089
    0x9050604020d02030c1305090c2209030e040507080a0501140f09041a01060c1a0708041103122a0303090c09090c0307060c06050a05061003020a0e0d0c0302180402 71
    0x210140c4042d000e444020b01030400d5440420075001d1488000c0c11030b20b220560313110000001c0109807240c03281030180c2c01d040030284c58011f1204c2c1e00990303070041d021503200c0310700740c0180101005c5a08a00344240440080d4040c2e40340d1045178420205a121090f45150040c102000c582c0141c2003000000000b291004042d02c0710414200311a85c00d40301100c480c0c4403410a0000c00c0ba00d6034803030011485000000c15007d0788642450141803096840e011800280701c10641720003022507140e0b0020350004000f40c081050224044080d00b0050192000134052007412030781d541c00110307040c180c015910003690364410203a80c0350b00c5120041020b14154208010390940ba0b000000002d0310514091010500314001841240c00554000b0200d459071030b030704c5402138034450482d40c09480040c0303840300007080c4102c240941d0344034a0000345081800290300d003080d8000e40102c06184204150703100e030600b16446130240444c21a0207200c40708011071441c4100102600010804199070074940c040c440182c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 529045584 1250 529044334 529044343
    0x40305120a091709120f2506021c050720030f1605010810080304180f3806030a02040503070f0321050c060f010303020c030c15030a060302060c010b10030905 69
    0x3c00a082d0280c0c1d640d00e403180024400c50880540c1809402200e94940c950304001926481d00100070403100380c40c0002d9500e1110180c00b40c0f00707010241c1c000b5400343c81c01c141c0300d01c1120b01080032804c20504003203150711034818070f841591181c2c0d52180500020401881d041041c21508070b1141e00602541980e80c101e2203681a45200307050602010f10040b60b204a074043c003032005001340c40300320b03500d0f00e0b034803030090318500610b810f1201c19a28017240d24003488a50b008004525190036003103241c000392b0041c4050506890422001c0d03020095084a46a65841c40114040e542000340981c582e0300b0001050300f8a034150348802503036600d601d1b0400c00144240680c403001c0c90149402050b0403541241034400740b06001680440b40900b000304003600881c0141e05050704c0c000d90881d800c120b40d440a02d03a407200c242050940c051100c0c0030803c1007101020045034030060201c030100304030360343c1e5020a03102c2d0060704440d201039450f081911810704014a100324800710525080c00703030341d015407140c03170700e5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 529046834 1250 529045584 529045613
    0x240f08070b16020a05060703030207020a1d13150c090503060c0406140f040f06030906200d05060f090405070911031017072301030b100905012006040305120a09 70
    0x521114a4030304250f589541040b13000b0315000d042182e0b0340400d444c3c01002948085c800302e1041d90380e014007055280e445000c1c201c2006100e080c0b0300d22a1110300c01403403204890302040390134584e03514072046118240c0c06220f2410946e40c481c0c80707032103082004050406100a0a10003401011710007005040e50007016640c01003044810356507034455051309010144038a130045440354040304d034000f5240d41d142c1d00040296002d008100011141405000400104c81e903266240180a0251901e00500781e03100c02d812150040841c0101c149420106082050803034060b19641c11146080049440038003c1c50118549020043d01c4c40c078011802210420300c030b00850f80f10b0019042141141c90040220001800704100380700240d079a4203a6400710780728820400c500103418070301c80403001c1c00c00381c1e546038540e86aa250500018200300c0115007400425440130b186c1c01c02c4021402401d0001d00c9500d01490080d44c071203035a82401da000501800c0e01070459032142e882d00d880c107004954024204d0340b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 529048084 1250 529046834 529046857
    0xa08090d021e03070b190e0604031d030a06060b120901090c030b1e0c190302030c0306090912070503070b07080610050f0f19030605010810050112240f08070b 69
    0x1042e0100760351545940030f8500300900c0c03214481e052101d05103261071840350180d0303030030418050140030394100c50711410180c4004000c5546114200f040710100921800c2008015040f5400e18802e0344908040e03d1890340034800c500c00000d039911601c00c4111410f40c0c00001e1070001d00c1503602560722403120707130b5031403002504c000c10201c04281009602022004a034003031f1046000542454021700f00e0a9003d43c03184070101c1302141c0442820350180c003e607841000300075800c500b140d0364601070115202e07004001010501610042060a0480c507001e0451527004200440c1c9a01081c0b6245006904c09032000d82400246410804150740e03450b03114818040624000d5141c0c420103d140385640280602103280700400709012200c2c11340706032026000c2c0b44039641485030703d075244015102c00b01d0030b440008198160800c148020f5004050751036000220020001d20035070a10343e50001120b5903c001091060040340c1003100c2c0141e14610070203042c40501414056140030b014001510480c52940d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 529049334 1250 529048084 529048123
    0x10110a23030a1d1c1d0901090905010608190b0c0405062d0a020f060f1b1e07080c0705010305310605010e071202040605030f2a0a08090d02 61
    0x101e02106881001e611404079030300311003408071084070503044022543d4141002452103401041d0700c074005010364005c0b01c406007554500382d00b0521648003409a1a01c01d039265906c6480020382740408004a4084002e409030605084000d031074070b0001140050402202c0640c140401d002e6651048103e50080c0b407004100220302031991502c0060840c0103452102c06040407074001e8a030750700071920074040400300c8182e0b642c031303501d000c01801402c3d815203140c0c0b080c0c61240c10750207541c0388000c020b0200d11a4140091440101940c00e181250302500c021103081101203100c04520310200141e00150809003014800c91030f0809004240d0030b81300c00352550000840d108544041196448441a25040b81080c8500d6850b081408100041601c3e801c0005043c0310002440d00014400d4406641c002d9540300e246840380d41d03078002c240d80080c0819400f814094020141002c154001c500d8805008260b02c0e10340004800c0680700f60310080850140d40c1010b80301c054415030115403032140118039101c05 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 529050584 1250 529049334 529049351
    0x60c02030304032010020a170a15030305210709050907020703021e0d06112107120c1b0501050a06090204080a060c1101050f010e061909020c10110a23030a 68
    0x652501812040c240f895620024041c24a03651000a000754103406180c1c42002741c0726030f0095022611202c2222400f003403400da082c40000c0c03081000389400305c502c101d2170803402c0210f82c414110348000e8640304046003051004205608010340c00716030160080c0040c2c07028500e943c0109800369801d007443e4150820f0304528404d42c0d581c0507039605249421080810a10080c1e00348000d050703106240100c046110104540c448802400f0058802d080981d54982036034148805440507000c0b001c0c00c0d4040c41202d01e011003c030741100d20352002da01c2c025000851070b4186061545c08460b502d0704002e160745d00401c4180b04400002903400181a4404400102d80c108500c0855540001e11003030f00c095400d00e000d02801c00b0b214010302c0e05981d4403d10340b0300c07140c8a903000c0203041f44e203d03a058078240c000301d0000c0000181660140124040160546da07076800324065100807601070500d60041010081800d400442d4040c0400000c1e1610a1418003e41914181c070b44103400010090341c42c50f600c0c3c6440c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 529051834 1250 529050584 529050647
    0x60b091f0908010203010e1803040b0f03060f090a0c0306050a0b07171c05100b03040b0a4106030307020d17070c06020c01030e07211a070804060c0203030403 69
    0x101d00c028102d80c0000c549070350315540100600102551402485620a1004000000301008071030031590717103480040c6800030480001200e0380000700081d62029030640c242105031540d00e01c03c1d00c6151125000100341c00b400e030010f070840310960003042c05090140e60034000110100f00316a04540c010b80b1100380503c00351010489481501c2d1001c021000c54041e05c1e8491000b600400c1c000c101da455a520160384a40316011140002c9130054400c4601c0d40200341009066841304500300c406c0015100d48211402d440344082043d40320144000070302800d01e5601e410100e18260b00140210b024628007607841e000904070000000c8082d003442602c00000700300c0c0f4280c00888611581c007241641c06036568017400f0391242da419141501080c2840007450a400703011035200140c0701da41c41c00b610b81c1a01782000154001c005032080304c0d075076910b484d141c0402d5406c0e01624880d01465035010303103920b8503107000402d541242c1050000d55109100340000a0b8008400c80320f104071811840c0d11410f0039082 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 529053084 1250 529051834 529051847
    0x12100f0303050d06091d0705060a050706050925080f0a050d27090203010e071e03021e0301150f0203070c060c03032d0b0303090f040914010e0c04060b091f 68
    0x5c204181e51400000c040a07401c621403810b208505c004c140c030310f815078038800c1c440584291000140082c0d820042000003400d81d5100c10340226500c8102e079415920101c400703007006881560f140c440c444600041040303901c100200e400c000c00000141400382c007603541d00380d039500307804110000740030b034103403004030294003500045001135107660340444400e60f01c48031180254420b015a400001c000710005100318058200e0801c8030502d0500031040d43e0784140c04074002e40042c4805005e405035503d580f42000c0203100610301038240216400803001301c00b540034004400090007038044d5041803004001203003040d40c1501c125165424103117201d5483d46800c0b002003440b14004551050140051484000c3d00410140c074000030403001c22405010504055072401184c0016901140d84607003c2d40314109900b01a0885d8403c1c60b4110100000079100303804d640d05511402c046030b0080c1081c5c01503140502450300145120040107141a0008000c01c0784549400e4260a4070b800c91546803203498420b82 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 529054334 1250 529053084 529053089
    0x3030a051b0d03051b0a020a2022050928030905060a02060a0608031312032f0c0429030708031614030301120b04020303160812100f0303050d06 63
    0x8082e01c10480c0c8030749000c1c00070001652000e04060f808425403103100f4181d8100e0b03c070a49160018180280c8550710440241804480c0c1c0e00000d0080d0380d40102500c80d800212004640c800ca10b9002c203070550044c0c0c0417500003d0041029520071f0000c8001564000d082080c00c0e008441803a007614124182502d00c0601030b80460740000380007c2c440403413039000c18940e004002d030040c01c2c0302090381c52051a640e4015003651045e4102045c404029030344080608086403403080c1840148100440d208100481c816200c1d0505481c02c802c07048003486061244801000046408101c401c401c041101d100d0080d4000018540c100c4101c046081c0d41c00b0086000145507040c212903850088500703000340300101000444204220348085482d030032012041da41628490380c103004144075140c4944210040280040c0e805001c200804001c003a80c428043c40d480d03014808023a540c0115070003a44d000c88c4001e080341407003115805c0c240460240e0a0000040b69013500e8080d485031440d4002000504499 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 529055584 1250 529054334 529054387
    0x91806150c020a0530010b061903052401080414060a060609091109011202040504050c07030e0906060910050d05130c09020315060c03070605070e0301060501090503030a05 75
    0x4a0080180075404030398108024426182c00754550713a0340040c4241011200d20b4201148400e500c170603550544114030720000c0d055400081490200c840c0031a055074044000c01004d6034004014442c6d06401d801241d4000c2100003c4090900c003941c0500007081418070f1b1141046842d00c0403d0501010503180590301c003522042c1d4825051040e02d5200030700a900c40d4200aca46030b0480041c403c80244900c0b8903020000d01414602030301c00d001140c800b9a01000b5001c42c0754240404074542d182c07482024440e00e10f0010090303440c03400c0d0401800141c2d1154220340310b49071034410480242c4441090710f5208405561040e0505200e00f4140c0700c50207055074005039180340c4000c00a1400c1031401c40c0d02c40034000c1541c002900d450b0310461080c0c2c44216003920f00706859585480c40e80c14400001d101c0d902d40c04059030304019481c1e40c0d080c280c0b002540e00d000081c604d00c40f6101c01c0d280070f2281d14020042401c00c0c02c602c5180502094590240704006000e00c0004600d84042c02c0038803801c00d05802c0c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 529056834 1250 529055584 529055609
    0xf070f0e2a090102010e0c03190c090f1d0109020d021005040801050408072d020d1a0a0603061b1d0402070b0901020a022413030e130207021203030403091806 69
    0x104501000076400008400c0e00560800074000c240c3d00f00032070030058420f00034001d411482c0c01c0490240305290070b4102215907800203a000540780841d4405c1094200c1100c0d00461060041407103040d54603212201400070b6458000203100580d2000f0030018104e07810317110f03011000e49400058449010302d6000d84c0b115400c01c010407041000540040181034801c2e0600c10050b40ca5070007209010181c401210101600c20f041e44000d85000300c40d402900d80300d4484100d281e1000c00421240d003000769591010151078441c21310030081c4600801680c0b4105609441c030740001706900805034428402d11102007040c04005400300c3d155a0110b0340942d03044220746400d421724545090003580092a40c10060145202e4103406200c41c03d1000a4030381d81c841d03142171544071001154070074007001804400b4400400728020450b12801c0025156904450f40140c941030507006100c80d60000c10345a140c2034104004003c0041d40040106003941d80c04001006041c91942d1032200420054206034071744500d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 529058084 1250 529056834 529056901
    0x1e0f0d0606080717060c160c030303050702070e160c020d02030a0b0703050604060b07030806040e062a0306030601030f06020c0115180504021e19060804050f070f0e 72
    0x80a0700302030100e807680c00481d042281d403624183c00311640000725001070303040710000c41c800c0740c1c413040608500100210340c840c82c00110364680080e0b146030341c03040740407070340700c204104140d40c05011010080c040060b0b01c1d0340c0e524060805400762081020860b0a10031007203003a4055450301e0a400c0f90360b95010701280e001c02120300b00030a84a800300c03890b100007810800015540d00f064081c102c2100d1040c0819400d142180d5810381e00000001c02c9107400030356501d0940160001040320358000e00c1118492800314007030750580307021030ac00e200041100410410a0002e00c1e20001a01411203070000c000349400c108a207000c40191040c0d0072011001d40c01d018804c14103d420030151821281d020144507010440410300c1070503a501118083d40c0908111180b078901141c4410f8910a2314000700a094005100c0c08801c3c0000f010350403000006005004010801c241000030f001c1480d1740c1030080941034504188a103080c0b0f040d000e08140c0c5549a030108046543ca1602e01d44071016030f0f001e8038141c46 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 529059334 1250 529058084 529058093
    0x30b0f2809050613020a080103171c0f0e03070b0112290601110f0d050d09080f091c170a0e030118050706050f18060702060a030c030c08061e0f0d 64
    0x41500c281d40324100f41e0380c1c13904c00c802c441d108076900280c03551201e40c5560310390381320381400a0802c001c89090034410440f00d0004036801c0009030b0b022050010007c0c00f42c8520b01018102c40c0d00c0c941c1e401007507104002100100d022222400d04541e003543e01c0b074021000c1450b00c90504200b1000d0100c09012850a00c0d105603c1071041a200d030000303036201039100c56a10502692035002c2c0901c0f0381e40c1c0e0132420681e11458070a5000304030301226194042141501caa031200e82a07030014148008195010800c2c0c03425182c010701c9810400e2640c0c0302c588001d402619418101c000105203c2901000040da000d03c85001c3e0034101441c190080082005201d01a07103c04c200301d038242c0844940c000e2000c00720b80140203c040da074442d50817030b450f541800002c0d04002d2041c0c05540640f43d1014043c0403007001a0340307000080c01c007418169008200361102031400380076200031605d07110074002250100005078803103d107500451400c9a0705491282d100c000418002000d0345240b40e0800c480c3e200800500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 529060584 1250 529059334 529059341
    0x1404030b04051011090415080d05041e03020604060e03010b041407230a030e1501030305120f28090507060207140405070c0305071703010306060510030b0f2809 70
    0x210b00403030544003003030462882d03a403c5400300500455040c0e0103115030551420242d2090b15890307910341d12070780780302d0304c5489040c5030880c000c500f03d000800005040c0b02441c0c00d25003240000d03800358421907000303080d54000b0b031182c05580030341401c0015900c041213a40e03030250020281140080e0042015600c0c461445070391610486443c0046503507555050004070a80e421004101c02c1211103d04222014804074041e01c1c0700c0d0314a034150310855072031400001100394014003c5220703407109584e846107480992a100401404170050121000c10410702074100c501c40c032400c920081c13400741102d06d4040020700600d880e4401406600c108400030800350340000e206016183c1c0c400b440019807004a0422081c0c503421244080015030907285000000e0060000c1c2010318490362250680d40000c40c0c1425030f40c4c10980c030640340c054907050208a142081e1820320060342113481d041c82040030800c04240380c00e400c07421040c05003080c46807100c00700c84410780c0340d0303428090360b400b004444d0783d01c0b501c01e0041d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 529061834 1250 529060584 529060591
    0x182806031407080705010e0301062303100c09030b0405010e070311041808070b22060b360c09031c02060106020a030903081623012f0a1404030b 63
    0xa04a040d0451459401c0000c0709000c865201c0010600d10b800c2000440d00c1440c2802100d8042d0749030714020680e448034509050000c2c0700440350294030540c0e00308161404401e121501900d518242030340f50349940c0130fa10032042d039070000041501522289030040c0103100d0000f800c02c1074015440084104407da00c03540400003411602130092081e0900040c103211203140009221444c20855800050a4000b520340d000103600700c1030f958200385008203045860050f00481c2c41a50b00c030b081c0803043c6000140c003910300240100d01507080c0f00c0094007041441592200840c40718040c40040d064180d0001211000c51000c1c043d102d040740d41c0000e5400c22101c24035a90058050352001180b050f100190502940c0d4044e62920309481ca1503c03041d10b55405040800c41d8045c040f031010b4041448603c004900e001070004176040b005c19000000d00312a0001150a404a02c141e2213805004000c103000304008030787c0d11020360f141d9003a03109480d0500901c502d0700660307002103000410300400c05d604620 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 529063084 1250 529061834 529061843
    0x11070e100e04030306180605030c09040f0b090f010501090b0d02040b04060f06050c010e0109051e0a0206030112110105030106020c0603090a060501031a310302070e160e060918280603 80
    0x20303460602d010b143c06840c0c240c041c40e078159103c3c2b18540386902e07042850641081c0190503026800307440c0e84560064102c01c99500100303501c507002c0c583c0d080a09124050040203120010040356038008002510301c804540040d01c255102c0d2241d095690b516800000185100400b2a100315540c0201400a0300108046075682d4a000b140d07504401043c02100581503008000c2c04d20725014403112001c40010380d80903440c074400c1c003d440006817640001180a803c1d04d07050038611840c14540f4400c156580000b441c1007080038001040410740000c5c0c08080c1c04411142242c40740c0d00d10036510f02e80945090007800c0f00c1c0c20a4000003d100000513440295150f001d0300b042185d460289680b492100d159082c0074240741c803203443d05c40d450720b140041c0303002b03120f413040e1100e55658043d0500c00b443c040e12207040e1250350703901c4900c802ea08140c0c16445003505480d15820030b001840012a614030059040046040ac040010f203030f600050451030003241da041085010140d0070304a20011300b854001100e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 529064334 1250 529063084 529063109
    0x612050708030a08010b070606080724110c150c0601030f0b0901050415020d0b0907020105180a020612190216020a05010c0f0201030b030c030a0b040b060111070e100e04030306 77
    0x41c618030100844802c03514a40301d440300d69203404051034883d4899402030700c000341d503800041707802e8000b4080c0c1801012a0700c114040200c6030080c001000052080c07400c1488249201c0722007401b8086000098030400320303808a20b05c031140c441710a50f482211003000d0940690070000c001c1008002e02e041c01a400740c00044955500e403c2c0040c2215000e5401a01039001407001c807080c0010b5800a142055507400c021400070303c403202180c203030310041d41d4140250351140f04000c8440024a1091610601940182502c404c1e07a00840c0382489240710122590b840080050840903083c04481c003001081c620031503840304012401200202085400ca100b03c11009001a540d8071400c1d601590b103030001258212010640d00540042079503069498042c01180d2000c00c0340d54052207101c1c804e5000d001100c1451606203003503d400180104030314103100440002c0080024009446c0040d07038148c0301011220f440b481d55280d600b0800da409882c0d114600d2b4200320426034150005011541e1a05014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 529065584 1250 529064334 529064339
    0x1e060e0319080f0103121101091406060a050f06070302010e030c010c031b121a0d060b0405160207030f050304090227030706050901230307020a030806010c0209040f0201110106120507 80
    0x7190b001d5001e895180c88074101d800140042090b80403011408161402d100400c005074032043c3e401e40c1c46010302035604030b6801c00318040754001400015400901124a6070204c1c0c00d2000080c0b1410014000300d0041c400030a000301094001d60000c880c1d50101e000700d94440e660020050302170910006054006400e1400400d00c200d411949811144c00b20f03200d22900401101c400d4000744001c0ca22070001d0010302d218001180ca6020003009001e0150101145d02780c19142840142c4030301401c40a24048020b8458103001d5000c96200180d0798810001c03510200542042869402203400c1210101e00c009100401030507080200402d10340170088150130407003008100341d01c6040d140718106c00b29904100c01c895540c402c0d4a480d540310180000704500c00b41100304501c0c6500b0807601c50001da4001c41c2c0590906030400c150750360282d024a0155800402680400c00d4844041c1c0002c1440075515010021680070708100068a00c8540007005003d07030702c0103010380104c1c1100c1d003610b150144444c007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 529066834 1250 529065584 529065587
    0x90e0f03040b0c0c1e0105030433060b030c030f071e08371d070311150f0f0703050c0d08071124060102030c120304210c1e060e0319 58
    0x1410390112490174040300032108000152000c0d44018000c8518446020054041821864018035046000c100101010701003c100340e003181ca15411804804000384100019180008116580054a4101c8055503221000c06032248400c41c1001c04500303045040c4040e51a9102d020b0611404408624050903a41500740c07240c0554900e56450441d81250040d0424002ca50400101c110001401a85c2201200c905134100181c0b90002c4509a10300b8000c1c90040ca00305070b840070000d0481986514150407501200e040d80b0500c0440c8180541c080fa404c7d082c18020010355003001d0a20041d10000084440020b18800003221000042548248001c29407140005c1142c004500c1c00800e0149501000100c0078071203004200c1030440c4000c00014442000074451420215140380c0d02a46030b040624003d84100c082d040391403076100e207055840b100954042c40150321a50814001d0400007500380844000030302c4000003400d15428060351980100000005080b18030041078809507680b40c0010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 529068084 1250 529066834 529066849
    0x304090b0406050f1807020c0d0501020714070609182a020d03090b01030609140a150b0402090105070303050c1303030e0f040606170709030c06020c0a0816090e0f03040b0c0c 76
    0x613116080400340340060040c8056507081c0d50440050300448029103204800108002e800d800126140e9401040d41c40c20048040c0144212044d018003502c40b0074240000200b60f40014420303003000340014090080451503a41c071500e070b0b0ba002000541e035000040c5c150741c10032100440d00940144210388246140398400e00c00d00c0300c80f50340110140076603461605c9807005040119001d651348150010b2140c4210030070010416100d00c81c0c48410b041d080c0045c0c1000c2203c404584942c001da00420a4540503030703001d4200c50140d5858180091151140410188240a0011803441041c0740201c00310a1603002445a00b01d810202c410420b440100c000b800300303491035442020301003041c2c9071105c241c0d9001641580c1e48008286000c8140300c3d9680c40345100301d40c1d130342d20010140c0c00007840c544150401801540142005070300810348400d2015030450340300410b2180c0131040703642d08404c015150041c400504d02d14214011261134039222025160325a121009402c214801c65030f18504c14100b820 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 529069334 1250 529068084 529068109
    0x6120b070e011d1f0207090b03150f101802130914010b0703020a02040f140a11032409100e0117030403030518030706180f0b04090b120304090b040605 66
    0x2510020104001000707040d40e07640e4001d030584c1c070090440c03a100c88069040c0040b086080380b540106600c0e840d0450300022245c1015140780a504003102402c3c051002d881165004110f403204800169605c2001c505580915000300d9058010034106814880c6543c01401c104922061389000b0300c1d0f66441007100701d6103036a039000c1500000d080100306140d8548068442c0c40e000e40181c0c1c000c01c0ea140d001408a414803014503458596600a03030b50345a826040040d480241d0120800070030302c1c412604041c601008100445180040201e400720014500503d1040103002e0014040c42c01c0c40c0d40c03038400248060088030050f0f001c0400004854402210011802c2c80b0740002d1460541582c40407a100c2d40403102c2c404010782283c1808c40c1c00e8500304000300c014081c030390344d901850865802c4401010f150754028004005d0800e01408900c032110112000c5a4070300b940010fa49000401040342a810f40c0e42031072140c007010500203420304450700070400401c0c007220100a0140c50740100b1807001e4000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 529070584 1250 529069334 529069337
    0x305070501110a06020706020d050a3308010510090c170f0a0b03030a0c0b130201270b0c010204050102070501111504231006060f0f2106120b070e01 65
    0x25081009294003500300380030024050003d4661403126900d640c4142e03444508101c41c3c1507800116070348030a004d4800d540d0400b03c0c8510602042280700c1030710385034265064030182071030120340c451191600030021000050117100028401441c181190682000c420300c105c80c112418080022070440c0700342240c6860003d5400000b8482e00d501d4107a504d40480100344000159072000f10031410b580400141c01001d4150741c17282c80000f81c501c0c0482001c2c501420050781d60700c0150461005070b81001504000042c0c1101510709403114040401100c41284e1100d840d01d40c00054480541c00190003e00c00d6038402c1e02240c2c20365030b07200700460708600e061226645980000581c0d04004150710006a0043c0c0580d0400504100040a200b00c030129220312501c00c0c0d00109103803c4044083c01090300170036890400500a04027948d002d0f001d420010841c01c104401040c1445400d8488998114480c10079034003004a261581c0c603000c01c00c103078070308281d413004000c00000340c03102d05c154402d0a507484107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 529071834 1250 529070584 529070593
    0x1120201090b0f16110a061805010804020f0a031214130501030b040905010e0c12060c0306060a09031b09140603030405060c10020a030225050d110a0b010605030717010305 75
    0x104070514203942c0004010140c00b0340100036404110307007a803801e00130003402400e0300300710b0450400c100709188040e0780c041018001040c034186100c100800c128801c075102820609080e03550740c0b001030040c007500c003600c940c80b03c00e001e000700900010780f270310035040c1d816615058252510386102c55031b42d006d10350001c2c40a00350480240040d51280e0040c8104980c09440880c00d0903040d0344031030070b5030500780300e0068590003032000142d240b0300b00c05e00780191a2400041d003072600b8070300820141440002c0c102070280c0000500c041c4680e1140000700c4c010340e04640d00c01041e052007603000421000601c03c41500a00701360f0b041e512140400c030410700070351009005629061a10003030080c1c0b500f00c2d4403014441d000341c0b100c0da03480840d503000030b1010900f10381d0010381c0c0e880d07405280c41031f290808400c6048144290703c40c04c001640040d0b106910045d9007001908521780480d40381c40c10300000701c01801940880000912540c206000e18000c030350948507040c0001d5200d883d075420301003d03c40909203a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 529073084 1250 529071834 529071839
    0x1005031501030e1906050a1505091501050f040806041a060904110310021b010e060c040303200d020a02091602060c0f1216030606050703080f0a0e120702090112020109 73
    0x83e0300c01c440b00e05001c42500c0d07070107840742014048002c81a2081d035009441d242000f200309450321540301a40c10300c49001c241c20f03007042c0101d0002d240042040750540001c080c0c0000c07681c010800c1d9181c2080c1407a106942c0c640b10303241d064072500e09840840d40071218042280000c40c194454a104a6000e00110710075a0b91762107440d0003030440c08044e0f8041c001c5000788032102c0801d0004046e5007c411840b844054079401685013100c0442c0c20610716904040180610701410504603800c0783e4140c035080056403c4000c0c07241c0780000c1030460300d55a215402d1510301b2641c000c00d04c03445c0071f40205d801020303a82d109601d15803002020070f05180141c018000060100492101400c50761100101c05410800f40c003a415100e01c03800e55400d1240a41c152000d001d0b16814006c0801501507407030800d081030b5140c2d6001d022650050f0a1b00030a1006800181902e02d843d40a040a550240121007846641c0144900580c2c85451b09a004108850005c140700101441c851000356040e920b551030382d803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 529074334 1250 529073084 529073087
    0x120c05070218071e110c0111030414040b04090b1b0c0a150207050d27050904081602101805040504050307020d0f0503040f080c0102160b07060207020411091005031501 73
    0x2a4001c002e0000d000c0d000086100070140102c0113905141c0c00d0301d5900840e194031580514285c03801d0000c904100070a9000107540001000740d070115008010f031200e40c0c00d0741da8005805802000141a04035240030701c043c041c0450804041e0203202154840c0414803441d40f600d00e41886194207402c40356101d00c00090010b10800004002c1542c4918014203002c4a41c0c2d43c0c40c205004140140c0002d03102d0141001c041c0120559029442d050002d8550043e140c840811f09003a002040908a19802300c0c0180b41c040002d1112040e45900501220b00780c40080400307000701446ca4083c0005c100248008209410b00d4810240110340000045060842076405c01201c0030100b2021900180e2480d000c1001441c20400703000907111201c4850300072410419018500403600307140a04541c40010300411120003081a0b0301540c1d0854440c569a2850b400d124001c0d105001d4002d4200f807400404840000085014101c11034040720300c0240801c240078102d855020a07144940c0f01f900715a417400266 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 529075584 1250 529074334 529074379
    0x50c0d020a030b10170105061c1b090c0e06070507091d100911030a15110c0f0a06061505030c090a15030c02060c04030317060a0510120c050702 63
    0x14401046000c9090702c0b55140040110700380c8011020890968061003075244100009916090307400c000c0100785440c200086038042450603006802034041108410b2217603401a20035085103203003e00b5019580da48580d0000c0001d882d181c000141201c0308085140703055030803100e102360000020004281400f003503600404007254410f203102d0050104a0404c41c003803041a010386c80103034000400030110f040400e507500c0d0403c05140b1a4004400c00e05c000340340151150444280d02200048194070391010740000d201301844c2c0c01e0305200d91094805e00240c00183c543c3c25074450042848055943c204115510084648070004514144001241d4810800142549006c010a455441c55803884a00c409040c035152440000e07884440001100350104030554118000510081c605403668800414850b0000c5480d1507540c1ca00012600b2642c4020441001c8c00c030081941c0ba0a40c0403800103000244102c1e400b003000e034180080c2c40342881c024016614503640282c0344507407407415401c502c0000e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 529076834 1250 529075584 529075609
    0xa2a0521090a0b0405040f09080a030902030c0415030c060f050301150c021519020c0f01030f060512032715030405070f080d14030709030f0c05060a030b1c050c 70
    0x1400d40500114001d50345000250b0020030840019560f03680c00c24080c007007074a21928180414504200c56040024503250803660030f00780c1842c00088580c020b200090504540700c0c40c15034402c4c00c1015642e500000c40d280312040300d2060040c5141e00756644001c1d14501146040368022441c2440100010082c4e140c1d4031002c40500c0c680741c0f5144c0e4055000030010404a0502141d5000c04182010580c0010040d0207202351540028100b003940c80c0002a0b0203021544c1403410161103044d03402001e9000e0300410007500001302840c88001501e10007a82d00e030032500c8025040e200c2e41e1026200209407925054072400064141624480380300c080c10007a50000e041201e85105808000460806101000303002c0c0c030a9401a0440724244007000304564000b030714200c5061001c0050200007904200c444044a03485132484501c1c00b03d9040148068040342d10840d0481800201402c005900d40e00c510b00321141141c901080d259400310309040007081d1000100a0f03440603810120034501608003511 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 529078084 1250 529076834 529076893
    0x1020705010804050703080301060801080c032d0a080309010506102a140607090f090b061206030f1203060117071d0d140114072a02060d020a2a05 64
    0xc0c0c0039a2580c0d107da0302d0388246e1100c00003075503260043c888440c3c28402500343d511b04030001d10607146c00e094001450a8186a848104503c0354140c1000820600c42107080c0354000368002d0310b0389030070113a06018040440c1c10a2003190711107000700d9010b0088040309410301c40070807400c0c282c5620002d0f0444054110388241c4118034180a401407581003000494807503803c42ea191640d25107030041c082035070750140e041401124140302c050900382d100d1005803059010007008154241c0c8070781d808030342020040030004e104c5000d0b0004505a0f2080d1000a6000301420303aa9081c12000707002030b8485c480000d41d80c03200010341c4102d080840b5400c03200c803012100c1004011020b05501d40e038428030380c01c1c0100490341c5143d442c0c11a00800c00340803566158461418148014090407001300e4103611248050420750640000300d4280640d2a44000c0c1c901000c00c01100319600d259100d006400f106000f5030038035200713070304501c3d198260540f2800a51020385c003c008210794240300d1040c240c0420000300b03000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 529079334 1250 529078084 529078093
    0x30a0c0516030e09090c03101a030703030903020f010507050a0b040201020708150906060f0117041b08030d05061c0228030b0f070903080720030f010605120106050102070501080405 79
    0x1d00c0a1841e0242040d90384a07440e880443e01030360701403218000000b05090540d4200c800b91040580740440c40300c20405202800040b000c40d100d80760301980210f80c00041d01481040300100c01c1642090f5450306480c0225004942c45c89036000442d1b281c0700d00c050043c010380000400c44002914a888580c2252050055828503510b40c0399151a0516070940c5001c000200d00600c40b03000014090700303410107810707120f6640b00c9402c4000030b130192010030913041034600244005410701c400c040088640e01003506010511603901c521056881d00010703004c4100030701d041c010504511f41095082070314498030041005105031502042403424488201c000305809030701c142d40c00300701240480c0c40650312aa018115500f0005c42c0300c450030400411140c01d0015817401800458001c0b8103803006203511100c8a00c80381e0400102c40007101c000b25805e9050f20806400d542e0480f0107411000036103000342c038110000140e00407558241c414512030b0760f0241c0c01000301840a540704105c9183c1c418043c0c0c0468 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 529080584 1250 529079334 529079347
    0x10051f090507142d07020a05040506011e030f05102301140a1412011e03240209030d030c0315050a150507050a0c0e06040516110a0605040606031a0c030a0c05 69
    0x10000340d13001200400f500d00006050002c6203400c0d002c0c040030b0300007500c080180d03240100001c3d10031107501940d011281403403142500315606c6070300060b0138509800b03801d2259040200d401070b12a070b40780c0202c20680b072140341611029074403600c40624002d0141d44000340e9060400e4403900684c022415401000746805282411146000c0106414040c100305441958500701d201d51118601c110041c410503042001080423070740c0304d4070f060b01d8072000355001440e40241d854504001c0c8207401c1c04c0740d014003c031481044640d425038001d1480550380e49052010107c1d0110f001224000344c00340341e030b00c46c0f9441024000c0c48030350204080088800d041546c60040b454440514140e0008021512501d04100c02d00140c07051b999103a82121090310706024074104005000b00003042000c6a07010810001c2800c00501001c005c03900105400c04000c1203981001d0500c0806040c1500043d540300c1c1d50401503151210380c903001c0e0b91041c000507071208c1c11a203802c0c07203200c017428248074408100102440300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 529081834 1250 529080584 529080637
    0x21905040510051906050307030f0b0d0501090b10062001180b060f180a092405090610050a0b07060906020f0c100b0d0803060310051f09050714 63
    0x706801403465000c0966918036240c100a15090304883e500200c0c00201e00070858150098290380e081810381c01c000c5034002c1016054402000d0b0440025031000b2010300e284144981988500c41d954040c0c0300c6900e269580300921036001c83c0034411030300000c50341845041140c0401080c030b0008000c48001241c00b804400040b42100103820341a150300315521700380549803034400c0d00d0014a0509460001000d240b491109555030300040004881c2c41e181c40b507201c100442c032044c0c1741c184c000140d0401c0100305c8243c02d010003004100e4a0340d480d486148081851005c50f24134250031101d000340600a1182400c0354025a9080f1041c2214000d484503050400100c0c0c078005440b9966044500903100d41611f9034252030645042c00308510700745001d1040c105600c41001c1c2c00825a0000794440e41c940360740010928204400401c030160030726160074805212880b05900303c41c081c3d407162010205032a1400f4408480040d00d03440085842c0441001201003118003604a5010309c603004441000b50041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 529083084 1250 529081834 529081841
    0x18030a14070e0c0315010e030d090306050f04082b09120e01030e0c0f0609030703030c021906120b0f09070819051603020c0304031a010f08031602190504 67
    0x201118110558800344001030340400ca07400c002c2410841404103070400c401c2d541068440030f041c60380c001003621000742d40b030790043c8a48800c0c0e02001e8210b80201d200f00701c2c003c0a040307050004550041c20600490701c40e4164076002e90155403c030390800d01d001040082100ba2015141034940c0d0400030f109400c0c0c25007640e21882c24503d014441c0e101c1000706818005000149100600703052602c0d03d80741c0c640b040c90000781c001c03e0007000d4845041070907051000a041740a1415900c0e410f12411102100300341d0f00044080da42d80c8203480d035060101c2950000380f002042c0d401004001210b1020040e0400b804e80c010419000d00038001d4031244401c0408500140401c585690100e4080c905020700d00c41c0c2c0c480308114000403d81d0420180c103086508844030714041120004150300800c00070809a0705104031001954088504190700d07214000d05040c0310b00921a245002d03100000c0040c04c03a00210803603403440c031034080080304100306038204441e0a14950502d0351a8900034004141c5840d90320 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 529084334 1250 529083084 529083103
    0x21051e0a170f04120c24090605040f030908030f03060d0c05210f030403110603040201110a1110050301120212030d020a0c0c0b0a08040b04050c0603070c030f080105060706021803 78
    0x81c1801103442c140c20300c046041403464484081260550720500403905041a0741b00b106440008042c2c05079030b02a02c8806420800b2000d81810300e45424081004141e4650412032842920b4800940707645298180e141d01a1341d00b0800010820000a111032405800000d01184034400806030b95440e03401240011f1010181144101a140c003000341d09002007140b480d56000d42d0000f5458141142c0da050700d032106a2018034092040403022804582c00749600c04c0034403d5a03000ca6810b58060b04114808104e1200f5160081200100c0e08000510074012681a5848075441c1e121058490f800c3c414910b100c0d150120490106001d025403008030b50000300003617a10365a0319081c4074000d0600038200451540504000078013044014403107900621000c0d80300e90060b032070620a0750350f400c10300c0c180046507521542c4100004100410260441c40f60480903020359600d800c103444604040d214984280a03a5a01400600c83c5e10700184c190707001402c5a10860140c8600c030080d11011900d44480b05 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 529085584 1250 529084334 529084351
    0x30807050a0303150602120f0d09030203122a160c060e1315051309060510140a050109090c02030c15190b0901050f04020c070321051e0a17 61
    0xc1c441c1d0300615915024a00a103007000b00c00103511454080082c0d540c0c0107208400c1c99011020a21110201c85142581c0f410201742900703005511071841c0c029180c1d03200074040040c2025180c00306000c1d6102d03410150780101d05880e581c081c656601207034242c5402c00c0710100c24142c1101c000100043d4000320420041c19035843d1f02c001314800e80c0c100008000f140201c03104862828400500c1110302104140407203405071005140c02d083e0b00700714400390200768405410103082c88288680e07000303110361607070488031348407011b000c000100c0c804c010f110001846440d002951000d000e0001018951061509807164011285400c4c03034417041f80e09001c0112250300010080c0c000b009000503020501400d12401c1a40c10803c0006020020340540b0041c01b465008203003101035403440d078403560704a91007614802c1c1114541c0d039407031616405016120442d0aa014405961611040e0182c0183c8a1980500c5114010105c01102c054616041310184c0401c02000020364800c1c3c0c21400e2580e0b0262684 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 529086834 1250 529085584 529085593
    0x30c221a030c0102061909030519090e0718140a170a060c02061b0d0f021b0c0a050303070b0a0b0a2c0103050606091b040605070c1a03040b06040603080705 68
    0x1603004150410440014107415500480c0170072880c1035201d00180d41030340382e071000018261014103049900340201d02e21561180062042d01e10305a4000b96514101c3c0c400000d01440d5544010741100e50b00f411910f080d118000d211000d020f00d40340700255407180100038000400c4a0b5440c120000c580041180801954000403001c200384a040e0150b0700d600002800180214107003007030124a140e2051507604031101c0f0201c1c00403034099403a04505e03201050f2a20075520303014000405a881d070b00b41d040c200320b40d00c01c860bc203040302c1c248607a441040f40c400402079810301006442d480c00c82d0100a000101c9651381e00d100c1c401598034010600041c02843c104854015117010380d400f1a00101d01c00e140244c000f03e00108005600000d034517a101a080c6c0e8544c9254503841d000c202003581158004050745030100b804039040c2d03881806000c201d80240030108015554180101500ca101d414840d4400000c100080c0800c6190452640150001d0000a080c99507078951900c0350300180000c0320303150007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 529088084 1250 529086834 529086881
    0x50f0d0605041808030708070e0409030806030c04060b04142e090902031005011d1509030601090b0f1002031c020405040c02010b0906040c0c0b0711060c040302030c22 73
    0x1880d201d81181000030382c4482c0742c0d03c2001c2e02c4002c07590000a0613041000f00e44070004031054402c1c00103184400000d44180943c141514000d4258281141c1c03007402485041900681d03413900c1d028540403503594510144c07030030381000c804088110182a5540d0082034505401e00310209035214040321403605130f003074064222204c1e4024030394519980401450380c014018842c000103d01405001c031502402c0400071940b00300203500704180c04089485d44903950b1010007060400590060603402c00c12429249a0707a202c0303000c0310455506282c2584c0040c1e00c1c03803020640d8203090f000c0b11030b44101801240c2c2804c481d8100710345840d40c000825000705070040790800480c2017a000302c19155840307000030b1081e1000407020400500000b0008d40c4180e0b202d8813580800c81c06040319801d03041c1c203c6c000311503c0c5060000a06103041008030b600d1940f080a00081d02c0c002508191010360354000e000e400441c11060400c140314405805d04840c03541105029120001e6510400c0c4030044850900b1a10a2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 529089334 1250 529088084 529088089
    0x303050405091b0301090b040e07080c1008090a030503040510051314060708040602090d08040306140612070504020d0f090f050601090b0901031203061203020601030501060b0c1c050f0d0605 83
    0xc400750401941e900c9034031100030083e03840020b0324190361104030300203041c84107400050003410b0100f4618400b030280b1040420506c401040503c04c9140a81d00700d4041c90056800b02d072003205c210350b80840358008c00d9001001a208400450308280075508440403601012208012181c0c2603804485421186080804021030386148521a00851002d00722510700810003410494005000814880c0e0014000313543d07989805403d2001a000300302e5a48454030b81c507010000f004608018117210f0300001c0011440d18010001c0380100540002070254145030105100c040c1d000103100701c0903d902d4a440404c0e98034a0300c10074245a004038200d1410440c941041ca0078260103030030840b00c00303080000003807454440c8003000341180d41c4154001c2c400080c0e4803049000b8403241d00154201c4101c10046000c0c036a0005080e4180c90080700200103455441e035182c041c0e84640a803e1040e41c00c000d03031a01c10079020360840343c0300c501e46061503890011001d041038242c0c0d01c4040d0b40494669207200620103030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 529090584 1250 529089334 529089349
    0x160e0604080a050c150901080a1b0903020f09250c061803140306150c0c090112060e0a030c03050c01060b040605270303041509120605010306050f04020f0f190303050405 74
    0xc4017038600040303a10801c8000450381c422043d200d41440380c00c03004180f1100070341e03000b40205030341000708a078501c03403082004142c9142840180e2041411464004403403500541141c0103000d804020790a04d00515200312401e44a20381000521103c8071114011079124010358203425030301e0381c60804040030b614000d0110100c003802491a0a07003481000306036210f2000c4a090560586901912a80c3c191905894000003052241e04590050000101d0710790700e1081c01074036803080c00d0074082c0c1441c400c110760f80c42211450180c0080c040414070030100e80204010715404560b1800403c941d51240c3c510311b490350042d8065000910300084030b019040190004c101140d018807a40c100c101a0708001a5813402580148108070302d442030300d056200e002d0b00d80702008000c42400b038200b1f80620b0800200600e02403009864890506c00001c0c1070007090540d85201d540e000740404204d01d50b44051180c00800f0000d0140c01c01e00300d003030300000f031540055071000862003a90340944e06e40c180418421075 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 529091834 1250 529090584 529090603
    0xf09031502070209071713050709020c0705010207060201050402010806060d0902220f11070624090209100f210207021518270703020417060708010f0e160e0604080a05 73
    0x4001a011b80d00001c0303410101500c0e080414540a0000b4400900300903041021342e512046101e4070004201c40c9604011512104a40d400d0f000d50380d5035642c440f0305a082c0e41d02110300a00017001c0f180040d541e89401c00143c00d8840310090000f40c01c1c0400d5001c0b6201c4030072076000b051000056400702480403564090b40000d403d00440030b0018200b4007070000024012144000c03e0280c540a810024450f15045941d01826244076045099600e20002000b9030011400c02d016050441c991a0400c1c0219440400c240f415940c4101c59090000e11203074030f031440c03102588120740810a050160b500c0804030400c61402c45229555040011510644060040c913080e0250380200e00201002a10401014190480d00241e69030350341e0781403089000b4401c54010908a5807158003a904d81440000c60340e1241c2590307180c11065076207a0104651b004032602c1001d40040e011000135a031068107008404400010341040500c1041500000701365070810b8004c20f03403680c0000c03400010301a00300440d1a8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 529093084 1250 529091834 529091837
    0x11030c0c120a1104050c1204080a02060a020a050a2d0302030109050901202503050d24050609400b060a031e1a010801080f06070f0903150207020907 65
    0x2c200c0e0507a990000e584010b1a0704034851903036280080c80d8145840c0403106020311344004242c25280c2464510001e4001003d101c006204803400030742050814400c58403c28240d4a601d4140040d00c1c2007103907a900c0651a100d00400040c802204800d08101c0d00000049944c40241e142c0d81011807203c201e0340000c01207500c681c14040c1c0c50045940344401107400f0101e483c40281c1e00e000720311540c4600c0e4031139441c00d80842c0c5800700c442d00b0b056010000d000002200c00d81840b918440341441d00c0b842e130031002503504132024400c080180e0310342800141420031014107030a4140f944009640c00d05200e11001207004500905011001d00d49026202040954200304000c60701030280441e503a4000c2460f420240b41d59440302c804a64410805840726640381c0a0a00800244184481092840e142a94045000380c3c0000c210444046802b21a0842000c0108600d68070710740f04854090050310000c041c08810302022001c61806c007492400c403001000056a203501c60300c1441300c8581c00520810 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 529094334 1250 529093084 529093093
    0x319111b0303070917070b03180d030e2d030a050415050f030f07020a051b040b01020312070509010c0807030906080106030b03060115050c0712050c0a0f1511030c0c12 73
    0x28201c0d001300324541502e060210901c02210300007032031450840e4503044031003640008010426a11600702c045039240d0304000070b0b101d103030710404426000d42c1d00744190448580c225410383d40480301d54481c00390705084804082c025030000b403804a4195440202e941c00080c00003c1c06000c011410b40c00214900400d2400c03a01c2e0400320b02079000c40d40009840c0903e4002024007141c8403600c204042100e0070f40001c295130050440c072082104c4540c480c4a52800380341031680107000307580040705880c00c0e42080e06e90280150f48100301245c60381e00c1074900bd410303c100c1c3c000d01004036401002400882e4441d0315001c80035418041c021304500c1d016400602010300302040140b460724042001811900040c440c03034209100a00280d81c01e000d000d00c501d2080c07250003c0040c1802244014860440c010825151660845000e1050720f880900400c0d0502001600400c00c2c040c1c1d4144081e5000d82d2880e010818007140d4001d2421f5074007030500c10342c051b484114007510900c0c1000510489030705040040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 529095584 1250 529094334 529094341
    0x5070602070e01060e0103090c050402160203011104060206040b0402190807090f09110d0606230f040504050303160e1e0102010e0c0f040f061a0a0e0d0f02060319111b0303 75
    0x174070111401c07607003034105529507008004202c13041c00b030a400741070001c1c400d40d00e6024100c0d030080d0000382407200740d11960820020b1031078100d1000407a020b840c06540501003a40d6540c039403110902010f4002c03604000d91100041c10341c03544c0e181c0e10740508400c1d00039102140c94668400159003280802003c40d40c03134009200c2c006403410994521703040e0152440a042612401d0280c0203008551245451100c2c0001c10260390400d13030860387c40e400e0f084402003e219429801e210441d81c0841e401002503100708007003040700d64003505400b8000d00c20310348240b02014040100e66120000b507902c1d2000503109005a40660702030190b02106c1131150700401034081440c0c005110f007170601400c14007031591040b00131040f00f030a070018005018100c50b21080d414143c54604001d510110304c5030b0006084070001e0304240307840025110250b4101c90701d03a098002c0740c1c00300b00441e4005010194242c030700b401d078036841000a006401003c0c103403402d15521541031030300d086801c0c5100c00d0f010040c1d800c104100b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 529096834 1250 529095584 529095587
    0xb040e0a03051602030d36170f06010b090a08071a0d020f0d0515090601121109030706020601030203060c1218100608010c0219120c0804090501260a170904021605070602070e0106 78
    0x3801c0842d5502044161100c0518500f20300381f070f401c1010f45200b230182b5000411440660780c0105100c04050b9405882e850384c4119954840425000d406015482d1481e44141e60801e82c1c0600550842c44000518280006c540010140d00c490f9203540190303150400c00030007404200303d90a141030103880f0301c81c0030324041c80002e04542105400c581540c1d5038180000c60820b4120503151454009411903401c541c440030013a558400034441203100c0d1151000082c01e0000d42d10035660403484500c15140749440b03210320403400c0c1d549020050300c60310a0722407420200340580602c0000341805800058003c5100030000e007440b41000300380804400d040a4200024a842c2c032081007912145400701c4c1307072111450000154403c0d944800c40c0181040000b00300f40f254818600b812440207207880890b07007070703509456854208008001e46041030820340e0310750541c040d400500c00c1c900002e200514159040c0c0d0a0420440d99010580c1c1d5988600340c01c1c0402c580420640300501a40d01e0030380f6966142960 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 529098084 1250 529096834 529096937
    0x6040b18060a0f0606090f180221010612020913050717070203030105040605040e0a02041e06080708010507020c222d0b040e0a03051602030d 62
    0x60006404400059000444440c040d000304600c0d401d0324482e051800071400980040c0550241c0303a45450000506103000741045400c607100750346c4100c0410700e8400b0440d11280241d15640003184c081100320b840c5101c0040c2031544550015070b8160755410041c00501c1c801c103000d140404c0710710401a903190750362880417104442c000c140e0302040d581e99444c8200c48880c0581e5000c0c820b4403030a41031020041e00440698182e60702503a042004a036103074100000d039110304000c5031060700400c0e081009428140c003e600e44000007083c0044000800c11400704440d05a03001c0c48a5403c008024059101e0a001d0250000c00d00e100a20745c080e40c0c400015016034803d40082910180075035507900d1030165030442c5a00c0401840044004080300f166243c0555000401218207407504012075003928242c40350f94003d05036500100400080c0340d030141e55682c0a24480c6032112030400103c001a0780412400041e103d4544c0d81d40103501e030307403101011900c0d02060010f5510640e00e917003c1200c2c90040c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 529099334 1250 529098084 529098091
    0x60705040501120b0d05030a05030723040905090a05100b0306010f030812130c091d06011a090307030f06090201080109290d1211100614100909020403030801150f0206 73
    0x3c60018880180344000391108149000043c42e9010200340109410b03005400707075120701615115003850741100614984054000820300180a40502c002e024600182d0300096000c00c04400303d46640d5842c0e105d0710715104441f8250300c43c3d0742d110744080f0300d1410140000c500404c2090030342280b8900b147d0302c03610b45004003241c65180c0c0504600003060860100500f2041c5034000381d018452507200c040e24000352040b0103d00f07424524008002c08041c400149550483c0c00d03a40b4124030190400442e213071164400c0403555030610412401101040c60754040d1b1403114400e0b1000940e0440510001d4001a4143c0c4840c00780351070981710707920151895031904058501e16007148a10422480041c2c06072100381e101500c41d400184140c55569000801e2007042c030f68440803201c03461500d840d0042038a0440c003400313500101411100f02d0604046031b8250314210705060a403074036503c2d00c041d2001ca030400c2d8400c1e000598110010400c01c8001031500c130700c14480745854509034050301c0c0301950b10140603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 529100584 1250 529099334 529099367
    0x260711062b05010317090102070303030c090806010b0901030c02030a09090c050708030405070302030c0409030e0904020102012319061202012708060411040612060e0106050405041202060705040501 86
    0x20820520030103600e451040120514200c000c4040c0401c5800090900740000c454002d001d061030800c1e9003c03442a11303940401603006255060441d035048000c1e06c0c0258841e01030080503040440d1100080c086180681103104205407100c000742c0c0010b003561820000501950820441008e0140d4000a29000e640c001e040200b1034174048001140c80c1e01c1030b403001410207407004c01032000300207000c660041141e000720119990802c846040000b19a42000018041085260048124200411244d60140c01400002510380740b030085403520140403619075580602d00b000f0041d1261f180c2c0301790200c051340c0b803a0400899080c01202a0031404e0b26034080e042c0309005100036480400941c20803511140410710b0340f900d40da00c0090310383e01c45081c0d03001c4440d2244c0880d00442c0381843d00c41c06084940b82e0f025030912001c152644c0b001098a130002d9a500d54075400081b0303164a840c09814056446114154400c00040400908000006e000c2104102c0100020420751703a20109009112016 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 529101834 1250 529100584 529100587
    0x105030c03070f050d060b2a0307021e0405160f050a090605130b040b04091107050304051e042d060e19022502120d080c07020d0c0326071106 62
    0x440b03c180d4160280040000c40c0d00d0a0100108450000c180a030220710000c02180c0d80048240c2c0d80c9460303a81360360511811662050003c8405450300107041000d48241080040d111824800841c042d254121014031184603d01c1c078552240340d002041e07898503c19807030501e007080c1c10404010000381951041e403080000102d0303c0e030340d505441d0080d280103028910307007140d0b82d030743ea0500100d8a0308a445818003032032500d251803203e030611100312000103074082e0103546428104030030405080740121104c00d031001c0041030044680c41d02e00c5108101c1c2e10540c000544003010221003200c1207504502c032020182070160030454180100705064000202c1010106c8a54401300740030000d000d100c0d1020074070034500d1403540c51561890741d140015802542d41c510000c40c5414030581c1c0700b001440000c001548800058250000c0b0b00c0944803070b0340f00800041e004c00041d160f0341841421500162004408ac0c3e0944419601c8600305841c2180a1150503042241c40e03102d0004020341c291146008900 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 529103084 1250 529101834 529101857
    0x50702092d1e0c13090e1b031510090c02010504021318030e0d0b130c05090103111c14010506031b01200c03030d09032a020409060608030a1206050105030c0307 70
    0x980c04142c6034041d0f0014240c0750300595030400940500100680700901b801845019050b6044440107c0303400320004e0001c100c44005001690342c2c00d0383c0144006103120724041c000c59081403d0007005602000ca50010801d0700703240c010882040c5804040003803a03403034a0540418003036280382000885405050003030302ea000c030402045400c00049801440a00c0303000400c0040d442d1204540c100502a2400383c410b65128002d1007051182030001910522400c0000c2489240c044e005039540c0900540b425541c500542d601c0c2c1c1c8040c0c06102464071079441c0c0c0100109800c040212051178040344000c844040751200010303003000b904030080318022181d02146200c0c0355041048041e042800340841e6030b1036204405150060031100c0084002420f00e4179502220002c052038104481c2101408400b610007a908100007400c0e28002295241d480d51400541d103001400688440e94043d200c031486040d9052082e0204c0f03940d900100c0c1480024420307c6110142001503d07846840c0f800c1c80c1c0035044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 529104334 1250 529103084 529103101
    0x130c05090a090608060f071202070804031e02120111040b03100e04032006060901090e0111031f091107021e031c030e06071e050702092d1e 61
    0x300c0d80c00c44540107445003900041401d400d5200700d04998400058401e1500e0300c1c0c14039800f20704280c46110008003070401c020f2070130460740d000f0912188100b0407603140982d641d59030840d40c016034142410785a09400e042065040c03c00d00038130680840340c000c2046510316140c10b50a4062801101e203c0440800014112042c011010b0081d001b10b99a11005207041d180041000089201c94ac2a2903500c3c0c1d401c003d102000900503024980003440211503a0918109800428502c00441c45964a641e8a42c81000000f0000c1d406101e449581c1c10400d110840c0410b01c00c09294844141645811140224810a50255665558100e40e000b46c0d29003000c8401c0c40080003002804d9060080c0d40181490202c0c40d40220004240c2c0e4809210a0550f25021a160030307007102c2400c0418403444002c803160b8401c1c1d080643d911410300303199041890f6500404c202e14000c46402d02c100b004281020321302c03408070300c04000c80c040b038446500c0c580c034000c005070340c035148080081200c280301c01000c9031902 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 529105584 1250 529104334 529104337
    0x4b020a0909020f070312050105030c060703031b05091905030c061c02040e06090f04020a03140f0111120f070512061f020714030705030703080f0c0717060a0b130c05 72
    0x40440c0c400540d11840743d51041821030f408644101d011500d010034048010100b4001c19040715402005001c0b01c0c0c850f207090042c544e0140c00d0840030560f440d078031550000c1c0b0080c4c2030307100c034445030b0748041e2102210301c140000d141002040f01d144c417124420030405545c0c000b840c006503e44c141c91b103540700c20900d1001c444c5100d29442d00809140041030100d98101e42241045c40340074212100c41c2e45484542c0180c00c8800182d40c040d41001003e00244042003801a1542840032074004840c4517800d880701d91800c50740fa9841c81a8440d60005241030700c10207405060f50446000c0b01201c010781410345000c3c10034851680c8440c40000e4000010b002560307042c041b400c1e1540e00c000701b9050000b54040c002d4980e80135010320020501c00120420507420005030380015190040c00408903241503803507641040c1c20000e031120224008021100100d401482040020100144500041019004c5203801c220700100400c003a903180107002c2c0c055030b4515005038240b0303050410005080301d20790b0046801d07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 529106834 1250 529105584 529105589
    0x405060f1c091a0402030a020d110d030203030603060916140a090207030e12060112260a020604150b0a05040e012a170c0a081302044b020a09 62
    0x40111201c0d030a01e4038200390030102c11148590109500380c02003e5900702c041c1015a0702a4241d448950300300b00600f0007503e0f04072414082c41596500c101544005042c08004c235008400580010090200078102000b20703a401102e000041c00d10b0708804029000310800d5403060301c00c400c0300c286003410741e5101c6802050191600c2c2c1c000f95581c0c641820054203101103504600d0240d85105465100c1d41c070003059180c1a204a94000c00c2019a070b6103a0746414091290200e4042003003c02c1001c001c0e144000070302282000d5006030201d4074041c1480613184220108040e1460304052034607015544008651068a804507000240c0a001542c0ca60042c25441c403481c0d820350010a1016040b0340485540952100a0f50b031109480c82028103008204800e43d003410090742c050180c9003010b40120700865201002422104401a06400284c15214922501d040400c0500100ba5415660440484460010311084078880824030302d06124210b0680c21a41c54070b5000c18815070044c4940d409600 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 529108084 1250 529106834 529106857
    0x30403170304240209010f030e030d0e07080d08070f0c020609060d140c040f0f0f120212011a040506060307021e2406091003080f0a0e1207060906050705030405060f 72
    0x1542440510f03818000d500c40c803211404514031501d19442e003442802a482400d641170051400d2964070f4a4100240c0303103900fa030940501a9038004144004c04000304120b0b16001d5175810400c1c10440c40203040d02c1015042207042000000c50701000d030f2907450841c0e0340304205031440c40d510780e01c00c421840240212110b041c035441c010b405018007005548003134401d07524000c0c600d400c4103030fa0300b913520351105151042c0c035040341440204000e0444180fa103903d880380041c110b0700d40d50180b00c0030682100d2510365044108109104103071254201031103483d0b40994180ca20510758140848003a507101010480c504c0075400c142c210000410091016220100340280ca22444410b2a20300b03100d1b1a10840764140960405000242629400d6083d0300403203400000807850f101001981e042c4550019015409016401c0c2e8555402d8840d0070030a01c440d01a038020f4600c182c20040001c00920096002c04100442401050b010860200803682103840031900669180360b620044403160241051400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 529109334 1250 529108084 529108133
    0x90a06080105090c1e0a0b090402090a0b1e03010627210b070801030218060604030206030103060f1109030d0e121c082508100b0c0a14030403170304 65
    0x940b00c48001030741e12045600b101c0008804017483c0c0c800c40030142d8060402c0c0e0014030f00000308001c4210000a103120301d00035102515201e040d4003c11b182606070380c400340c00903100054054080705014a560107141842644610f1945401c1000b0719086030303010365120380c40b21515440441035452803124000d202c0c003451281516030100854034410341104050355076070024400100305510401d0100d059941c01031408101c000c099003280c0811000a0081e50418000c100100243e0780d030002a5000f14410702c800708080781109a030700259048100510b510000a1081d00143d0b94045684c880743c41c80ca182920040200c00002243c07404281c81009890040e002c40c01b83c42c030260061280043d406455000d0162200d0054102100c000c03080da001075804000f1560300103100e1103c8980040220004000c01c0781c60742035034441c40c1d01c0f821100d403895112024070800c22155803004100078000c10b0107182000d10f1510780300401410300101e8403030a40b00100041c204802c00010380f010a26194103803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 529110584 1250 529109334 529109341
    0x405060a03060c020c09060409121115100305010b01090f14030c090403090608070c0b0703050604020705010f0e070e09030306100c0506040303061d280b041b080c040602060402090a06080105 83
    0x2175185d40003840303114040d0380c0040c0025141e05090103250340a60f4481c075078845201600c0703421140300c820455155024000c180800c1502c0200310303001070058480c6400074030b0301c40c03840c035027036084900103010141070002c1d841d0108020704140440100b1600141c601d1281e046070100024148407003c410710703901001a0302400280340c0e00c00386c1c00c81943c0c0c95440c0c01c8926210782c41c0946079080e014a0090100021b00000780002d0312a4100b9034200741d02900141c24050715a8906081d1801d42c03003180340590351044035280000c2d08010a400902003900c0e005c0c2281001a6803507224400100658080d845801408070450711501c0c002d400150010240c4505081501d001006454a4400e01c4010040d0300880710030400c040c0a42170041d0142654001914010380f85220084c2201061030440f540d04d540703220ac161114028000c0a11041c1d601c60102000940094036110015054001c2a08e0038401031009a0700000c0c41074100e501200e81c40500c0d9a42d00d000c2c000740016810040c0694241701c00c1c07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 529111834 1250 529110584 529110587
    0x9050f13111207020303040b04080703091206090c050f18092e0f0b03190206160b01050a0b09131104050a030b04060b1c0b090a050303010605040f05030c010e0405060a03060c 76
    0x10348010441d400502c9859282d03540d040f0307034a001c2920094031284140000c0f8001031480350007011614070074180f0504a40d5145100005c9140f04c00c0309403031007500c1b503000c3e41c1000740725420980513010442e0340c0c00c03005102e000072554500c0e9021150800c51184030102d1440c00003001b40200b2030304c003c07860b110015591002c0440c201360343e00301d58905a0400c0414070700b00da807a00410001d010003a000780040340e80d824101c6008a140201640c00050400c0b0b46a110001d4880c071000c3e0720301800506502d9450705040c090107402c6984a24a0381000b4000ca02055403114580030400b802040040307060854001c4061442c4907541c04254044401e160000c100007968440922550140304100141d022041c240070300a02d842106000030b80c00b00007451300140b00416040e070000c400c101210031407000b40e81c1d6949141d000b80c01c40000300342d0228007004007412013181e01010b8034050b4081d10628030400300181c81c105c1c010070b80b00c2c440d90f200c02c0000c6040c4c8900b84118001c0d50020030600100749074260 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 529113084 1250 529111834 529111837
    0xa0203130b040302010c0828030e12030f040b0705040b180f090105091b0f040807050901091b050a0e280806010302060301030204110c011e0c020d09050f1311 69
    0x12400e00e0806040000d004a000042c0c1e400c90b41c060b182d10200b88256511001d0070351055001e10001060360a0a651005084400d01c10f451159100000c0050840c44600c0c504084504100c01c00b00c010410851103e255801403070704594060f0b4400c01c42d4440407415121401150012a020040070504049000e884d8400c080981400c1e50512502447c3d1014410b100e4402d008030303500448440040b4000c0341c2d00104804290858000c0c4a00b0b0001d0079120000310350041d0310000e200da0101c0014801850001300c01401080000c6007000910400c10300b140c414951547c4e4841402000f040103a40d96000c1c0445030840840141000c18034640310341810260361100b100301075070080ea960089041b880024165050300e8000303200900b142c1c0f840c0e00b080301810112032000c194640030310844d032041409010303491013041030b146000380720f45003607910400319100744185204640c0300d240161a0160408003038415280203881386c3c141ca12006000c01d201041c50b40307038040368903c0c14079164074800d075000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 529114334 1250 529113084 529113097
    0xa2117070c230a0302060f0409090b0f0915061011010e0607030e0f06041b1d01030501150e1501140a0206011806060503010b03060d08160c090e030d091103030a0203 72
    0x44034031a800c4082c0c01c0e810200c40c07900e00d800c901281010f002601c0c164010344909201800b05a107019240c020340030642e0b890034004c90706944090240501080c14440066000ca91007000300300801824a0004d62214040c0c0f04500607070064512903a018070401040c514021081c1c003d000400c1c0941040c0c1c0d507924120345500000b441c00c201325098607404104180c607490340000805a0340c455032180d01d480c1e084407100c03084440310f5040c0025a900e00849003030100381100d1440c0c0325989103080041c00d6030b40d50307109040060500b00d01404003503218520f65400010080b15045030380a04401668a004a0016804003601c0841c001d1400d44d800107a440c1a120620744004441240c580f511083d51071342d0242c180800c20a0005021100e5000091030f44600c1c001c0002d4220785a60310b1700342140c2c0c00807a0298040c490745c95060144500b0f009800024030002100700482044a40065101d000c0c100565484d1a11184c4034000c0c080f0103c81e10040e400d00800b560b90b1101c0480d0082e549a1021 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 529115584 1250 529114334 529114349
    0x509090f040b06010203031608060a030f030507050601090501030b1909020402031003150c0f081003020d030906390218100807150219030302160605150a2117070c 71
    0x10000603d035944080f00341c85c007a09042c04da0101550b031284096440020041400d608100c02240010114580303814084005010b0740301c0b295141c401c0d062190030950140c001c0f480740e41c1000c00400002c0c00c40d0840c40d91200e26001900d40e00e04c44004014040c00d01008003941c0140040240f040003444d0382d002d170088030300c10440100f00c6022001361009031a005015007021819401142000a01034071405034411100320b040118a80c07203500045060143c1c070f4090380012241304041c06001e40118003454040d400d0344902143c2100a0040b00311200115402c20081d0060741c0c010045441e05410482100d1340348a80c85d02d5860403940c041421005032240d200c05200744000010780c05034881d40d0300d040301d0507a07025000d44040d0711082c95508050510440070507a0801c90220104a50078410354020b202d014046518105a4041e080c4020110a01c501c5103001c104100402034441442d40040e40c1030400e030008081580c1840e094142c50741904031404580050400304002c03441c0043e000381c400c80c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 529116834 1250 529115584 529115603
    0x6150807050909030313020310020304051f0207050d05090a0503071805071107120f1506030201091a0306040509030405060304050c010807030c080a050c0c0118020a05010318120509090f04 82
    0x7501c04102940c40e082c2c582c3e28054000f0070114101d61108850341c0d210a00180407a100303803014040d200200d0b13000b2141514190080103020060011030112030001c0c000b41c540c00c0d0b0402c940c90315843d890b1010300f1503030323024484001002202600c44c0c1d540e100c01020000c0c10f0351000c664440010502c03084000001e20f11500e03000c00541d04500032503401c0c0d80f6480d20001090304904240e8036100d5052400026103622400c542484005185502c41150700a01c00d00040344542c070707602c00500440002d82010200103c0c4441328040808100c0560303620110444000ca01602c40441c0c8508611450700a0b1b80c000710000308100910200103100c4440c4082a40e40407000da8840b0001c0302211005003501d80080c00140104000c1a070581115800018082d0a10f1901d030480c1c05c0340307085a481a600e02d0384100803012000c1545064141003004000a090920604049111140034640803100040c018900380907240040c44c4118199a00034001524440c59401c01c10b203030309d038001402c6408645140c00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 529118084 1250 529116834 529116839
    0xc030902090f2202031608010914060c09060d090203071e0b130501050703021038060403080705012d0f09030815120703060623030c09040302030706150807 68
    0x710b04074a51154009084070010350f900200b180125610b8503005030390501c502032255480404100900d0000c0080707200010b02041a031414103111580d40000d0f41650f0040c1703081150046070a030440e04007107812101c01d6030320f03d000d00c81800180182d92010b900340c829110080741c41d2b010078220409a1f40c2a1013515029983c07003126404600c0780d14010052503c160000b00600e500407809007030010311900554130301103841c90000c011201400d608000c1c0100705007981da100d00c0aa44015211400e1800c01c40ec07901944022030a9031240b0b1000504c003100c002204010b0100a5000d14041c8415240201d0300c02c052001e03440d0a00080c0750740740f50003490710425004000c518850407a0156141c0c0b2002c0d0a40e032201540001044507400341ca40000c103035080766403540e50500210300a14800d40002925505140c44607072502c0c00003135980710280c00098245601d84d000200c490306600104c400b800d0941c0c2e546412410350140140040806003400079958545409034194016502040c049070034960307 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 529119334 1250 529118084 529118101
    0x14090c0a020d1d041104091401150807020a120203041701150308030a090c080a0c0510021c0e0607060e0f010c05180a03050303070c020a0b0307120c020c03010c03090209 74
    0xc600030944025030300c0715400510440c000c0b45006a032200c82c0110b592215400b070041000e64846110742480c01e480014148200744a5220f02950281c039502200034079810000d0003008081c901c407070007040c02800c1e800030700c2d194420407540340e0040e4840d40e070b150000500b52001c0c0d0342c0d8001d4001d00c4030030078500d0303000900b600051140309100301d186c00142c1c92080c9903403210b00240e440501000107040c0c48441013808143c0c0e2b200900c0c01044800002d000702c99090428200d059400c0d0080c500c114205420100c02640c00a1043e1010700d401d4104c140f41c03030b0541415a0110410406603800007030100d034100c10b014160303010422066507503060303d58000303140201a00321005030400001060050240700c2c65450403427041d9400480c05000c0c0713200d50b500c03621850702c0d540040b41e0150000c1c041460040850130900507007001802091013441c01d604014001515500001e00314072613050303884c002035120504c02c1140c24046800035000b08044c0364460030050150600c100c05074081c4003050080340921 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 529120584 1250 529119334 529119337
    0x804090e120c0c013b03120c0726030a0e060d06292a0c0307030b0a06050d1709210102070c050907140304030306050913120807050d110c0102030114090c 67
    0x15080d05401036860320075040b5010411244180d03a61b050310800f8004884845660300401c0c0c19502100108040c40c03928800c80300640039019501c1d0b240740703400d5111a0707015001060325802c130050305000080b4100b01011990718002c5416502c03050b4140000001c03454003c01c050300c168035242e41001001d16425034059030724800c0803210b40d01407101045108031421180e91340c6580520381020b0703c40d0091174000292619050760411f803440c0181100303101e5810b84510461000b01425520b41052404c241c682009515203840d50020b081d00001c2c140d9825907c40c41c41c1031a0b000d51042055030000d42d05490f50007901700403802c4660044656010400c1d04c2c0401d80b00b4801e8405980f44c0441441d0081c20010941006d0022014591a0000458150b480c400014403891940f1546c1d81070713400a0910540d1800350400c0076040c03101503030901034400d07805411180c2c003190f0350300c01181c4040ca141c0c0720f2800d0b10403400084510352000c0700114075071551411550048104079400741c200e488407220210325 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 529121834 1250 529120584 529120637
    0x1020406050a110c21010204260f07120b04020d05010c0e0307050a1202010f30050f0f0a020c100e010605011124060d1e02030709090804090e120c0c01 66
    0x122074100d81a400103041019117440c80c0d8260015040c69511a00c0c11268001d482d41491112400b010466060004101e0f12003200980b00c0100303881442c1002c4d1120a10006d01d01904a440d000c0000341551030f0001450034140c0d00c0301c003c0205503c101c90003440264551056031080c02107601c0002c40745400b1a4980030b807140c000e00c034134040d80f151340151844c1c8144064401485400c0c0d8605818074000c2c1c12286010a40c070700750303040e03480c44c0010660484400500e10165844800c05000c0002c694002d6541d100c2060500169248546008076152003510300b580c0e65605d09185181e2510801034020108464003a00e0782c2d2940003070141c40945031a00c0074941101d52001c4200ca00141c00090f08403a0801c401409103164a1890b80b101481c451010000d240304425640c80b40c2d007141410040e80c4000c04196004002d07104040da01e01c43c0901c11403082d03100d844d40b540401010140140200b44280740c0c2211025650150640c1181d100c2180000290103d0007000302d03240ca0b030303021408050340d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 529123084 1250 529121834 529121839
    0x1a0604020715180506040f020108011a070f142a040c050d05061c03030c02100e0d12021228020a050706051320040f09080406080c070501020406050a110c 67
    0x503030300b0380b20000c0010a00e2402c503582c0203c003030707410b907010a806220943c040c46c05003240a0740200680009894810180c1c0042d0075500d80d902030140751035a0b1010750740810351201084079100d4840c10b001c40da9a86a03100541c050003281c0e0154948814915110401c08251035091142400031081204035040d50751a000856030810842280e03040c00d602550340602c00400c00081075240300301c0e00752403280c484401c60100303583d42254581c0b0350301000390084200b0441e00900a202092100e19210288008a1000c4c4943d03400350b02e03540c01a94066400e0508034460514040c43c0c07004040000c052400d81d503400b003600307414140188501a000b101d464101c0341d21230501e03000c4659504401040004c249168107542c031100040000d00640c083c40b1110050b01c80e50301c0c80c40007a02080211890f42c0b0420241524066003100040c0401d415101212001d0138200319550f40c030348180d160751141150003017165100140100e49990450050f00c07480b2582d64920b41000142002140d540c07550f089400d6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 529124334 1250 529123084 529123103
    0x130f0e100b04090327080d030b01020f0c030c06071e0c0e0703061d09010207020907030b0a060203040e180f0111070c0b1305060f090603090109030e0a2405090603041a06040207 77
    0x560401815205c919807901c054070b003032031583d464452a0420140e000d008000907102c04001d216136a040080600d030b0302c40c240103440362001c0080001d139100c10040c40640140d00c041521824000000d5030408030070041000800500102d02d17003ca11540c0314007502140c61200740101c2d01d82c078840e106403c1a02c607d01e050400d14030b8054407400000000900d4502c00f5902081018016250000b402c3c1c02594141c5001c5581c00582017003180080b6603800400443d0f00600040000c82120300e03800d90007150081d0310a03140d9101d50245801d10311141132100304c13036003081c1c986007021142600901525006800d404801502e40c5401e091620516951a0000c09014000c0c491407510741c00806254220020b000e140c0028000030580e0740e0401c4400c00e4981e50349a00310700905805c030020790245c050441f4008140ca040044e054201003040c00f00d43c20120382d0b5411001268050800c075074488034000c0000da12890980383c000505000d1480c50b05480c11900b0224485052070700a4031910f590000444 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 529125584 1250 529124334 529124357
    0x50901030b0103021f2709140103060b01030207020310051e130606060504081b130609021201121a13081c0b0a081009020d060903020f2a130f0e100b040903 68
    0x110004101801203014901e999000140640c282c0c8100003880c8071948d8000380a41c5141414011210300305510f505240c0100442da00681d4040703903566040020340340004d026101c5a02d0f01892903540300d84c12a080003040c041c0f04160040000950085105400c2030140c0360715900200c2c2c0e00d004521a0030700c0c0e40d00050a4032041c0b41b0100303284500c0400a81008c80d0381d1150783c5540c041e9903182e4041d150155001450030181130100c00c500e40504540e8061203102a141da5514100d000703011028070401d81c91038041f601c80704134400820300c800d811032030154441ca208200ba202c0709445c00b0140c0ca01501e403005c1d001150605644d00002c07105544060110b01d414100700c10064685954220303440080c0d00b0058000541c14812002c07410300a0f030003440c202300801c00c800e10b0300d04082d6000e21003114002c400300300c0741d43c41d084003942081e054032496018400b007042000501101c490070700c107246c104070801000450000e4001c00d00603d40505101a0320801c1c00e01089031000740001c2d00150010880 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 529126834 1250 529125584 529125617
    0x907080a080d0911031b0a0f050108040213060302130f140408030705090102010204080f07030c060c150e011811010f03112b06090207060e03030603060406050709050901030b0103021f 80
    0x58041140512401d800f204c0c20800003034109848200710003d00b140d04c0300001d0107810320840b040003400e482002103140301d00380f03000030380032100003440280300d01f141800424081d80c2c144c2290008582c054003a80d513908110a401c0d003d4485c6007084608240b4107465040c120022013071590169403c00c9003240344d038440d00004c50b122b070f2004120300d041d0b41d001c000004440400b00072210202e107040b000fa2810303a0840c07500320441d0301545d000e10100b084183e031110120782001036041710f007050700b1000140a82c04c03410450243c5504448050100d0926540c4420b0045821411156400c03d9032102070a60708124142c0859044103c40c1c8100c010501024007200440c079400e100742d00840c1041300c44020001007203015a070907074106c0791015402060b00c20410000e030242c0414036280707101035800c529000010a542d05001040580345036120f0707011030b2040d400760b0b01c0d100140602815940b499030310303400e010000d82c0080c80101d0050002c9608104c0051000d141074030320344560b55030344660400b840c01c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 529128084 1250 529126834 529126841
    0x7030305090418231504080705060711030901030c0912060911041a0907020a20030c01050f0702130b030a050f19030f110114090a14030306060904090c050a0e0907080a080d 75
    0x3500c0130340d100341000007035030383d4250b00c43d144240c1c0311320900e942c0c030b0810b40380190a01d0006070140e0305000c24880b109010200210940e50030300f10a1a0014028450304022500e40c2c281e544618102021a104541440016000040128028000d40c10402ea1040601044400000c840c0300410700d140ea5603401450300e6403041d070300000640704460f0000f0040d2204203114000c0140d44500410340c40403118030317080c103100900201100f400c04504152184001c1e1100d0720801c50002d00c11402d10000030b404c810039030700c000b4010b07a004c0d003210484e2a040c0390040da103001d4a156460705214200b2550508030300c81000d9064294580d84420264002300000c0d01d02100e02c1c82c2d21541c43d52140041580d06882156035840340864a000740300340003c0381061025880c41240c0044c0c0c580041040014a40b0380c40c0c129000c9141c00c2ea0009a210584d003442c14000b9466040990b11203a070701c80000721040132480c0c10340a0ba082c00240c07045199034080301c40da05c4504240c0140303c40340034000400813174001c0e403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 529129334 1250 529128084 529128143
    0xb0706090206120f0a230a0b1504231207030f081903050609072a17070309030c08010506010e1005190503011805221407030305090418 59
    0x10140d80c10140f03054450600c406086442e40326003101c0c44204004d20446029000a05a0b10b280c42125004210401100f88200600c550034013a00c9200031051a2228995044011040c440294a40c0c2c3c5440d040074a01e6003551650411094400103807641f0703d4104600403c01000d0f5000708600b40c6076950b18031000c490408280c952400c00c0c81503001007880c2e030511000e019210743e800140740c50040c0820403005d2000d0424030401072040c10004843c0b811550034100c11210309150340703500d9901d03d822190020074042d22a0310100c04600034040541040070403054038420b0076101e440d02d1301c9004603822140121100342c0080e044103495450390030040d42110184205c0d1622078904020303102d10880c0700503c10041400600000010041003c043c0040030404068000c10300050900c080c3c0718400640e2801c95102e07d400c58124a0304000c05403484400042d061400e40d21050b03900c0c2009822031b041654550300039400c100320300c603000114204040c80168440815201d02c840d0310310065820f03213082e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 529130584 1250 529129334 529129339
    0xf05010506090405072003030105041b0206181911030601120512030c041e140607050c19170601091802030d031505120a14010e060406150b03070f020114010b07060902 73
    0x113034012252041e007120b00b1240001e640047d03950b03514040c244411200007401c040100c0d030307034251000107296010130780d81d070801d040341003d10600004901c3c00c0e0800b0210403248580f44040c220310810442c4824070003400c0380007102a0396007603aa803200100ba10030b84140050090308400c005400d02d07090b4502460300003000140c06400c0a48454130545c004009105600642009840400481c6c0c4030904d0114101010783d031040c10210142d41d10341c0d8901e82811064401c00340d454940c3c00001ca10707100c01004140b1601d5141204000d0890302e52a49000e0003a46e1a580c00c00281120216000c0d100442190340540204458801c400c4100c00400b131900200100a12180d400070b2250ba448509801d00115040603107180d010502d0a4001a08007aa40e26003503410b000020442400104209070301c07981285001c0380351100c61a51211000071500101800780002c030910403665400080d84440100341c3c0c008222a0340c81411003c1140000d20078010b00003410404180003450b650405544140b02 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 529131834 1250 529130584 529130597
    0x305090a0f060209040b01032c030f0313050f1609020d1b0509011805010f0c0f050a0f06140c030601050f04050d032105061c0201020f0708100f0501050609040507 71
    0x2039946800c10348604410969841d60080344c14121898640700c3c1056850f4242010801c000340304500c1428031100010503284c0b0500c032120306051520a104850000050301d40c156900e01d0098010307420388203007074019541c80c404c00400780310706074001807000c10f0040414040780d24107182654034806544a016241e914980704e030400180358000411a41800d201500c580e40c60380d8582000402d6090034643e0303440406070420042103980d070002c150b02041100c500d4541d14180c030740d062200c1c1c01700150f07400400c4c502c600e00c07000c028000c103915441242031094409200340c2c0b8aa281400103410256410910403108101064203503001c1d0004041c200b0800039943d08050f40c5c0c03000500c4079220484180e020038450b41e5200d075003017101c1200c41a403441010082005080c44408504070103002500021003030b0004440c8011340e2700030401c0b008200c030410f0440c1c003d02d4641c0301464a5481c2c49066450560902c040151501d0351402564144c580281c0550b0400102c0c030100b101500029005106001c3c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 529133084 1250 529131834 529131853
    0x6030b0d0b250207051318120c21080606070c15020f10050618150d020406090c120605030a021825090e0a020a08060d14030c07090e1c030509 62
    0x42c00300314400e942101d600546007003490300f000d2100c02c107414111a00364600e0110680014560909071030b00c030a401116000186481072020b54003206a02c0f0301030312560004c003250500340c1c00351002011214071031f500d842041d1162424001e1034040d690f4000c1c0a03078100c0d0004c0c00b410342d0328810750300740d0500da2040b114440c0c0c1a2801c241040490301c02c104203d600d44082001c03d082c1006582c24684407941900000d01d0000c1481078400043c4850078455007460300c1c10001e555860304000060040403e003088008080940507000040b841240314030035052a1700000c0310b2601041031003105401415403015280b00c000450410500104442c5046404000d200a1004e4219010035245032035190740310030600b0024440d8414100a043c034903110700420504401503800744080341c22003416256412403128500d08002a102c40604981c0c051001161440e10220000b507848200c8a80352010884a003c00342c45035111003100513039100c08011001c149810a100c1c2d4080390303211820b442541d41d071307a1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 529134334 1250 529133084 529133131
    0x60e0f04150609051e010f0b090d0b070c021e0a180f0507021e0c010c03050c0c0306340519091802070501050f010f060e0a0308030c1306030b0d0b 64
    0x1c000c1e400043c04256034004220101800100002083e403c50b405240c0c950315200c08680c1c051441e000b0701c00744100110701e014141d10740407a5402000c1d480002c4420916024000600006008009078841c03a01c02e40c5180141000300200c10740e5100150003104002e00340403041c1c1d204e943c2c078640c4450150740c808180c45107000310710420303000f40040e030302900310040c1302003840700e100b1494160400355400020710300c01c4030f0781c12180041919600d8100300b502c0340c2d41154001c1c20442011082c9806001d40000c100d54804036500460702e514080c000e41540c1281c500500d80312800d010b200c480070542c01c025407404c44000e2181d0401280103441c100048a46036440310f1510103e9003041c949560300030038020100310080c0503265002040d204200c030f01c1d43c900064480c1c030f20264440d050902610b030195242036103482c461500a1034001c2c0340c05503a41005c00c04441d0692002c0407a68650404200128903144a805041c00000d001400c034070441d040740d01d8415a01501800c01207a149042c922442c586 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 529135584 1250 529134334 529134341
    0xc1303050703050a0201021c090501080c0705010c030c020d0e0625060e01020304060b100f050a091205070602060714091003020405030613050d0e090c2505100f060e0f0415 75
    0xa51040004d00083c011520029190600d10f00e6440c458075400000700b0321752580700316848219042445e04960580343c0034800b0034a48212100a0b000f9420130641070026a0136803c071101501180e0b00701c03542081e08003c00c803404d07560007860b01d500c1003040040054031070410420030158215803c0450250b01c07569598000c4804c0c1c0d004c8c40b821a5008800c0109016003440b84031300c100ca003966a0b0014200c150f4009020308000030101050250205540080c140702c2d071a128094410710b11507201110392803d02d00e43d50b059038460040103100d10000651868480d400b49003190485143c8282041d01d00c00801941001c620007a004150307090000040c00e036020402140210300b400d800110688003800c02743c0c1004010218141409001c00c0d8002c01030b04d810711016400304908074036540310b410050f1a00c0b030010411444107007074040580030100b80000414030f00d2148050301010071010030400d0081c0180c1d0440d114860446c60b091001410700c1e03a8803950300d5400b501c02d80000300f4500f43c03000f002044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 529136690 1106 529135584 529135589
    0x609060d1212090507050a090209060304060e150f04060c020303090c091e0f0109050703150302010507170d09030206060f03060105010f020309090a050f130201080c13030507 76
    0x400d10488107010702c00d1619000b0b001c2548281002c1ea0b445101d406181c0c45218280d100140b008030610031500e1005002e4105030a41e40c80d13849001c001c0810542e84295402500303801892500041502d03841a0030030034081c00d0500300307800c100d802c64454400f42d400750b60007013051040302240007482200d000307421151000e081d59401811118041080c0030000c0161808041c000240100a80300341651301c140820400c1f030741d42c0c0c0e07003c40c29100c211807480c0b000384c4074100c10301c00341d4403a10040201502880c880c400014050103d104c40750702c607203e4100080d40c3c1d0340001042550501005130001d0084a484000c110f441d00029101c0750306100c0c060502000d40c600c089054000d03c1a00c810400003405030301107141a903a49000303444110384000450030300a0028256405031064003a542c4d4040e9580c0304655030300e084110080d03010812540e0411200700d40040003035800c0200601 = true := by decide +kernel

theorem cover : BRFrame.Cov 528956834 529136690 := by
  have h0 := BRFrame.cov_init 528956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 528956834 ≤ n) (h2 : n < 529136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
