-- Prove2me | solution 1 for EulerMascheroni.P2.factorial_binomial_prime_digit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T19:54:35.046236+00:00
-- url     : https://prove2.me/submissions/8caa4701-0fad-4281-999e-9e75ff207fd2

import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic

open scoped BigOperators

namespace P2Digit

lemma lucas (n k p : ℕ) (hp : p.Prime) :
    (n.choose k : ZMod p) =
      ((n%p).choose (k%p) : ZMod p) * ((n/p).choose (k/p) : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p))

lemma low_choose (a b j p : ℕ) (hp : p.Prime) (hb : b < p) (hj : j < p) :
    ((a*p+b).choose j : ZMod p) = (b.choose j : ZMod p) := by
  rw [lucas _ _ p hp]
  simp [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]

lemma second_choose (a b j p : ℕ) (hp : p.Prime) (hb : b < p) (hj : j ≤ b) :
    ((2*(a*p+b)-j).choose (a*p+b) : ZMod p) =
      ((2*a).choose a : ZMod p) * ((2*b-j).choose b : ZMod p) := by
  have hn : 2*(a*p+b)-j = (2*a)*p+(2*b-j) := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_sub_assoc (by omega : j ≤ 2*b)]
  rw [hn, lucas _ _ p hp]
  have hbp : (a*p+b)%p=b := by simp [Nat.mod_eq_of_lt hb]
  have hbd : (a*p+b)/p=a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp.pos, Nat.div_eq_of_lt hb, zero_add]
  rw [hbp,hbd]
  by_cases hc : 2*b-j < p
  · have hdm : ((2*a)*p+(2*b-j))/p = 2*a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp.pos, Nat.div_eq_of_lt hc, zero_add]
    have hmm : ((2*a)*p+(2*b-j))%p = 2*b-j := by simp [Nat.mod_eq_of_lt hc]
    rw [hdm,hmm]
    ring
  · have hl : (2*b-j)%p < b := by
      have htop : 2*b-j < 2*p := by omega
      have he : (2*b-j)%p = 2*b-j-p := Nat.mod_eq_sub_mod (by omega) |>.trans
        (Nat.mod_eq_of_lt (by omega))
      omega
    have hz : ((2*b-j).choose b : ZMod p) = 0 := by
      rw [lucas _ _ p hp, Nat.mod_eq_of_lt hb,
        Nat.choose_eq_zero_of_lt hl]
      simp
    rw [hz,mul_zero]
    have hm : ((2*a)*p+(2*b-j))%p = (2*b-j)%p := by simp
    rw [hm,Nat.choose_eq_zero_of_lt hl]
    simp

lemma term (a b j p : ℕ) (hp : p.Prime) (hb : b < p) (hj : j < p) :
    (j.factorial : ZMod p) * ((a*p+b).choose j : ZMod p)^3 *
      ((2*(a*p+b)-j).choose (a*p+b) : ZMod p)^2 =
    ((2*a).choose a : ZMod p)^2 *
      ((j.factorial : ZMod p) * (b.choose j : ZMod p)^3 *
        ((2*b-j).choose b : ZMod p)^2) := by
  rw [low_choose a b j p hp hb hj]
  by_cases hjb : j ≤ b
  · rw [second_choose a b j p hp hb hjb]
    ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : b < j)]
    simp

lemma truncate (c : ℕ → ℕ) (M J q : ℕ) (h : q ∣ J.factorial) :
    (∑ j ∈ Finset.range M, j.factorial * c j) ≡
      (∑ j ∈ Finset.range (min M J), j.factorial * c j) [MOD q] := by
  induction M with
  | zero => simp [Nat.ModEq]
  | succ M ih =>
    by_cases hm : M < J
    · rw [min_eq_left (Nat.succ_le_of_lt hm)]
    · have hJM : J ≤ M := le_of_not_gt hm
      have hd : q ∣ M.factorial * c M :=
        dvd_mul_of_dvd_left (h.trans (Nat.factorial_dvd_factorial hJM)) _
      have hz : M.factorial * c M ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr hd
      simpa only [Finset.sum_range_succ, min_eq_right hJM,
        min_eq_right (hJM.trans (Nat.le_succ M)), add_zero] using ih.add hz

def U (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n+1), j.factorial * (n.choose j)^3 * ((2*n-j).choose n)^2

lemma trunc (n p : ℕ) (hp : p.Prime) :
    (U n : ZMod p) =
      ∑ j ∈ Finset.range (min (n+1) p),
        (j.factorial : ZMod p) * (n.choose j : ZMod p)^3 *
          ((2*n-j).choose n : ZMod p)^2 := by
  have hd : p ∣ p.factorial := Nat.dvd_factorial hp.pos le_rfl
  have ht := truncate
    (fun j => (n.choose j)^3 * ((2*n-j).choose n)^2) (n+1) p p hd
  have he := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ht
  simpa [U, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, mul_assoc] using he

lemma digit (a b p : ℕ) (hp : p.Prime) (hb : b < p) :
    (U (a*p+b) : ZMod p) = ((2*a).choose a : ZMod p)^2 * (U b : ZMod p) := by
  have hle : b+1 ≤ min (a*p+b+1) p := le_min (by omega) (by omega)
  have hs : (U b : ZMod p) =
      ∑ j ∈ Finset.range (min (a*p+b+1) p),
        (j.factorial : ZMod p) * (b.choose j : ZMod p)^3 *
          ((2*b-j).choose b : ZMod p)^2 := by
    unfold U
    push_cast
    apply Finset.sum_subset (Finset.range_mono hle)
    intro j _ hj
    have hjb : b < j := by simpa using hj
    rw [Nat.choose_eq_zero_of_lt hjb]
    simp
  rw [trunc _ _ hp, hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact term a b j p hp hb
    (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _))

end P2Digit

theorem solution (a b p : ℕ) (hp : p.Prime) (hb : b < p) :
    (∑ j ∈ Finset.range (a*p+b+1),
      j.factorial * ((a*p+b).choose j)^3 * ((2*(a*p+b)-j).choose (a*p+b))^2) ≡
    (2*a).choose a ^ 2 *
      (∑ j ∈ Finset.range (b+1), j.factorial * (b.choose j)^3 * ((2*b-j).choose b)^2)
      [MOD p] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simpa [P2Digit.U, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using P2Digit.digit a b p hp hb


