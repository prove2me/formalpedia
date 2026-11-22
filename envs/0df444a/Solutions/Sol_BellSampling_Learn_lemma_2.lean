-- Prove2me | solution 1 for BellSampling.Learn.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:27:54.647597+00:00
-- url     : https://prove2.me/submissions/e84f2909-ff2c-4b27-998a-3640b07a32c3

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace Aux_Bell_l2
open BellSampling.Learn

lemma cases4 : ∀ c : ZMod 2 × ZMod 2, c = (0, 0) ∨ c = (0, 1) ∨ c = (1, 0) ∨ c = (1, 1) := by
  decide

lemma bell1_eq (c : ZMod 2 × ZMod 2) (a b : Bool) :
    bell1 c a b = ((1 / Real.sqrt 2 : ℝ) : ℂ) * sigma1 c a b := by
  rcases cases4 c with rfl | rfl | rfl | rfl <;> cases a <;> cases b <;>
    simp [bell1, ket2, sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide]

lemma sig1_real (c : ZMod 2 × ZMod 2) (a b : Bool) : star (sigma1 c a b) = sigma1 c a b := by
  rcases cases4 c with rfl | rfl | rfl | rfl <;> cases a <;> cases b <;>
    simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide]

lemma bellVec_eq {n : ℕ} (r : PStr n) (x y : Bits n) :
    bellVec r x y = ((1 / Real.sqrt 2 : ℝ) : ℂ) ^ n * sigma r x y := by
  unfold bellVec sigma
  simp only [Matrix.of_apply, bell1_eq, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

lemma sigma_real {n : ℕ} (r : PStr n) (x y : Bits n) : star (sigma r x y) = sigma r x y := by
  unfold sigma
  simp only [Matrix.of_apply]
  rw [star_prod]
  simp_rw [sig1_real]

end Aux_Bell_l2

open BellSampling.Learn in
theorem solution {n : ℕ} (ψ : QState n) (r : PStr n) :
    bellProb ψ r = ‖∑ x, ∑ y, star (ψ x) * sigma r x y * star (ψ y)‖ ^ 2 / 2 ^ n := by
  set k : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ) ^ n with hk
  have hkstar : star k = k := by
    rw [hk, star_pow, Complex.star_def, Complex.conj_ofReal]
  have key : ∑ x, ∑ y, star (bellVec r x y) * (ψ x * ψ y) =
      k * ∑ x, ∑ y, sigma r x y * (ψ x * ψ y) := by
    simp_rw [Aux_Bell_l2.bellVec_eq, star_mul', Aux_Bell_l2.sigma_real, ← hk, hkstar,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    ring
  have key2 : ∑ x, ∑ y, star (ψ x) * sigma r x y * star (ψ y) =
      star (∑ x, ∑ y, sigma r x y * (ψ x * ψ y)) := by
    rw [star_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [star_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [star_mul', star_mul', Aux_Bell_l2.sigma_real]
    ring
  have hknorm : ‖k‖ ^ 2 = 1 / 2 ^ n := by
    rw [hk, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), ← pow_mul, mul_comm, pow_mul, div_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), one_pow, div_pow, one_pow]
  unfold bellProb
  rw [key, key2, norm_star, norm_mul, mul_pow, hknorm]
  ring
