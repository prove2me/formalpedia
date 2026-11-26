-- Prove2me | solution 1 for ClassicalComplexWPT.normalizedPreparationTail_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:28.519833+00:00
-- url     : https://prove2.me/submissions/b8d986cc-424d-42b7-b078-ef1b3e60eb09

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Theorems.Thm_ClassicalComplexWPT_analyticNormalizedCoefficientMap_zero
import Theorems.Thm_ClassicalComplexWPT_exactOrderInLastVariable_iff_lastTaylorCoefficients
import Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
attribute [local simp] ClassicalComplexWPT.normalizedOriginCoeffs_apply



set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) (r : ℝ≥0) (hr0 : 0 < r)
    (hr : (r : ℝ≥0∞) < p.radius) {k : ℕ} (hk : k ≤ d) :
    normalizedPreparationTail p r hr d 0 k = 0 := by
  rw [normalizedPreparationTail, analyticNormalizedCoefficientMap_zero]
  by_cases hkd : k < d
  · change normalizedOriginCoeffs p r hr d k - monomialSeq d k = 0
    rw [normalizedOriginCoeffs_apply]
    have hcoeff : lastTaylorCoefficient p k 0 = 0 :=
      ((exactOrderInLastVariable_iff_lastTaylorCoefficients p hp).mp horder).1 k hkd
    rw [hcoeff, mul_zero, mul_zero]
    rw [monomialSeq_apply_ne (ne_of_lt hkd), sub_zero]
  · have hkeq : k = d := le_antisymm hk (Nat.le_of_not_gt hkd)
    subst k
    change normalizedOriginCoeffs p r hr d d - monomialSeq d d = 0
    rw [normalizedOriginCoeffs_apply, monomialSeq_apply_same]
    have htop : (r : ℂ) ^ d * lastTaylorCoefficient p d 0 ≠ 0 := by
      have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      exact mul_ne_zero (pow_ne_zero _ hrC)
        ((exactOrderInLastVariable_iff_lastTaylorCoefficients p hp).mp horder).2
    rw [inv_mul_cancel₀ htop, sub_self]
end ClassicalComplexWPT
