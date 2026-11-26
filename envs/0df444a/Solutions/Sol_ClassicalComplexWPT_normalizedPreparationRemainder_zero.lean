-- Prove2me | solution 1 for ClassicalComplexWPT.normalizedPreparationRemainder_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:12:56.128187+00:00
-- url     : https://prove2.me/submissions/192316c5-8b8e-4393-abe2-efb9ecb4aeba

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Theorems.Thm_ClassicalComplexWPT_convolution_apply_eq_zero_of_right
import Theorems.Thm_ClassicalComplexWPT_normalizedPreparationTail_zero_of_le
import Theorems.Thm_ClassicalComplexWPT_seqDivisionRemainderGlobal_eq


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
    (hr : (r : ℝ≥0∞) < p.radius)
    (hsmall : ‖normalizedPreparationTail p r hr d 0‖ < 1) :
    normalizedPreparationRemainder p r hr d 0 = 0 := by
  rw [normalizedPreparationRemainder, seqDivisionRemainderGlobal_eq d _ _ hsmall]
  apply lp.ext
  funext k
  by_cases hk : k < d
  · rw [seqDivisionRemainder, seqLowCut_apply_of_lt d _ hk]
    change monomialSeq d k - convolution
      (seqDivisionQuotient d (normalizedPreparationTail p r hr d 0) hsmall
        (monomialSeq d)) (normalizedPreparationTail p r hr d 0) k = 0
    rw [monomialSeq_apply_ne (ne_of_lt hk)]
    rw [convolution_apply_eq_zero_of_right (fun j hj ↦
      normalizedPreparationTail_zero_of_le p hp horder r hr0 hr (hj.trans hk.le))]
    exact sub_zero 0
  · rw [seqDivisionRemainder, seqLowCut_apply_of_le d _ (Nat.le_of_not_gt hk)]
    rfl
end ClassicalComplexWPT
