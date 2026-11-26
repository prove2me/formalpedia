-- Prove2me | solution 1 for ClassicalComplexWPT.norm_normalizedScale_sub_monomial_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:07:19.083923+00:00
-- url     : https://prove2.me/submissions/c820389e-552d-44de-9ae2-7a1c6cc3b820

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Theorems.Thm_ClassicalComplexWPT_normalizedScale_sub_monomial_apply_lt

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {t : ℝ≥0} (ht : t ≤ 1) (ht0 : 0 < t)
    (f : OriginSeq) (d : ℕ) (hlow : ∀ j < d, f j = 0) (hfd : f d ≠ 0) :
    ‖normalizedScale t ht f d - monomialSeq d‖ ≤
      ((t : ℝ) / ‖f d‖) * ‖f‖ := by
  rw [L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm]
  have hsright : Summable (fun k ↦ ((t : ℝ) / ‖f d‖) * ‖f k‖) :=
    (L1Coeff.summable_norm f).mul_left _
  calc
    (∑' k, ‖(normalizedScale t ht f d - monomialSeq d) k‖) ≤
        ∑' k, ((t : ℝ) / ‖f d‖) * ‖f k‖ := by
      apply Summable.tsum_le_tsum
      · intro k
        exact normalizedScale_sub_monomial_apply_lt ht ht0 f d k hlow hfd
      · exact L1Coeff.summable_norm _
      · exact hsright
    _ = ((t : ℝ) / ‖f d‖) * ∑' k, ‖f k‖ := by rw [tsum_mul_left]
end ClassicalComplexWPT
