-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.place_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:29.386918+00:00
-- url     : https://prove2.me/submissions/28195a27-7153-4ccc-9630-b8f34a96b3fd

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_plc_prime
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_sum_lw_vw_natCast_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : PlaceSum := by
  unfold PlaceSum
  intro K _ _ _ S X hX
  rw [← Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem plc hw)]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp0 : p ≠ 0 := by
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hp
    rw [← hw]
    exact (plc_prime w).ne_zero
  have e : ∑ w ∈ S with plc w = p, lw w * ((ramw w : ℝ) * X (plc w)) =
      (∑ w ∈ S with plc w = p, lw w * (vw w (p : K) : ℝ)) * X p := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    have h4 : plc w = p := (Finset.mem_filter.mp hw).2
    unfold ramw
    rw [h4]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (sum_lw_vw_natCast_le _ p hp0) (hX p)
end Formalism.EigenvalueLevelCeiling
