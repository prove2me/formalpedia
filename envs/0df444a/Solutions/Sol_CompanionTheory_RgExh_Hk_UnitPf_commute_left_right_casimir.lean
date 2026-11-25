-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.UnitPf.commute_left_right_casimir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:11:06.781355+00:00
-- url     : https://prove2.me/submissions/72175c71-9198-456c-bdc5-f2b739c85b20

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_left_casimir_apply
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_right_casimir_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedVariables false
open Finset
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh
variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}
namespace CompanionTheory.RgExh.Hk.UnitPf
theorem _root_.solution : Commute (y1 X) (y2 X) := by
  refine LinearMap.ext fun H => funext fun a => ?_
  simp only [Module.End.mul_apply, left_casimir_apply, right_casimir_apply, map_neg, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact (LinearMap.congr_fun (commute_om X a c).eq (H c)).symm
end CompanionTheory.RgExh.Hk.UnitPf
