-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.UnitPf.right_casimir_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:28:47.768103+00:00
-- url     : https://prove2.me/submissions/10104ea5-af47-44ff-ad2f-9737ff5b150f

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_left_casimir_apply
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_right_casimir_apply
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_eta_apply
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_sum_tensE_single

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
theorem _root_.solution (v : X.V) : y2 X (eta X v) = -(y1 X (eta X v) + ((m + 1 : ℕ) : ℂ) • eta X v) := by
  funext a
  rw [right_casimir_apply]
  simp only [eta_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, left_casimir_apply]
  rw [sum_tensE_single]
end CompanionTheory.RgExh.Hk.UnitPf
