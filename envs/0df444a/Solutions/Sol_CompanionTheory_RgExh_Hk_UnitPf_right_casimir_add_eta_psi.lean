-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.UnitPf.right_casimir_add_eta_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:23:16.496066+00:00
-- url     : https://prove2.me/submissions/984b2032-27e1-4813-a662-826570e62b4b

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_right_casimir_apply
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_eta_apply
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_psi_apply

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
theorem _root_.solution (H : Fin (m + 1) → Fin (m + 1) → X.V) (a d : Fin (m + 1)) :
    (y2 X H + eta X (psi X H)) a d = -∑ c, X.E a c (H c d) := by
  rw [Pi.add_apply, right_casimir_apply, eta_apply, psi_apply]
  simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply, tensE_apply]
  rw [Finset.sum_add_distrib]
  by_cases h : d = a
  · subst h; simp [Pi.single_eq_same]
  · simp [h, Pi.single_eq_of_ne h]
end CompanionTheory.RgExh.Hk.UnitPf
