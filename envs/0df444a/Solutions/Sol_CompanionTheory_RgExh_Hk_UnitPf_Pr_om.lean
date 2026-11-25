-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.UnitPf.Pr_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:35:02.83181+00:00
-- url     : https://prove2.me/submissions/013f75e8-5333-461d-ac28-3fde244d483b

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_ContOfFnProd
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExh_commute_qdet_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet qminor Tm GlRel)
open Formalism.QuantumDeterminants (capP)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor)
open CompanionTheory.RgExh
variable {m : ℕ} (X : GMod (m + 1)) (χ : Fin (m + 1) → ℂ) (s : Fin (m + 1))
variable {X χ s}
namespace CompanionTheory.RgExh.Hk.UnitPf
theorem _root_.solution (f : Fin (m + 1) → X.V) : Pr X χ s (om X f) = om X (Pr X χ s f) := by
  have hc := GlobalTheory.CompanionTheory.RgExh.commute_qdet_of (tensE X) (om X) (fun a b => commute_om X a b) (omg χ s)
  simp only [Pr, LinearMap.smul_apply, map_smul]
  congr 1
  exact LinearMap.congr_fun hc.eq f
end CompanionTheory.RgExh.Hk.UnitPf
