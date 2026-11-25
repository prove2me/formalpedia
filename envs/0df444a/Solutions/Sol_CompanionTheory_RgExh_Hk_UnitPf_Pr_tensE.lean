-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.UnitPf.Pr_tensE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:59:12.336557+00:00
-- url     : https://prove2.me/submissions/0260ecaa-b65f-4698-9f62-41f6956deb4e

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_ContOfFnProd
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne
import Theorems.Thm_Formalism_REAL_qDetCentral


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
theorem _root_.solution (a b : Fin (m + 1)) (f : Fin (m + 1) → X.V) :
    Pr X χ s (tensE X a b f) = tensE X a b (Pr X χ s f) := by
  have hc := Formalism.REAL.qDetCentral (Module.End ℂ (Fin (m + 1) → X.V)) (m + 1) (tensE X) (glRel_tensE X) (omg χ s) a b
  simp only [Pr, LinearMap.smul_apply, map_smul]
  congr 1
  exact LinearMap.congr_fun hc f
end CompanionTheory.RgExh.Hk.UnitPf
