-- Prove2me | solution 1 for CompanionTheory.ThKF.E.exists_rho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:12.794797+00:00
-- url     : https://prove2.me/submissions/42381e8d-da8e-4bb2-8049-d3393b1f01cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_CompanionTheory_ThickeningEstimates_InnerProductFactorization_EqOfInner
import Theorems.Thm_GlobalTheory_Published_Metaplectic_eChar_apply
import Theorems.Thm_GlobalTheory_Published_Metaplectic_hasTemperateGrowth_eChar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKF CompanionTheory.ThKF.E
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKF.E
theorem _root_.solution (w : l ⊕ l → ℝ) (f : Sch l) : ∃ g : Sch l, ⇑g = rhoFun w f := by
  have ht : Function.HasTemperateGrowth (phase w) := by
    have h2 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫ + ⟪pPart w, qPart w⟫ / 2 :=
      (innerSL ℝ (qPart w)).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    have h3 := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp h2
    convert h3 using 1
    funext x
    simp only [phase, Function.comp, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  refine ⟨smulLeftCLM ℂ (phase w) (compSubConstCLM ℂ (-pPart w) f), ?_⟩
  funext x
  rw [smulLeftCLM_apply_apply ht]
  simp [rhoFun]
end CompanionTheory.ThKF.E
