-- Prove2me | solution 1 for CompanionTheory.ThKF.E.exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:35.034651+00:00
-- url     : https://prove2.me/submissions/cf11672e-c036-4b7b-98ef-bf9f415a1694

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_CompanionTheory_ThickeningEstimates_InnerProductFactorization_EqOfInner

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
theorem _root_.solution (x : EuclideanSpace ℝ l) : ∃ φ : Sch l, φ x ≠ 0 := by
  obtain ⟨f, h1, h2, h3, -, h4⟩ := exists_contDiff_tsupport_subset (n := ⊤) (s := Set.univ) (x := x) Filter.univ_mem
  refine ⟨(h2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).toSchwartzMap (ofRealCLM.contDiff.comp h3), ?_⟩
  show ((f x : ℝ) : ℂ) ≠ 0
  simp [h4]
end CompanionTheory.ThKF.E
