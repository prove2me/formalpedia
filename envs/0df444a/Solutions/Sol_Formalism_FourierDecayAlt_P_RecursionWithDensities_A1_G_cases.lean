-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.G_cases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:36.965905+00:00
-- url     : https://prove2.me/submissions/4f568a08-3be3-421a-b33f-905d2eccb5fc

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {α : Type}
variable {E : Type} [AddCommGroup E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution (L : AddSubgroup E) (S : Finset E) (Th : E → α → α → ℂ) (c : E ⧸ L) :
    ((¬ ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c) ∧ G L S Th c = fun _ _ => 0) ∨
      ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c ∧ G L S Th c = Th t₁ := by
  by_cases hc : ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c
  · right
    refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, ?_⟩
    unfold G
    rw [dif_pos hc]
  · left
    refine ⟨hc, ?_⟩
    unfold G
    rw [dif_neg hc]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
