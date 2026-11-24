-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_RdV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:21:19.760331+00:00
-- url     : https://prove2.me/submissions/a878963c-8eb8-4bbf-bb11-fcb59874428a

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hasDerivAt_of_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
theorem _root_.solution {m : ℕ∞} {f : Mat k r → E} {g X : Mat k r} (hX : inLie k r X) (h : Loc (m + 1) f g) :
    Loc m (RdV X f) g := by
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h
  refine ⟨U, fun x => fderiv ℝ f' x (x * X), hU, hgU, ?_, ?_⟩
  · have h1 := hf'.fderiv_of_isOpen (m := (m : WithTop ℕ∞)) hU (by push_cast; exact le_rfl)
    exact h1.clm_apply (mulRightRealCLM X).contDiff.contDiffOn
  · intro x hx hxG
    have hd : DifferentiableAt ℝ f' x :=
      (hf'.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    exact (hasDerivAt_of_ext hU hx hxG hX hd he).deriv
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
