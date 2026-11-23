-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.IsPoly.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:35.955064+00:00
-- url     : https://prove2.me/submissions/79ab7a2a-f5a5-4701-9c07-264a8f29c007

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_dual
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.PC
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W
noncomputable section
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx6.PC
namespace IsPoly
theorem _root_.solution {f : ℂ → B} (hf : IsPoly f) (S : Set ℂ) (hS : S.Finite) (h : ∀ y, y ∉ S → f y = 0) (y : ℂ) :
    f y = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  obtain ⟨s, hs⟩ := hf.dual φ
  have h0 : s = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot s (Set.Infinite.mono ?_ hS.infinite_compl)
    intro z hz
    show s.eval z = 0
    rw [← hs]
    show φ (f z) = 0
    rw [h z hz, map_zero]
  have h1 : φ (f y) = s.eval y := hs y
  rw [h1, h0, eval_zero]
end IsPoly
end Formalism.FourierDecayAlt.P.Mx6.PC
