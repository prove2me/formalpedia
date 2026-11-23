-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.herm_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:21.305215+00:00
-- url     : https://prove2.me/submissions/2cd0bb8e-9dd4-431f-9f9a-b77cfb49fa9f

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd4
theorem _root_.solution {RR : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)} (h : (d0 RR * T)ᴴ = d0 RR * T) :
    (d0 RR * Tᵀ)ᴴ = d0 RR * Tᵀ := by
  ext1 i j
  have h' := congrFun (congrFun h j) i
  unfold d0 at h' ⊢
  rw [Matrix.conjTranspose_apply, Matrix.diagonal_mul] at h' ⊢
  rw [Matrix.diagonal_mul] at h' ⊢
  exact h'
end Formalism.FourierDecayAlt.P.Wd4
