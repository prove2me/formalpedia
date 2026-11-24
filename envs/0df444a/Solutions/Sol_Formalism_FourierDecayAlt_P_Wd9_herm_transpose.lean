-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.herm_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:32.493108+00:00
-- url     : https://prove2.me/submissions/ecbc7638-f4e5-43f9-b8f1-fc1f9f06c23b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd9
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))
namespace Formalism.FourierDecayAlt.P.Wd9
theorem _root_.solution {RR : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)}
    (h : (d0 RR * M)ᴴ = d0 RR * M) : (d0 RR * Mᵀ)ᴴ = d0 RR * Mᵀ := by
  refine Matrix.ext fun i j => ?_
  have h1 := congrFun (congrFun h j) i
  rw [Matrix.conjTranspose_apply, d0, Matrix.diagonal_mul] at h1
  rw [Matrix.conjTranspose_apply, d0, Matrix.diagonal_mul, Matrix.diagonal_mul,
    Matrix.transpose_apply, Matrix.transpose_apply]
  rw [Matrix.diagonal_mul] at h1
  exact h1
end Formalism.FourierDecayAlt.P.Wd9
