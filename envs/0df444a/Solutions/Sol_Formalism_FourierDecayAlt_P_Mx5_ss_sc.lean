-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.ss_sc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:51.699257+00:00
-- url     : https://prove2.me/submissions/06490b0e-8dc7-45e6-9bc1-0b877dfa86aa

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution (l : ℕ) (w : Pr P.r) : Commute (SS P l) (sc P w) := by
  unfold sc
  show SS P l * Matrix.scalar _ w = Matrix.scalar _ w * SS P l
  ext i j
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold SS
  rw [Matrix.of_apply]
  split_ifs
  · exact Algebra.commutes (R := ℂ) _ _
  · rw [zero_mul, mul_zero]
end Formalism.FourierDecayAlt.P.Mx5
