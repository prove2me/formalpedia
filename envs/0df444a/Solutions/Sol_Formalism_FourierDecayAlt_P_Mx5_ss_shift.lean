-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.ss_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:23:42.122679+00:00
-- url     : https://prove2.me/submissions/f2c59db8-8a46-448f-8b39-b0d9a937c6e3

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_kap_eq


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
theorem _root_.solution (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    kap P g * SS P l = SS P l * kap P f := by
  rw [kap_eq, kap_eq]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  unfold SS
  rw [Matrix.of_apply]
  split_ifs with hu
  · rw [h j i hu, ← map_mul, ← map_mul, mul_comm]
  · rw [zero_mul, mul_zero]
end Formalism.FourierDecayAlt.P.Mx5
