-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.sss_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:41.772712+00:00
-- url     : https://prove2.me/submissions/6a3dc3df-7f20-4492-9e21-d98b85bd58e2

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_ss_shift

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
    star (SS P l) * kap P g = kap P f * star (SS P l) := by
  have h2 := ss_shift P l (fun π => star (f π)) (fun π => star (g π)) (fun π π' hu => by rw [h π π' hu])
  have h3 := congrArg star h2
  rw [star_mul, star_mul, star_kap, star_kap] at h3
  simp only [star_star] at h3
  exact h3
end Formalism.FourierDecayAlt.P.Mx5
