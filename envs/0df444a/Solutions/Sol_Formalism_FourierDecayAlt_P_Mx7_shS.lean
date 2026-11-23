-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.shS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:31:57.017731+00:00
-- url     : https://prove2.me/submissions/c27ebf6a-813b-4c59-b046-07da63e438c0

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_star_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_kap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (hSh : SSShift) (P : Par) (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    star (SS P l) * kap P g = kap P f * star (SS P l) := by
  have h1 := hSh P l (fun π => star (f π)) (fun π => star (g π)) (fun π π' hu => by simp only [h π π' hu])
  have h2 := congrArg star h1
  rw [star_mul, star_mul, star_kap, star_kap] at h2
  simpa only [star_star] using h2
end Formalism.FourierDecayAlt.P.Mx7
