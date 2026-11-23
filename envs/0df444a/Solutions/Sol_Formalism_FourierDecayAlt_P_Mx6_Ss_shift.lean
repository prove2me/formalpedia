-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.Ss_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:10.791235+00:00
-- url     : https://prove2.me/submissions/73dbd1b2-5382-4981-98a9-8859a4ac0a38

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_S_shift

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    star (SS P l) * kap P g = kap P f * star (SS P l) := by
  have h1 := S_shift P l (fun π => star (f π)) (fun π => star (g π)) (fun π π' hu => by rw [h π π' hu])
  have h2 := congrArg star h1
  rw [star_mul, star_mul, star_kap, star_kap] at h2
  simpa using h2
end Formalism.FourierDecayAlt.P.Mx6
