-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.rho_up
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:32.017862+00:00
-- url     : https://prove2.me/submissions/1e542d9e-6243-4e7e-90d0-b96db485a6f8

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rhoUp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_rhoUp


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
theorem _root_.solution {l : ℕ} {π π' : Ty P} (h : Up P l π π') {i : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) :
    (rho P π' i : ℂ) = (rho P π i : ℂ) + if i = l then 1 else 0 := by
  rw [Mx3.rhoUp P l π π' h i hi]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Mx6
