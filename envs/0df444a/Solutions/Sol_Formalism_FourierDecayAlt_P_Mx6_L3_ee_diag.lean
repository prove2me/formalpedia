-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L3.ee_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:11.345358+00:00
-- url     : https://prove2.me/submissions/1f76612b-4bfa-442c-a427-e3737010a749

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_good0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_goodm1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_good0

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L3
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6.L3
theorem _root_.solution {i : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    ee P i i u v = 0 := by
  funext π
  have h1 := good0 P hu π hi
  have h2 := good0 P hv π hi
  have h3 := goodm1 P hu π hi
  have h4 := goodm1 P hv π hi
  simp only [ee, sh, rr, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Pi.zero_apply, if_true]
  field_simp
  ring
end Formalism.FourierDecayAlt.P.Mx6.L3
