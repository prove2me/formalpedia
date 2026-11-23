-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L3.lam_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:22.097381+00:00
-- url     : https://prove2.me/submissions/e6d538e8-dd01-4c12-91c4-853dca08bc2a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_S_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_rho_up

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
theorem _root_.solution (i : ℕ) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (a b : ℂ) :
    lam P i a * lam P j b = kap P (rr P i a * sh P i j b) * (SS P i * SS P j) := by
  have h := S_shift P i (rr P j b) (sh P i j b) (fun π π' hU => by
    simp only [sh, rr]
    rw [rho_up P hU hj]
    congr 1
    ring)
  unfold lam
  calc kap P (rr P i a) * SS P i * (kap P (rr P j b) * SS P j)
      = kap P (rr P i a) * (SS P i * kap P (rr P j b)) * SS P j := by simp only [mul_assoc]
    _ = kap P (rr P i a) * (kap P (sh P i j b) * SS P i) * SS P j := by rw [h]
    _ = _ := by rw [← kap_mul]; simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Mx6.L3
