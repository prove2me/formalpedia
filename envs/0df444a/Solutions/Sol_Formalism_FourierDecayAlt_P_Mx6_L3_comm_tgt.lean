-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L3.comm_tgt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:24.621273+00:00
-- url     : https://prove2.me/submissions/e7d47b1d-2a33-4971-bc8b-ddd221f9572d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
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
theorem _root_.solution (hC : SSComm) (hP : P.OK) {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1))
    (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i) :
    (kap P fun π => (rho P π j : ℂ) - (rho P π i : ℂ) - 1) * (SS P j * SS P i) =
      (kap P fun π => (rho P π j : ℂ) - (rho P π i : ℂ) + 1) * (SS P i * SS P j) := by
  have h := hC P hP i hi j hj hne
  have a1 := S_shift P i (fun π => ((rho P π j - rho P π i - 1 : ℝ) : ℂ))
    (fun π => (rho P π j : ℂ) - (rho P π i : ℂ)) (fun π π' hU => by
      rw [rho_up P hU hj, rho_up P hU hi, if_neg hne, if_pos rfl]
      push_cast
      ring)
  have a2 := S_shift P j (fun π => (rho P π j : ℂ) - (rho P π i : ℂ))
    (fun π => (rho P π j : ℂ) - (rho P π i : ℂ) - 1) (fun π π' hU => by
      rw [rho_up P hU hj, rho_up P hU hi, if_neg hne.symm, if_pos rfl]
      ring)
  have b1 := S_shift P j (fun π => ((rho P π j - rho P π i + 1 : ℝ) : ℂ))
    (fun π => (rho P π j : ℂ) - (rho P π i : ℂ)) (fun π π' hU => by
      rw [rho_up P hU hj, rho_up P hU hi, if_neg hne.symm, if_pos rfl]
      push_cast
      ring)
  have b2 := S_shift P i (fun π => (rho P π j : ℂ) - (rho P π i : ℂ))
    (fun π => (rho P π j : ℂ) - (rho P π i : ℂ) + 1) (fun π π' hU => by
      rw [rho_up P hU hj, rho_up P hU hi, if_neg hne, if_pos rfl]
      ring)
  rw [← mul_assoc, a2, mul_assoc, a1, ← mul_assoc, h, mul_assoc, ← b1, ← mul_assoc, ← b2, mul_assoc]
end Formalism.FourierDecayAlt.P.Mx6.L3
