-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L3.Lam2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:11.44583+00:00
-- url     : https://prove2.me/submissions/067145d7-3ce6-4036-8509-c5de104003c6

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_rho_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_xC_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_xEx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_good0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_good1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_good0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_good1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_comm_sum

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
theorem _root_.solution (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • ((kap P fun π => (xC P π (u + 1))⁻¹) * abelian₂ P v -
      abelian₂ P v * (kap P fun π => (xC P π (u + 1))⁻¹)) =
      (kap P fun π => (xC P π (u + 1))⁻¹) * (abelian₂ P u - abelian₂ P v) := by
  have h := comm_sum P (fun π => (xC P π (u + 1))⁻¹)
    (fun j π => (u + (rho P π j : ℂ) + 1) * (u + (rho P π j : ℂ))⁻¹ * (xC P π (u + 1))⁻¹) 1 u v
    (fun j hj π π' hU => by
      have h0 := good0 P hu π' hj
      have h1 := good1 P hu π' hj
      rw [xC_split P π' (u + 1) hj, xC_split P π (u + 1) hj,
        xEx_up P hU {j} (Finset.mem_singleton_self j), mul_inv, mul_inv]
      rw [rho_up P hU hj, if_pos rfl] at h0 h1 ⊢
      generalize (xEx P {j} π (u + 1))⁻¹ = Ei
      have h2 : u + 1 + ((rho P π j : ℂ) + 1) ≠ 0 := by intro h; apply h1; rw [← h]; ring
      have h3 : u + 1 + (rho P π j : ℂ) ≠ 0 := by intro h; apply h0; rw [← h]; ring
      field_simp
      ring)
    (fun j hj π => by
      have h1 := good0 P hu π hj
      have h2 := good0 P hv π hj
      simp only [rr]
      generalize (xC P π (u + 1))⁻¹ = Xi
      field_simp
      ring)
  rw [one_smul] at h
  exact h
end Formalism.FourierDecayAlt.P.Mx6.L3
