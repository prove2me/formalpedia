-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.curv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:49.813364+00:00
-- url     : https://prove2.me/submissions/08977e78-b4aa-424a-96a5-d3c344660521

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_der_fn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_smul_fnP
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_dz_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_key_zb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_euler_zeta_gamma_inv_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (a TT : ℝ) :
    (-dzbP + (a : ℂ) • (zP * ggiP TT)) * (dzP + (a : ℂ) • (zbP * ggiP TT)) -
      (dzP + (a : ℂ) • (zbP * ggiP TT)) * (-dzbP + (a : ℂ) • (zP * ggiP TT)) =
      (algebraMap ℂ (Pr r) ((2 * a * TT : ℝ) : ℂ)) * ggiP TT * ggiP TT := by
  have e1 : (dzbP : Pr r) * fnP ((a : ℂ) • (coord vzb * (gg TT)⁻¹)) ((a : ℂ) • (coord vz * (gg TT)⁻¹)) =
      fnP ((a : ℂ) • (coord vzb * (gg TT)⁻¹)) ((a : ℂ) • (coord vz * (gg TT)⁻¹)) * dzbP +
      fnP ((coord vzb)⁻¹ * euler vzb ((a : ℂ) • (coord vzb * (gg TT)⁻¹)))
        ((coord vz)⁻¹ * euler vz ((a : ℂ) • (coord vz * (gg TT)⁻¹))) := by
    rw [dzbP, der_fn]
  have e2 : (dzP : Pr r) * fnP ((a : ℂ) • (coord vz * (gg TT)⁻¹)) ((a : ℂ) • (coord vzb * (gg TT)⁻¹)) =
      fnP ((a : ℂ) • (coord vz * (gg TT)⁻¹)) ((a : ℂ) • (coord vzb * (gg TT)⁻¹)) * dzP +
      fnP ((coord vz)⁻¹ * euler vz ((a : ℂ) • (coord vz * (gg TT)⁻¹)))
        ((coord vzb)⁻¹ * euler vzb ((a : ℂ) • (coord vzb * (gg TT)⁻¹))) := by
    rw [dzP, der_fn]
  rw [mul_assoc, ← Algebra.smul_def, zP, zbP, ggiP, multiplierPair_mul, multiplierPair_mul, multiplierPair_mul, smul_fnP, smul_fnP, smul_fnP]
  simp only [map_smul, mul_smul_comm, euler_zeta_gamma_inv_identity, key_zb] at e1 e2
  have e3 := multiplierPair_comm ((a : ℂ) • (coord vz * (gg TT)⁻¹ : Fn r)) ((a : ℂ) • (coord vzb * (gg TT)⁻¹))
    ((a : ℂ) • (coord vzb * (gg TT)⁻¹)) ((a : ℂ) • (coord vz * (gg TT)⁻¹))
  have e4 : fnP (((2 * a * TT : ℝ) : ℂ) • ((gg TT)⁻¹ * (gg TT)⁻¹ : Fn r)) (((2 * a * TT : ℝ) : ℂ) • ((gg TT)⁻¹ * (gg TT)⁻¹)) =
      -fnP ((a : ℂ) • -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹)))
        ((a : ℂ) • -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹))) -
      fnP ((a : ℂ) • -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹)))
        ((a : ℂ) • -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹))) := by
    rw [multiplierPair_neg, sub_eq_add_neg, multiplierPair_neg, multiplierPair_add]
    have : (((2 * a * TT : ℝ) : ℂ) • ((gg TT)⁻¹ * (gg TT)⁻¹ : Fn r)) =
        -((a : ℂ) • -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹))) +
        -((a : ℂ) • -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹))) := by
      simp only [Algebra.smul_def]
      push_cast
      simp only [map_ofNat]
      ring
    rw [← this]
  rw [e4]
  simp only [add_mul, mul_add, neg_mul, mul_neg]
  rw [e1, e2, e3, dz_comm]
  abel
end Formalism.FourierDecayAlt.P.Mx4
