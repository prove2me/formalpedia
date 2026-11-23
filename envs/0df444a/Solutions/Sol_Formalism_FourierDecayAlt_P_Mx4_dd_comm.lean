-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.dd_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:41.93449+00:00
-- url     : https://prove2.me/submissions/4e679d90-59bb-47e4-9704-5bf0adf60e37

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_eulerComm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_mulOp_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_vz_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_eci
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_comm_eu

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
theorem _root_.solution : (mulOp (coord vzb)⁻¹ * euler vzb : Op r) * (mulOp (coord vz)⁻¹ * euler vz) =
    (mulOp (coord vz)⁻¹ * euler vz) * (mulOp (coord vzb)⁻¹ * euler vzb) := by
  have h1 : euler vzb ((coord vz)⁻¹ : Fn r) = 0 := by rw [eci, if_neg vz_ne.symm]
  have h2 : euler vz ((coord vzb)⁻¹ : Fn r) = 0 := by rw [eci, if_neg vz_ne]
  have a1 := comm_eu vzb vz _ h1
  have a2 := comm_eu vz vzb _ h2
  calc (mulOp (coord vzb)⁻¹ * euler vzb : Op r) * (mulOp (coord vz)⁻¹ * euler vz)
      = mulOp (coord vzb)⁻¹ * (euler vzb * (mulOp (coord vz)⁻¹ * euler vz)) := mul_assoc _ _ _
    _ = mulOp (coord vzb)⁻¹ * ((mulOp (coord vz)⁻¹ * euler vz) * euler vzb) := by rw [a1]
    _ = (mulOp (coord vzb)⁻¹ * mulOp (coord vz)⁻¹) * (euler vz * euler vzb) := by simp only [mul_assoc]
    _ = (mulOp (coord vz)⁻¹ * mulOp (coord vzb)⁻¹) * (euler vzb * euler vz) := by
        rw [mulOp_mul, mulOp_mul, mul_comm (coord vzb)⁻¹ (coord vz)⁻¹, eulerComm r vz vzb]
    _ = mulOp (coord vz)⁻¹ * ((mulOp (coord vzb)⁻¹ * euler vzb) * euler vz) := by simp only [mul_assoc]
    _ = mulOp (coord vz)⁻¹ * (euler vz * (mulOp (coord vzb)⁻¹ * euler vzb)) := by rw [a2]
    _ = (mulOp (coord vz)⁻¹ * euler vz) * (mulOp (coord vzb)⁻¹ * euler vzb) := (mul_assoc _ _ _).symm
end Formalism.FourierDecayAlt.P.Mx4
