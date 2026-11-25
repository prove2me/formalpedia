-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.gN_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:09.022104+00:00
-- url     : https://prove2.me/submissions/bbbd530e-f9e3-4c83-89c0-75102b957f24

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OoConvOf
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNSandwich
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_uh_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_uh_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_uh_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_key
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution (hNI : NormInv) {x A y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hA : A ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {b : ℝ}
    (hb : 0 ≤ b) :
    B.gN (x⁻¹ * A * y) ^ (-b) ≤ (B.gN x * B.gN y) ^ b * B.gN A ^ (-b) := by
  have hN := hNI k r
  have hxi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hx
  have hyi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hy
  have hM : x⁻¹ * A * y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hxi.1 hA) hy
  have hm1 := (hN.2 _ hM).2
  have ha1 := (hN.2 _ hA).2
  have hx1 := (hN.2 _ hx).2
  have hy1 := (hN.2 _ hy).2
  have hyinv := (hN.2 _ hy).1
  have hAeq : x * (x⁻¹ * A * y) * y⁻¹ = A := by
    rw [show x * (x⁻¹ * A * y) * y⁻¹ = (x * x⁻¹) * A * (y * y⁻¹) by simp only [mul_assoc],
      hxi.2.1, hyi.2.1, one_mul, mul_one]
  have hle : B.gN A ≤ (B.gN x * B.gN y) * B.gN (x⁻¹ * A * y) := by
    calc B.gN A = B.gN (x * (x⁻¹ * A * y) * y⁻¹) := by rw [hAeq]
      _ ≤ B.gN (x * (x⁻¹ * A * y)) * B.gN y⁻¹ := hN.1 _ _
      _ ≤ B.gN x * B.gN (x⁻¹ * A * y) * B.gN y⁻¹ :=
          mul_le_mul_of_nonneg_right (hN.1 _ _) (by rw [hyinv]; linarith)
      _ = (B.gN x * B.gN y) * B.gN (x⁻¹ * A * y) := by rw [hyinv]; ring
  have hp : 0 < B.gN x * B.gN y := mul_pos (by linarith) (by linarith)
  have hmb : 0 < B.gN (x⁻¹ * A * y) ^ b := Real.rpow_pos_of_pos (by linarith) b
  have hab : 0 < B.gN A ^ b := Real.rpow_pos_of_pos (by linarith) b
  have key : B.gN A ^ b ≤ (B.gN x * B.gN y) ^ b * B.gN (x⁻¹ * A * y) ^ b := by
    rw [← Real.mul_rpow hp.le (by linarith)]
    exact Real.rpow_le_rpow (by linarith) hle hb
  rw [Real.rpow_neg (show (0:ℝ) ≤ B.gN (x⁻¹ * A * y) by linarith),
    Real.rpow_neg (show (0:ℝ) ≤ B.gN A by linarith)]
  calc (B.gN (x⁻¹ * A * y) ^ b)⁻¹
        = (B.gN (x⁻¹ * A * y) ^ b)⁻¹ * B.gN A ^ b * (B.gN A ^ b)⁻¹ := by
          exact (mul_inv_cancel_right₀ hab.ne' _).symm
    _ ≤ (B.gN (x⁻¹ * A * y) ^ b)⁻¹ * ((B.gN x * B.gN y) ^ b * B.gN (x⁻¹ * A * y) ^ b) *
          (B.gN A ^ b)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (inv_nonneg.2 hmb.le))
          (inv_nonneg.2 hab.le)
    _ = (B.gN x * B.gN y) ^ b * (B.gN A ^ b)⁻¹ := by
        rw [mul_comm ((B.gN x * B.gN y) ^ b) (B.gN (x⁻¹ * A * y) ^ b), inv_mul_cancel_left₀ hmb.ne']
end Formalism.FourierDecayAlt.P.S3dx4
