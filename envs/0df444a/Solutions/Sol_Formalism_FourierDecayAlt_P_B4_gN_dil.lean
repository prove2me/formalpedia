-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.gN_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:34:58.1669+00:00
-- url     : https://prove2.me/submissions/eddecb8c-5983-47f3-83ca-073afe00bafc

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_isUnit_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inv_mem_I
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ne_zero_of_mem_I
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_four_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_gN_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {τ₁ τ₂ A : ℝ} (h₁ : τ₁ ∈ Set.Icc (1 / 2 : ℝ) 2) (h₂ : τ₂ ∈ Set.Icc (1 / 2 : ℝ) 2)
    (hA : 0 ≤ A) (g : Mat k r) :
    gN g ^ A ≤ ((4 : ℝ) ^ r) ^ A * gN (aDil k r τ₁ * g * aDil k r τ₂) ^ A := by
  have h10 := ne_zero_of_mem_I h₁
  have h20 := ne_zero_of_mem_I h₂
  have hg : g = Matrix.diagonal (dg k r τ₁⁻¹) * (aDil k r τ₁ * g * aDil k r τ₂) *
      Matrix.diagonal (dg k r τ₂⁻¹) := by
    rw [← aDil_eq, ← aDil_eq, ← aDil_inv k r τ₁ h10, ← aDil_inv k r τ₂ h20]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ (aDil_isUnit_det _ h10), Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (aDil_isUnit_det _ h20), Matrix.mul_one]
  have hle : gN g ≤ (2 ^ r) ^ 2 * gN (aDil k r τ₁ * g * aDil k r τ₂) := by
    conv_lhs => rw [hg]
    exact gN_diag _ _ _ (dg_norm_le (inv_mem_I h₁)) (dg_norm_le (inv_mem_I h₂)) _
  have h0 : 0 ≤ gN g := Real.sqrt_nonneg _
  calc gN g ^ A ≤ ((2 ^ r) ^ 2 * gN (aDil k r τ₁ * g * aDil k r τ₂)) ^ A :=
      Real.rpow_le_rpow h0 hle hA
    _ = ((4 : ℝ) ^ r) ^ A * gN (aDil k r τ₁ * g * aDil k r τ₂) ^ A := by
      rw [Real.mul_rpow (by positivity)
        (show (0 : ℝ) ≤ gN (aDil k r τ₁ * g * aDil k r τ₂) from Real.sqrt_nonneg _), four_pow, sq]
end Formalism.FourierDecayAlt.P.B4
