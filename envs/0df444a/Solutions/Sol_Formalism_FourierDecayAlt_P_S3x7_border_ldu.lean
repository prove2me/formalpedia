-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.border_ldu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:34.938862+00:00
-- url     : https://prove2.me/submissions/6e89b4bf-5f03-4caf-9df1-7a77bafd8d76

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cl
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_lc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_ll

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x7
theorem _root_.solution {r : ℕ} (B L₀ D₀ U₀ : Matrix (Fin r) (Fin r) A) (v u : Fin r → A) (c : A)
    (uB : IsUnit B.det) (e₀ : B = L₀ * D₀ * U₀) :
    border B v u c = border L₀ 0 (u ᵥ* (B⁻¹ * L₀)) 1 *
      border D₀ 0 0 (c - ((u ᵥ* (B⁻¹ * L₀)) ᵥ* D₀) ⬝ᵥ ((U₀ * B⁻¹) *ᵥ v)) *
      border U₀ ((U₀ * B⁻¹) *ᵥ v) 0 1 := by
  have h1 : (L₀ * D₀) *ᵥ ((U₀ * B⁻¹) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← e₀, Matrix.mul_nonsing_inv _ uB,
      Matrix.one_mulVec]
  have h2 : ((u ᵥ* (B⁻¹ * L₀)) ᵥ* D₀) ᵥ* U₀ = u := by
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc,
      ← Matrix.mul_assoc L₀, ← e₀, Matrix.nonsing_inv_mul _ uB, Matrix.vecMul_one]
  rw [border_mul, border_mul]
  simp only [Matrix.zero_vecMulVec, add_zero, Matrix.mulVec_zero, smul_zero, dotProduct_zero, one_mul,
    zero_add, mul_one, h1, h2, ← e₀, add_sub_cancel]
end Formalism.FourierDecayAlt.P.S3x7
