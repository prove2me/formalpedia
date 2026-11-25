-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.DensPf.cayley_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:40:30.572894+00:00
-- url     : https://prove2.me/submissions/6e6e130b-3403-4644-8170-858f6b6020b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_CayleyIsometry
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Matrix MvPolynomial
open scoped ComplexOrder
open Formalism.L2.SG.Pf.ColDictValCPf.DensPf
variable {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf.DensPf
theorem _root_.solution (G A : Matrix (Fin n) (Fin n) ℂ) (hskew : Aᴴ * G = -(G * A))
    (hB : IsUnit (1 + A).det) :
    ((1 - A) * (1 + A)⁻¹)ᴴ * G * ((1 - A) * (1 + A)⁻¹) = G := by
  have h1 : (1 - Aᴴ) * G = G * (1 + A) := by
    rw [sub_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hskew, sub_neg_eq_add]
  have h2 : G * (1 - A) = (1 + Aᴴ) * G := by
    rw [mul_sub, add_mul, Matrix.one_mul, Matrix.mul_one, hskew, sub_eq_add_neg]
  have h3 : (1 + A) * (1 - A) = (1 - A) * (1 + A) := by noncomm_ring
  have hBH : IsUnit (1 + Aᴴ).det := by
    rw [show (1 : Matrix (Fin n) (Fin n) ℂ) + Aᴴ = (1 + A)ᴴ by
      rw [conjTranspose_add, conjTranspose_one], det_conjTranspose]
    exact hB.star
  rw [conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_sub, conjTranspose_add,
    conjTranspose_one]
  calc (1 + Aᴴ)⁻¹ * (1 - Aᴴ) * G * ((1 - A) * (1 + A)⁻¹)
      = (1 + Aᴴ)⁻¹ * ((1 - Aᴴ) * G) * (1 - A) * (1 + A)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (1 + Aᴴ)⁻¹ * (G * (1 - A)) * ((1 + A) * (1 + A)⁻¹) := by
        rw [h1]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (1 + A), h3]
        simp only [Matrix.mul_assoc]
    _ = (1 + Aᴴ)⁻¹ * ((1 + Aᴴ) * G) := by rw [h2, mul_nonsing_inv _ hB, Matrix.mul_one]
    _ = G := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hBH, Matrix.one_mul]
end Formalism.L2.SG.Pf.ColDictValCPf.DensPf
