-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.DensPf.skew_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:59:31.645837+00:00
-- url     : https://prove2.me/submissions/a86cece2-b3bf-457b-be24-6f0e18794eaf

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
theorem _root_.solution (G P : Matrix (Fin n) (Fin n) ℂ) (hH : Gᴴ = G) (hG : IsUnit G.det) :
    (P - G⁻¹ * Pᴴ * G)ᴴ * G = -(G * (P - G⁻¹ * Pᴴ * G)) := by
  have hi : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hH]
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hi, hH]
  simp only [sub_mul, mul_sub, Matrix.mul_assoc, nonsing_inv_mul _ hG, Matrix.mul_one]
  rw [← Matrix.mul_assoc G G⁻¹, mul_nonsing_inv _ hG, Matrix.one_mul]
  abel
end Formalism.L2.SG.Pf.ColDictValCPf.DensPf
