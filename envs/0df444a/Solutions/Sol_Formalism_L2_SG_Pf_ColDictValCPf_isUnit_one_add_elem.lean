-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.isUnit_one_add_elem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:23.861015+00:00
-- url     : https://prove2.me/submissions/1865b9b0-c240-4931-820b-f68fd05cd398

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivisorClosedHolds
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_elem_apply
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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (a b : Fin n) (m : ℕ) : IsUnit (1 + elem a b (m : ℂ)).det := by
  have h : 1 + elem a b (m : ℂ) =
      (2 : ℂ) • (1 + replicateCol (Fin 1) (Pi.single b ((m : ℂ) / 2)) * replicateRow (Fin 1) (Pi.single a (1 : ℂ))) := by
    ext r c
    rw [Matrix.add_apply, elem_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
    simp only [Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Finset.univ_unique, Finset.sum_singleton,
      Pi.single_apply, smul_eq_mul]
    split_ifs <;> (try subst_vars) <;> (try simp_all) <;> ring
  have hR := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (Pi.single b ((m : ℂ) / 2))
    (Pi.single a (1 : ℂ))
  rw [h, det_smul]
  erw [hR]
  rw [isUnit_iff_ne_zero]
  refine mul_ne_zero (pow_ne_zero _ two_ne_zero) ?_
  simp only [dotProduct, Pi.single_apply]
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]
  intro h0
  have := congrArg Complex.re h0
  by_cases hab : a = b
  · subst hab
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · simp [hab] at this
end Formalism.L2.SG.Pf.ColDictValCPf
