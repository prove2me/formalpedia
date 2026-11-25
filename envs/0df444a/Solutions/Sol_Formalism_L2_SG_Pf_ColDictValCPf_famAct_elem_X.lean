-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.famAct_elem_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:20.954881+00:00
-- url     : https://prove2.me/submissions/ec413775-00e8-49b1-a4f4-ae1c0ef9b076

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
theorem _root_.solution (τ : ι) (a b : Fin n) (t : ℂ) (v : ι × Fin n × Fin n) :
    famAct (Function.update (fun _ => 1) τ (elem a b t)) (X v) = (bigGen τ a b (X v)).eval (C t) := by
  obtain ⟨τ', r, s⟩ := v
  by_cases hv : τ' = τ
  · subst hv
    simp only [famAct, aeval_X, Function.update_self, elem_apply, map_add, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single r (fun c _ hc => by rw [if_neg (Ne.symm hc), map_zero, zero_mul]) (by simp),
      if_pos rfl, map_one, one_mul]
    simp only [bigGen, aeval_X, true_and, Polynomial.eval_add, Polynomial.eval_C]
    by_cases hb : r = b
    · subst hb
      rw [Finset.sum_eq_single a (fun c _ hc => by rw [if_neg (by tauto), map_zero, zero_mul]) (by simp),
        if_pos ⟨rfl, rfl⟩, if_pos rfl, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    · rw [Finset.sum_eq_zero (fun c _ => by rw [if_neg (by tauto), map_zero, zero_mul]), if_neg hb,
        Polynomial.eval_zero]
  · simp only [famAct, bigGen, aeval_X, Function.update_of_ne hv, hv, false_and, if_false, add_zero,
      Polynomial.eval_C]
    rw [Finset.sum_eq_single r (fun c _ hc => by rw [Matrix.one_apply_ne (Ne.symm hc), map_zero, zero_mul])
      (by simp), Matrix.one_apply_eq, map_one, one_mul]
end Formalism.L2.SG.Pf.ColDictValCPf
