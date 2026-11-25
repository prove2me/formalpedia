-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.map_genAct_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:44:06.711128+00:00
-- url     : https://prove2.me/submissions/4eedfd24-d0bd-4778-970d-c1b4beda9437

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivisorClosedHolds
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
theorem _root_.solution (τ : ι) (g : Matrix (Fin n) (Fin n) ℂ) (v : ι × Fin n × Fin n) :
    map (eval fun x => g x.1 x.2) (genAct τ (X v)) = famAct (Function.update (fun _ => 1) τ g) (X v) := by
  obtain ⟨τ', r, s⟩ := v
  by_cases hv : τ' = τ
  · subst hv
    simp only [genAct, famAct, aeval_X, if_true, Function.update_self, map_sum, map_mul, map_C, map_X,
      eval_X]
  · simp only [genAct, famAct, aeval_X, if_neg hv, Function.update_of_ne hv, map_X]
    rw [Finset.sum_eq_single r (fun c _ hc => by rw [Matrix.one_apply_ne (Ne.symm hc), map_zero, zero_mul])
      (by simp), Matrix.one_apply_eq, map_one, one_mul]
end Formalism.L2.SG.Pf.ColDictValCPf
