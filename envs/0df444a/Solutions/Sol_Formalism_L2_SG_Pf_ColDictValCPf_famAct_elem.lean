-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.famAct_elem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:26.823352+00:00
-- url     : https://prove2.me/submissions/b57fb5c5-ec6b-4275-bb1b-c2003f5743a8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivisorClosedHolds
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_famAct_elem_X
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
theorem _root_.solution (τ : ι) (a b : Fin n) (t : ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    famAct (Function.update (fun _ => 1) τ (elem a b t)) P = (bigGen τ a b P).eval (C t) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [famAct, bigGen]
  | add p q hp hq => rw [map_add, hp, hq, map_add, Polynomial.eval_add]
  | mul_X p v hp => rw [map_mul, hp, map_mul, Polynomial.eval_mul, famAct_elem_X]
end Formalism.L2.SG.Pf.ColDictValCPf
