-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.elem_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:30:31.566018+00:00
-- url     : https://prove2.me/submissions/20d75296-449e-451e-821f-213e1b98f697

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
theorem _root_.solution (a b : Fin n) (t : ℂ) (r c : Fin n) :
    elem a b t r c = (if r = c then 1 else 0) + (if r = b ∧ c = a then t else 0) := by
  simp only [elem, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, replicateCol_apply,
    replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, Pi.single_apply]
  by_cases h1 : r = b <;> by_cases h2 : c = a <;> simp [h1, h2]
end Formalism.L2.SG.Pf.ColDictValCPf
