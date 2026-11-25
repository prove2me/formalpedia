-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.tgood_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:05.179524+00:00
-- url     : https://prove2.me/submissions/63be4ad1-91d5-4814-94bc-e3fa71cd638a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_mul
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open MvPolynomial
variable {σ : Type*}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution {α : Type*} (w : σ → ℕ) (c : ℕ) (s : Finset α) (d : α → ℕ)
    (F : α → Polynomial (MvPolynomial σ ℂ)) (h : ∀ i ∈ s, TGood w c (d i) (F i)) :
    TGood w c (∑ i ∈ s, d i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact tgood_one w c
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact tgood_mul w c (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end Formalism.L2.SG.Pf.ColDictValCPf
