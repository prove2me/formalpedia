-- Prove2me | solution 1 for FockRaiseLowInner.wt_single_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:40.216331+00:00
-- url     : https://prove2.me/submissions/c2782a99-204c-478b-8024-c9e289a20894

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockRaiseLowInner
open MvPolynomial FockH1Action
variable {σ : Type*}
namespace FockRaiseLowInner
theorem _root_.solution (l : σ) (α : σ →₀ ℕ) :
    wt (Finsupp.single l 1 + α) = ((α l : ℂ) + 1) * wt α := by
  classical
  have hl : l ∈ insert l α.support := Finset.mem_insert_self l α.support
  have hsub1 : (Finsupp.single l 1 + α).support ⊆ insert l α.support := by
    intro i hi
    rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hi
    by_cases h : i = l
    · rw [h]
      exact hl
    · rw [Finsupp.single_apply, if_neg (Ne.symm h), zero_add] at hi
      exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hi)
  have hsub2 : α.support ⊆ insert l α.support := fun i hi => Finset.mem_insert_of_mem hi
  unfold wt
  rw [Finsupp.prod_of_support_subset _ hsub1 _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset _ hsub2 _ (fun _ _ => by simp)]
  have e1 := Finset.mul_prod_erase (insert l α.support)
    (fun i => (((Finsupp.single l 1 + α : σ →₀ ℕ) i).factorial : ℂ)) hl
  have e2 := Finset.mul_prod_erase (insert l α.support) (fun i => ((α i).factorial : ℂ)) hl
  try beta_reduce at e1 e2
  rw [← e1, ← e2]
  have hrest : ∏ x ∈ (insert l α.support).erase l, (((Finsupp.single l 1 + α : σ →₀ ℕ) x).factorial : ℂ) =
      ∏ x ∈ (insert l α.support).erase l, ((α x).factorial : ℂ) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hil : i ≠ l := Finset.ne_of_mem_erase hi
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hil), zero_add]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same,
    show (1 + α l).factorial = (α l + 1) * (α l).factorial from by
      rw [add_comm]
      exact Nat.factorial_succ _]
  push_cast
  ring
end FockRaiseLowInner
