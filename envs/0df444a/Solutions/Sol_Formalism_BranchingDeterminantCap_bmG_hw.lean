-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_hw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:26.857001+00:00
-- url     : https://prove2.me/submissions/a29a401e-c154-44f2-8fa9-6ea94a13d2dc

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_nuNext_of_succ
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_nuNext_last
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_shift
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_D_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (R : Type*) [CommRing R] {n : ℕ} (lam sg : Fin n → ℕ) (hIL : bmIL lam sg) :
    ∏ i : Fin n, (bmG_D R n (i.val + 1) ^ (sg i - nuNext lam i) * bmG_D R n i.val ^ (lam i - sg i)) =
      hw R le_rfl sg := by
  rw [Finset.prod_mul_distrib, bmG_shift n (bmG_D R n) (bmG_D_zero R n) (fun i => lam i - sg i),
    ← Finset.prod_mul_distrib]
  unfold hw
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add]
  have h1 : bmG_D R n (i.val + 1) = lpMinor R (i.val + 1) (by omega) (by omega) := by
    unfold bmG_D
    rw [dif_pos (by omega)]
  rw [h1]
  congr 1
  by_cases hi : i.val + 1 < n
  · rw [bmG_nuNext_of_succ lam i ⟨i.val + 1, hi⟩ rfl, bmG_nuNext_of_succ sg i ⟨i.val + 1, hi⟩ rfl,
      bmG_nuNext_of_succ (fun i => lam i - sg i) i ⟨i.val + 1, hi⟩ rfl]
    have h2 := (hIL i).2
    rw [bmG_nuNext_of_succ lam i ⟨i.val + 1, hi⟩ rfl] at h2
    have h3 := (hIL ⟨i.val + 1, hi⟩).1
    omega
  · rw [bmG_nuNext_last lam i hi, bmG_nuNext_last sg i hi, bmG_nuNext_last _ i hi]
    rfl
end Formalism.BranchingDeterminantCap
