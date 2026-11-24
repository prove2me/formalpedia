-- Prove2me | solution 1 for FairSelling.restricted_MMS2_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:29.066905+00:00
-- url     : https://prove2.me/submissions/db9fb3a5-870e-4739-9d19-0c526c2d04f9

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_restrictVal_nonneg
import Theorems.Thm_FairSelling_le_MMS_of_outcome
import Theorems.Thm_FairSelling_vbarSum_restrict_subset
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome

attribute [local simp] FairSelling.restrictVal_mem

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R B1 B2 : Finset G) (r : ℝ)
    (hdisj : Disjoint B1 B2) (hB1 : B1 ⊆ R) (hB2 : B2 ⊆ R)
    (h1 : r ≤ vbarSum w p B1) (h2 : r ≤ vbarSum w p B2) :
    r ≤ MMS 2 (restrictVal R w) (restrictVal R p) := by
  classical
  set o : Outcome G 2 :=
    unifiedOutcome (fun _ => restrictVal R w) (restrictVal R p) ![B1, B2] ∅ 0 with ho
  have hovalid : o.Valid (restrictVal R p) := by
    rw [ho]
    apply unifiedOutcome_valid _ _ (restrictVal_nonneg R hp)
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [hdisj.symm]
    · intro i; simp
    · intro i; simp
    · simp
  refine le_MMS_of_outcome (by norm_num) (restrictVal R w) (restrictVal R p)
    (restrictVal_nonneg R hw) (restrictVal_nonneg R hp) o hovalid r (fun j => ?_)
  have hu : util (restrictVal R w)
      (unifiedOutcome (fun _ : Fin 2 => restrictVal R w) (restrictVal R p) ![B1, B2] ∅ 0) j
      = vbarSum (restrictVal R w) (restrictVal R p) (![B1, B2] j) + (0 : Fin 2 → ℝ) j :=
    util_unifiedOutcome (fun _ : Fin 2 => restrictVal R w) (restrictVal R p) ![B1, B2] ∅ 0 j
  rw [ho, hu, Pi.zero_apply, add_zero]
  fin_cases j
  · show r ≤ vbarSum (restrictVal R w) (restrictVal R p) B1
    rw [vbarSum_restrict_subset w p R B1 hB1]; exact h1
  · show r ≤ vbarSum (restrictVal R w) (restrictVal R p) B2
    rw [vbarSum_restrict_subset w p R B2 hB2]; exact h2
end FairSelling
