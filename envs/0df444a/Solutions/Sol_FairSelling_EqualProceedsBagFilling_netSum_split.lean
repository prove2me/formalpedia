-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.netSum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:35:09.0898+00:00
-- url     : https://prove2.me/submissions/2a739a65-a06a-4d93-9d1e-b07bcee28e70

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
namespace FairSelling.EqualProceedsBagFilling
theorem _root_.solution (B : Finset G) :
    netSum n vi p tk B
      = effSum vi p tk (keepPart vi p tk B) + priceSum p (sellPart vi p tk B) / n := by
  unfold netSum effSum priceSum keepPart sellPart
  rw [← Finset.sum_filter_add_sum_filter_not B (fun g => p g ≤ min (vi g) tk)
    (fun g => netVal n vi p tk g)]
  congr 1
  · refine Finset.sum_congr rfl fun g hg => ?_
    have hg' := (Finset.mem_filter.mp hg).2
    unfold netVal effVal
    rw [if_pos hg', max_eq_right hg']
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun g hg => ?_
    have hg' := (Finset.mem_filter.mp hg).2
    unfold netVal
    rw [if_neg hg']
end FairSelling.EqualProceedsBagFilling
