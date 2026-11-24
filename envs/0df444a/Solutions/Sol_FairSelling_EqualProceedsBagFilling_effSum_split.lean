-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.effSum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:34:51.475705+00:00
-- url     : https://prove2.me/submissions/0c16f2a1-3a80-4330-aa87-a67c2b2f72d5

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
    effSum vi p tk B = effSum vi p tk (keepPart vi p tk B) + priceSum p (sellPart vi p tk B) := by
  unfold effSum priceSum keepPart sellPart
  rw [← Finset.sum_filter_add_sum_filter_not B (fun g => p g ≤ min (vi g) tk)
    (fun g => effVal vi p tk g)]
  congr 1
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' := (Finset.mem_filter.mp hg).2
  unfold effVal
  exact max_eq_left (by push_neg at hg'; exact hg'.le)
end FairSelling.EqualProceedsBagFilling
