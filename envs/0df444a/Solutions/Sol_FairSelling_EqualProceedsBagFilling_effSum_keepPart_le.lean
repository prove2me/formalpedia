-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.effSum_keepPart_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:35:14.391799+00:00
-- url     : https://prove2.me/submissions/9ff14f37-900b-42ad-b0a9-ae8591ef4344

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
    effSum vi p tk (keepPart vi p tk B) ≤ ∑ g ∈ keepPart vi p tk B, vi g := by
  refine Finset.sum_le_sum fun g hg => ?_
  have hg' := (Finset.mem_filter.mp hg).2
  unfold effVal
  exact max_le (le_trans hg' (min_le_left _ _)) (min_le_left _ _)
end FairSelling.EqualProceedsBagFilling
