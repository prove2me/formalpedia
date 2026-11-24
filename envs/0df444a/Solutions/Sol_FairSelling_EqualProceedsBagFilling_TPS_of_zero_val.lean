-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.TPS_of_zero_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:36:22.77387+00:00
-- url     : https://prove2.me/submissions/5d0c9384-b24b-46fc-9e21-ef337e9af6ef

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
theorem _root_.solution [Fintype G] (p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    TPS n (fun _ => (0 : ℝ)) p = (∑ g, p g) / n := by
  have hval : ∀ x : ℝ, truncSum n (fun _ => (0 : ℝ)) p x = (∑ g, p g) / n := by
    intro x
    unfold truncSum
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rcases le_or_gt 0 x with hx | hx
    · rw [min_eq_left hx, max_eq_left (hp g)]
    · rw [min_eq_right hx.le, max_eq_left (le_trans hx.le (hp g))]
  have hset : TPSset n (fun _ => (0 : ℝ)) p = Set.Iic ((∑ g, p g) / n) := by
    ext x
    simp [TPSset, hval x]
  rw [TPS, hset, csSup_Iic]
end FairSelling.EqualProceedsBagFilling
