-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.effVal_le_nsmul_netVal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:34:41.218055+00:00
-- url     : https://prove2.me/submissions/dd8a5b51-9005-4835-a864-7593be2e12ff

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
theorem _root_.solution (hv : ∀ g, 0 ≤ vi g) (ht : 0 ≤ tk)
    (hn : 0 < n) (g : G) : effVal vi p tk g ≤ (n : ℝ) * netVal n vi p tk g := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold effVal netVal
  split
  · rename_i h
    rw [max_eq_right h]
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [le_min (hv g) ht]
  · rename_i h
    push_neg at h
    rw [max_eq_left h.le, mul_div_cancel₀ _ (ne_of_gt hn')]
end FairSelling.EqualProceedsBagFilling
