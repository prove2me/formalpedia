-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.effVal_le_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:34:22.504621+00:00
-- url     : https://prove2.me/submissions/adfb9ea4-578b-4850-8493-093ac7d02624

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
theorem _root_.solution (hp : ∀ g, 0 ≤ p g) (ht : 0 ≤ tk) (g : G) :
    effVal vi p tk g ≤ p g + tk := by
  unfold effVal
  refine max_le (by linarith) (le_trans (min_le_right _ _) (by linarith [hp g]))
end FairSelling.EqualProceedsBagFilling
