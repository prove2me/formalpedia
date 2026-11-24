-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.effVal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:33:49.533698+00:00
-- url     : https://prove2.me/submissions/7fd5ff57-e438-4ce9-93e5-e1bc3306c1d9

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
theorem _root_.solution (hp : ∀ g, 0 ≤ p g) (g : G) : 0 ≤ effVal vi p tk g :=
  le_trans (hp g) (le_max_left _ _)
end FairSelling.EqualProceedsBagFilling
