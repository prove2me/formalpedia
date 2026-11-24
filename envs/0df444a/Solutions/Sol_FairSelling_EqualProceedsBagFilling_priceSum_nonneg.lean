-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.priceSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:49:57.791807+00:00
-- url     : https://prove2.me/submissions/5015fd57-5858-4452-8a8e-f9922751f58c

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
theorem _root_.solution (hp : ∀ g, 0 ≤ p g) (B : Finset G) : 0 ≤ priceSum p B :=
  Finset.sum_nonneg fun g _ => hp g
end FairSelling.EqualProceedsBagFilling
