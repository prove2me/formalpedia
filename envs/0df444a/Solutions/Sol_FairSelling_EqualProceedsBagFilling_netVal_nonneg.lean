-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.netVal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:33:52.121677+00:00
-- url     : https://prove2.me/submissions/b80d5905-4c78-4e4b-8cb8-9d4fdccde547

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
theorem _root_.solution (hv : ∀ g, 0 ≤ vi g) (hp : ∀ g, 0 ≤ p g) (ht : 0 ≤ tk) (g : G) :
    0 ≤ netVal n vi p tk g := by
  unfold netVal
  split
  · exact le_min (hv g) ht
  · exact div_nonneg (hp g) (Nat.cast_nonneg _)
end FairSelling.EqualProceedsBagFilling
