-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.remarkPrice_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:26.156463+00:00
-- url     : https://prove2.me/submissions/e80b948a-9537-440d-94fd-89479d8cc0ce

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
theorem _root_.solution : ∀ g, 0 ≤ remarkPrice g := by
  intro g; unfold remarkPrice; split <;> norm_num
end FairSelling.EqualProceedsBagFilling
