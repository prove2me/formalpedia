-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.sellPart_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:33:29.075157+00:00
-- url     : https://prove2.me/submissions/d333b9cf-cbc7-4535-a6c7-d029640bb764

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
theorem _root_.solution (B : Finset G) : sellPart vi p tk B ⊆ B := Finset.filter_subset _ _
end FairSelling.EqualProceedsBagFilling
