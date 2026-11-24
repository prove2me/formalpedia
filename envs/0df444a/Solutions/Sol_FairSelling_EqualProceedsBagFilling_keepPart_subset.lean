-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.keepPart_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:33:03.117902+00:00
-- url     : https://prove2.me/submissions/a7f3aed1-86e6-4e53-b18c-5a3cf972e2c9

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
theorem _root_.solution (B : Finset G) : keepPart vi p tk B ⊆ B := Finset.filter_subset _ _
end FairSelling.EqualProceedsBagFilling
