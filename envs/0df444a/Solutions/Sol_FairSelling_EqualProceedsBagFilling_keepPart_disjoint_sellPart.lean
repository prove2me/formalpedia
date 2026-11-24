-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.keepPart_disjoint_sellPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:33:31.594284+00:00
-- url     : https://prove2.me/submissions/e1286d23-451e-4dc4-ba40-39282e904e11

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
    Disjoint (keepPart vi p tk B) (sellPart vi p tk B) := by
  unfold keepPart sellPart
  exact Finset.disjoint_filter_filter_not _ _ _
end FairSelling.EqualProceedsBagFilling
