-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.effVal_le_of_price_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:34:32.685801+00:00
-- url     : https://prove2.me/submissions/81d86883-5326-4bd8-b296-759e08c73046

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
theorem _root_.solution (h : p g ≤ tk) : effVal vi p tk g ≤ tk :=
  max_le h (min_le_right _ _)
end FairSelling.EqualProceedsBagFilling
