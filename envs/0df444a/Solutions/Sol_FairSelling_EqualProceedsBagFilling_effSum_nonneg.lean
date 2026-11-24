-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.effSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:35:12.923033+00:00
-- url     : https://prove2.me/submissions/c05b37d6-4b75-4e9b-9cfe-32e1a21975ca

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_effVal_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
namespace FairSelling.EqualProceedsBagFilling
theorem _root_.solution (hp : ∀ g, 0 ≤ p g) (B : Finset G) : 0 ≤ effSum vi p tk B :=
  Finset.sum_nonneg fun g _ => effVal_nonneg hp g
end FairSelling.EqualProceedsBagFilling
