-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.netSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:55:29.041868+00:00
-- url     : https://prove2.me/submissions/0ea4e81e-7162-4309-a305-455c76af56de

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_netVal_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
namespace FairSelling.EqualProceedsBagFilling
theorem _root_.solution (hv : ∀ g, 0 ≤ vi g) (hp : ∀ g, 0 ≤ p g) (ht : 0 ≤ tk) (B : Finset G) :
    0 ≤ netSum n vi p tk B :=
  Finset.sum_nonneg fun g _ => netVal_nonneg hv hp ht g
end FairSelling.EqualProceedsBagFilling
