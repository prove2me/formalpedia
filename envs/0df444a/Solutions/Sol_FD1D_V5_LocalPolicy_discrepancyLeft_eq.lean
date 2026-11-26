-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.discrepancyLeft_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:29.497697+00:00
-- url     : https://prove2.me/submissions/77b3987b-e5f8-4b3f-b74e-641194e87735

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution (a p h : ℝ) (x y : ℕ) :
    discrepancyLeft a p h x y =
      (discrepancy a p h x y - bias a p h x y / a) / 2 := by
  unfold discrepancyLeft discrepancy massLeft
  ring
end FD1D.V5.LocalPolicy
