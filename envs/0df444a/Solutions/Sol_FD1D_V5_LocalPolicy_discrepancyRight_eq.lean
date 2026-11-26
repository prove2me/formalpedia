-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.discrepancyRight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:43.322159+00:00
-- url     : https://prove2.me/submissions/c5a7a4cd-dccf-48a2-9fb3-b6dc0477b419

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution (a p h : ℝ) (x y : ℕ) :
    discrepancyRight a p h x y =
      (discrepancy a p h x y + bias a p h x y / a) / 2 := by
  unfold discrepancyRight discrepancy massRight
  ring
end FD1D.V5.LocalPolicy
