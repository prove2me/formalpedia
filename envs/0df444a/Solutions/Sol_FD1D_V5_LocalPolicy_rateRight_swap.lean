-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.rateRight_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:51.186551+00:00
-- url     : https://prove2.me/submissions/d19138d5-617a-4abb-aa46-6f924d931982

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy
import Theorems.Thm_FD1D_V5_LocalPolicy_rateLeft_swap

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution (a p h : ℝ) (x y : ℕ) :
    rateRight a p h y x = rateLeft a p h x y := by
  rw [← rateLeft_swap a p h y x]
end FD1D.V5.LocalPolicy
