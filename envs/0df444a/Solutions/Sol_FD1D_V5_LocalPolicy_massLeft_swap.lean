-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.massLeft_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:20:33.950406+00:00
-- url     : https://prove2.me/submissions/5aea65aa-d47d-4dda-b10a-6d77eb9d923c

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy
import Theorems.Thm_FD1D_V5_LocalPolicy_parentMass_swap
import Theorems.Thm_FD1D_V5_LocalPolicy_bias_swap

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution (a p h : ℝ) (x y : ℕ) :
    massLeft a p h y x = massRight a p h x y := by
  unfold massLeft massRight
  rw [parentMass_swap, bias_swap]
  ring
end FD1D.V5.LocalPolicy
