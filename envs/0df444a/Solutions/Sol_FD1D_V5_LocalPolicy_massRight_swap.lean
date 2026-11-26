-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.massRight_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:26.01307+00:00
-- url     : https://prove2.me/submissions/c82e0462-40c9-447c-b111-2b089d6c9893

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy
import Theorems.Thm_FD1D_V5_LocalPolicy_parentMass_swap
import Theorems.Thm_FD1D_V5_LocalPolicy_bias_swap

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution (a p h : ℝ) (x y : ℕ) :
    massRight a p h y x = massLeft a p h x y := by
  unfold massLeft massRight
  rw [parentMass_swap, bias_swap]
  ring
end FD1D.V5.LocalPolicy
