-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.massLeft_add_massRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:33:51.316653+00:00
-- url     : https://prove2.me/submissions/7d8262b9-683e-4ad6-b466-5b8504a638a8

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution (a p h : ℝ) (x y : ℕ) :
    massLeft a p h x y + massRight a p h x y =
      parentMass h x y := by
  unfold massLeft massRight
  ring
end FD1D.V5.LocalPolicy
