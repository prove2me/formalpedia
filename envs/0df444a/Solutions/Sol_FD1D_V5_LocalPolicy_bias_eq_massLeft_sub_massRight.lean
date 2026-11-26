-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.bias_eq_massLeft_sub_massRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:26.640664+00:00
-- url     : https://prove2.me/submissions/4cd137db-23d4-4639-8475-348ac19cc803

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution (a p h : ℝ) (x y : ℕ) :
    bias a p h x y =
      massLeft a p h x y - massRight a p h x y := by
  unfold massLeft massRight
  ring
end FD1D.V5.LocalPolicy
