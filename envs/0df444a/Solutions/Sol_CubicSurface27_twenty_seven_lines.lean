-- Prove2me | solution 1 for CubicSurface27.twenty_seven_lines
-- status  : ACCEPTED   (prove)
-- author  : @LG
-- created : 2026-11-22T01:33:29.325103+00:00
-- url     : https://prove2.me/submissions/4f414a19-e6cc-435b-96fd-90af836710e2

import Mathlib
import Definitions.Def_cubic_surface_27_layer
import Theorems.Thm_CubicSurface27_linesOf_finite
import Theorems.Thm_CubicSurface27_linesOf_finite_to_27

theorem solution (F : MvPolynomial (Fin 4) ℂ)
    (hF : CubicSurface27.IsCubicForm F) (hsm : CubicSurface27.IsSmoothCubic F) :
    (CubicSurface27.linesOf F).ncard = 27 := by
  have hfin : (CubicSurface27.linesOf F).Finite := CubicSurface27.linesOf_finite F hF hsm
  exact CubicSurface27.linesOf_finite_to_27 F hF hsm hfin
