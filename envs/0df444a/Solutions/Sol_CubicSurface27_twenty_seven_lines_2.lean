-- Prove2me | solution 2 for CubicSurface27.twenty_seven_lines
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @LG
-- created : 2026-11-22T01:53:53.9526+00:00
-- url     : https://prove2.me/submissions/5d3dd91e-4a57-4ee4-b29b-1d781270066d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_cubic_surface_27_layer
import Definitions.Def_cubic_surface_transverse
import Theorems.Thm_CubicSurface27_smooth_implies_transverse
import Theorems.Thm_CubicSurface27_transverse_implies_twenty_seven

theorem solution (F : MvPolynomial (Fin 4) ℂ)
    (hF : CubicSurface27.IsCubicForm F) (hsm : CubicSurface27.IsSmoothCubic F) :
    (CubicSurface27.linesOf F).ncard = 27 := by
  exact CubicSurface27.transverse_implies_twenty_seven F hF
    (CubicSurface27.smooth_implies_transverse F hF hsm)
