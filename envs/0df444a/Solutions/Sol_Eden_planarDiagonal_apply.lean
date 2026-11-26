-- Prove2me | solution 1 for Eden.planarDiagonal_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:22:54.570891+00:00
-- url     : https://prove2.me/submissions/0e3efdff-4823-436f-a611-82281311983e

import Definitions.Def_Eden_PlanarVectorField
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_PlanarDerivative

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (d v : PlanarSpace) (i : Fin 2) :
    planarDiagonal d v i = d i * v i := rfl
end Eden
