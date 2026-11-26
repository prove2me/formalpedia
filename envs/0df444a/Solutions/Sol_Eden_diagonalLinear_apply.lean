-- Prove2me | solution 1 for Eden.diagonalLinear_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:17:41.214112+00:00
-- url     : https://prove2.me/submissions/b3fbdc24-bfd3-49a7-be34-dd15bfbf9b27

import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_DerivativeDecomposition

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (d v : PhaseSpace) (i : Fin 5) :
    diagonalLinear d v i = d i * v i := rfl
end Eden
