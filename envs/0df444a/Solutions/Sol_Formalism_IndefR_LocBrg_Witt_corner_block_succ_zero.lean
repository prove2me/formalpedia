-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.Witt.corner_block_succ_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:12.488352+00:00
-- url     : https://prove2.me/submissions/3fdcbc17-8a7f-4e1f-aa64-54e4c712e259

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg Formalism.IndefR.LocBrg.Witt
variable {R : Type} [CommRing R]
namespace Formalism.IndefR.LocBrg.Witt
theorem _root_.solution {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    blk0 c M i.succ 0 = 0 := rfl
end Formalism.IndefR.LocBrg.Witt
