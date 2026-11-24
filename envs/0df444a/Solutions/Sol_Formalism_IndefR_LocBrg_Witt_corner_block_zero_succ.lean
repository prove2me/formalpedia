-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.Witt.corner_block_zero_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:12.43521+00:00
-- url     : https://prove2.me/submissions/33b07f3b-10b7-48de-bfc7-7915bb7b76e9

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
theorem _root_.solution {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    blk0 c M 0 j.succ = 0 := rfl
end Formalism.IndefR.LocBrg.Witt
