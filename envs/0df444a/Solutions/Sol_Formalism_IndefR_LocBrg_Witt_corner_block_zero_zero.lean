-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.Witt.corner_block_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:17.597048+00:00
-- url     : https://prove2.me/submissions/b99e2330-d3c7-46de-8e45-705fdd9abe2e

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
theorem _root_.solution {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) : blk0 c M 0 0 = c := rfl
end Formalism.IndefR.LocBrg.Witt
