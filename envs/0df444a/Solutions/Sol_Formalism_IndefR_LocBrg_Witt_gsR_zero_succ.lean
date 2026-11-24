-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.Witt.gsR_zero_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:19.049804+00:00
-- url     : https://prove2.me/submissions/dbfe0f14-072c-4948-a228-29254d230485

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
variable [IsLocalRing R] (σ : R →+* R)
namespace Formalism.IndefR.LocBrg.Witt
theorem _root_.solution {n : ℕ} (u : R) (m : Fin n → R) (j : Fin n) : gsR u m 0 j.succ = -(u * m j) := rfl
end Formalism.IndefR.LocBrg.Witt
