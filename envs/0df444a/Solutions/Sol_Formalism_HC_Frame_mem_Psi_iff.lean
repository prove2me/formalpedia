-- Prove2me | solution 1 for Formalism.HC.Frame.mem_Psi_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:35:56.126198+00:00
-- url     : https://prove2.me/submissions/d2eff71c-0630-40ae-8c25-3bdf880849c0

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.Frame
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution {φ : Frame} (g : φ.GG) : g ∈ φ.Psi ↔ g.1.2 = 1 := by
  rw [Frame.Psi, MonoidHom.mem_ker]
  rfl
end Formalism.HC.Frame
