-- Prove2me | solution 1 for Formalism.HC.Frame.val_ofNat_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:20.789318+00:00
-- url     : https://prove2.me/submissions/2d5ca14c-efec-47a2-9840-dba2aed36453

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
theorem _root_.solution {u : ℕ} (hu : u < φ.ord) : (φ.ofNat u).val = u := by
  rw [φ.val_ofNat u, Nat.mod_eq_of_lt hu]
end Formalism.HC.Frame
