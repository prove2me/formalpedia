-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.ThickExists.cast_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:07.907839+00:00
-- url     : https://prove2.me/submissions/9b0cde64-169b-490f-a1df-6dd2a216838a

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.ThickExists
namespace Formalism.FrobeniusOrbits.ThickExists
theorem _root_.solution (B : ℕ) {S : ℕ} (v : Fin S → ℕ) :
    ((Behrend.map B v : ℕ) : ℤ) = ∑ m, (v m : ℤ) * (B : ℤ) ^ (m : ℕ) := by
  rw [Behrend.map_apply, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Nat.cast_mul, Nat.cast_pow]
end Formalism.FrobeniusOrbits.ThickExists
