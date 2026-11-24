-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.character_sum_range_add_modulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:24.37132+00:00
-- url     : https://prove2.me/submissions/b55013b5-8d4b-42c1-a0a0-d4a52c5b567f

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Theorems.Thm_Formalism_ZeroFreeDirichlet_character_sum_range_modulus_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ range (q + M), χ (n : ZMod q) = ∑ n ∈ range M, χ (n : ZMod q) := by
  rw [Finset.sum_range_add, character_sum_range_modulus_eq_zero χ hχ, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Nat.cast_add, ZMod.natCast_self, zero_add]
end Formalism.ZeroFreeDirichlet
