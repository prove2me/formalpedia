-- Prove2me | solution 2 for Formalism.ZeroFreeDirichlet.norm_character_sum_range_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:12:18.385701+00:00
-- url     : https://prove2.me/submissions/69f6d47e-8e3e-4b63-9b22-38d82f15046b

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Theorems.Thm_Formalism_ZeroFreeDirichlet_character_sum_range_add_modulus

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
    ‖∑ n ∈ range M, χ (n : ZMod q)‖ ≤ q := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    by_cases hM : M < q
    · calc ‖∑ n ∈ range M, χ (n : ZMod q)‖ ≤ ∑ n ∈ range M, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ range M, (1 : ℝ) := Finset.sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ _
        _ = M := by simp
        _ ≤ q := by exact_mod_cast hM.le
    · obtain ⟨M', rfl⟩ : ∃ M', M = q + M' := ⟨M - q, by omega⟩
      rw [character_sum_range_add_modulus χ hχ M']
      exact ih M' (by have := NeZero.pos q; omega)
end Formalism.ZeroFreeDirichlet
