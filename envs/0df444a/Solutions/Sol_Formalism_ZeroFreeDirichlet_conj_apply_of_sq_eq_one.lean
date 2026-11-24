-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.conj_apply_of_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:44:05.592142+00:00
-- url     : https://prove2.me/submissions/0baae1fe-3b95-4861-81b5-ec61fcbd35f0

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TrivReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (a : ZMod q) :
    starRingEnd ℂ (χ a) = χ a := by
  by_cases ha : IsUnit a
  · have h2 : χ a * χ a = 1 := by
      rw [← sq, ← MulChar.pow_apply' χ two_ne_zero, hχ, MulChar.one_apply ha]
    rcases mul_self_eq_one_iff.1 h2 with h | h
    · rw [h, map_one]
    · rw [h, map_neg, map_one]
  · rw [MulChar.map_nonunit χ ha, map_zero]
end Formalism.ZeroFreeDirichlet
