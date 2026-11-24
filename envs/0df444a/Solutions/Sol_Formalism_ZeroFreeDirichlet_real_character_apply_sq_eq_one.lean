-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.real_character_apply_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:45:06.477957+00:00
-- url     : https://prove2.me/submissions/0b71ca0c-3ccc-464c-8128-b484a7b8e29b

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelBoundSameCharacter
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelProductCharacterInequality

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
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n.Coprime q) : χ (n : ZMod q) * χ (n : ZMod q) = 1 := by
  have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hn
  have h := congrArg (fun f : DirichletCharacter ℂ q => f (n : ZMod q)) hsq
  simp only [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply hu] at h
  rw [← sq]
  exact h
end Formalism.ZeroFreeDirichlet
