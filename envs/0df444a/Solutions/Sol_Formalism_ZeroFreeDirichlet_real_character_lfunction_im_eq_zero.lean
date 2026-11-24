-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.real_character_lfunction_im_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:28:47.121789+00:00
-- url     : https://prove2.me/submissions/2279d735-f3d2-49f2-99ac-b5520cd5dbf7

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TrivReal
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRealPos
import Theorems.Thm_Formalism_ZeroFreeDirichlet_realCharConj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    (σ : ℝ) : (DirichletCharacter.LFunction χ σ).im = 0 := by
  have h := realCharConj q χ hχ hχ1 (σ : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.1 h.symm
end Formalism.ZeroFreeDirichlet
