-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.eOf_char_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:24:37.381956+00:00
-- url     : https://prove2.me/submissions/99965e0f-7d68-4453-bc1f-d1b26859f594

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_eOf_exc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) (h : eOf M = some (χ₁, β₁))
    (b : ZMod M) (hb : IsUnit b) : χ₁ b = 1 ∨ χ₁ b = -1 := by
  have hex := eOf_exc M (χ₁, β₁) h
  have h2 : (χ₁ ^ 2) b = 1 := by
    rw [hex.1]
    exact MulChar.one_apply hb
  rw [MulChar.pow_apply' χ₁ (by norm_num)] at h2
  exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
end Formalism.HermitianLattices.Ext.PrimesInProgressions
