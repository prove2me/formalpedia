-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.mean_square_of_pnt_progressions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:57:44.259226+00:00
-- url     : https://prove2.me/submissions/8adb3ebf-de19-40af-8982-c723eb4ab44f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMain
import Definitions.Def_Formalism_GL3MeanSquares_PrimePairOfBoxAndWeakMeanSquareHypotheses
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqFinal
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_meanSquareHypW_of_pnt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (hP : PNTAPRelW) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, 0 < C ∧ Formalism.HermitianLattices.WeakMeanSquareEstimates.MeanSquareHypW ε C x₀ := by
  intro ε hε hε1
  obtain ⟨C, x₀, h⟩ := meanSquareHypW_of_pnt hP ε hε hε1
  refine ⟨max C 1, max x₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro x X m₀ a₀ κ hx h8 hp ha h4 h1 h2 h3 hk hm
  obtain ⟨ha', hb⟩ := h x X m₀ a₀ κ (le_trans (le_max_left _ _) hx) h8 hp ha h4 h1 h2 h3 hk hm
  refine ⟨ha', le_trans hb ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hc : (0 : ℝ) ≤ ((Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset m₀ a₀ X).card : ℝ) := Nat.cast_nonneg _
  have hxl : 0 ≤ x * Real.log x * ((Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset m₀ a₀ X).card : ℝ) :=
    mul_nonneg (mul_nonneg (by linarith) hl) hc
  have := mul_le_mul_of_nonneg_right (le_max_left C 1) hxl
  simpa [mul_assoc] using this
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
