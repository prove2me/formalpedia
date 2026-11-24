-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.consecutive_ratio_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:44.399304+00:00
-- url     : https://prove2.me/submissions/b3e56f2b-bc81-4f52-bd9f-78cb3071001e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : ConsecutiveRatioPowerBound := by
  intro q f N hN hf hq
  have h1 : 4 * f + 2 ≤ q := by nlinarith
  have hQ : (4:ℝ) * f + 2 ≤ q := by exact_mod_cast h1
  have hF : (1:ℝ) ≤ f := by exact_mod_cast hf
  generalize (q:ℝ) = Q at *
  have hQ2 : 0 < Q - 2 := by linarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = 1 / (Q - 2) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x ≤ 1/4 := by rw [hx, div_le_div_iff₀ hQ2 (by norm_num)]; linarith
  have e : (Q - 1)/(Q - 2) = 1 + x := by rw [hx]; field_simp; ring
  rw [e]
  have b1 : 1 + (f:ℝ) * (-x) ≤ (1 + (-x))^f := one_add_mul_le_pow (by linarith) f
  have b2 : (1 + x)^f * (1 + (-x))^f ≤ 1 := by
    rw [← mul_pow]; apply pow_le_one₀ <;> nlinarith
  have hfx : (f:ℝ) * x ≤ 1/4 := by rw [hx, mul_one_div, div_le_div_iff₀ hQ2 (by norm_num)]; linarith
  have pos : 0 < 1 + (f:ℝ) * (-x) := by linarith
  have b3 : (1+x)^f * (1 + (f:ℝ) * (-x)) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left b1 (by positivity)) b2
  have b4 : 1 ≤ (1 + 2*(f:ℝ)/Q) * (1 + (f:ℝ) * (-x)) := by
    have : (1 + 2*(f:ℝ)/Q) * (1 + (f:ℝ) * (-x)) - 1 = (f:ℝ)*(Q-4-2*f)/(Q*(Q-2)) := by
      rw [hx]; field_simp; ring
    have h2 : 0 ≤ (f:ℝ)*(Q-4-2*f)/(Q*(Q-2)) := by
      apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    linarith
  exact le_of_mul_le_mul_right (le_trans b3 b4) pos
end Formalism.HermitianLattices.LocalLatticeBases
