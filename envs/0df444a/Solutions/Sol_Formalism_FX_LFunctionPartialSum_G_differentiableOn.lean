-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.G_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:52.112816+00:00
-- url     : https://prove2.me/submissions/5684ed07-31d8-40a2-a32e-5d84146c4cdc

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_dterm_zero
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_norm_dterm_le

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
open Formalism Formalism.FX
open Formalism.FX.LFunctionPartialSum
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.FX.LFunctionPartialSum
theorem _root_.solution {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) :
    DifferentiableOn ℂ (G χ) {s : ℂ | 0 < s.re} := by
  intro s0 hs0
  have hs0' : 0 < s0.re := hs0
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hUo : IsOpen ({s : ℂ | s0.re / 2 < s.re} ∩ Metric.ball 0 (‖s0‖ + 1)) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hs0U : s0 ∈ {s : ℂ | s0.re / 2 < s.re} ∩ Metric.ball 0 (‖s0‖ + 1) := by
    refine ⟨?_, ?_⟩
    · show s0.re / 2 < s0.re
      linarith
    · simp
  have hdiff : DifferentiableOn ℂ (fun w => ∑' n, dterm χ w n)
      ({s : ℂ | s0.re / 2 < s.re} ∩ Metric.ball 0 (‖s0‖ + 1)) := by
    apply Complex.differentiableOn_tsum_of_summable_norm (F := fun n w => dterm χ w n)
      (u := fun n : ℕ => B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1)))
    · exact ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _).mul_left _
    · intro n w hw
      have h1 : s0.re / 2 < w.re := hw.1
      have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at h1; linarith
      apply DifferentiableAt.differentiableWithinAt
      show DifferentiableAt ℂ (fun w => Ap χ n * ((n : ℂ) ^ (-w) - ((n : ℂ) + 1) ^ (-w))) w
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.sub
      · exact (differentiableAt_id.neg).const_cpow (Or.inr (neg_ne_zero.mpr hw0))
      · exact (differentiableAt_id.neg).const_cpow (Or.inr (neg_ne_zero.mpr hw0))
    · exact hUo
    · intro n w hw
      have h1 : s0.re / 2 < w.re := hw.1
      have h2 : ‖w‖ < ‖s0‖ + 1 := by simpa using hw.2
      have hwre : 0 < w.re := by linarith
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · show ‖dterm χ w 0‖ ≤ B * ((‖s0‖ + 1) * ((0 : ℕ) : ℝ) ^ (-(s0.re / 2) - 1))
        rw [dterm_zero, norm_zero]
        exact mul_nonneg hB0 (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · show ‖dterm χ w n‖ ≤ B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1))
        refine (norm_dterm_le χ hB hwre n).trans ?_
        apply mul_le_mul_of_nonneg_left _ hB0
        apply mul_le_mul h2.le _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn) (by linarith)
  exact (hdiff.differentiableAt (hUo.mem_nhds hs0U)).differentiableWithinAt
end Formalism.FX.LFunctionPartialSum
