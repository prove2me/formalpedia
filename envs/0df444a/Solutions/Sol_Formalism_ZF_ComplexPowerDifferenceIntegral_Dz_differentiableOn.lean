-- Prove2me | solution 1 for Formalism.ZF.ComplexPowerDifferenceIntegral.Dz_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:48:33.077462+00:00
-- url     : https://prove2.me/submissions/2739922f-6e66-4974-b3bd-fe735be87e20

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_norm_dz_le
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_summable_shift

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
open Formalism Formalism.ZF
open Formalism.ZF.ComplexPowerDifferenceIntegral
namespace Formalism.ZF.ComplexPowerDifferenceIntegral
theorem _root_.solution : DifferentiableOn ℂ Dz {s : ℂ | 0 < s.re} := by
  intro s0 hs0
  have hs0' : 0 < s0.re := hs0
  let U : Set ℂ := {s | s0.re / 2 < s.re} ∩ Metric.ball s0 1
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s0 ∈ U := ⟨by show s0.re / 2 < s0.re; linarith, Metric.mem_ball_self one_pos⟩
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun s => dz s n) U := by
    intro n
    apply Differentiable.differentiableOn
    intro s
    have h1 : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : ((n : ℝ) + 1) ≠ 0)
    have h2 : ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : ((n : ℝ) + 1 + 1) ≠ 0)
    unfold dz
    refine ((DifferentiableAt.sub ?_ ?_).sub ((differentiableAt_id.sub_const 1).mul ?_))
    · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h1)
    · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h2)
    · exact differentiableAt_id.neg.const_cpow (Or.inl h2)
  have hbound : ∀ n : ℕ, ∀ s ∈ U,
      ‖dz s n‖ ≤ (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) := by
    intro n s hs
    have hre : s0.re / 2 < s.re := hs.1
    have hd : ‖s - s0‖ < 1 := by
      have := hs.2
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have hpos : 0 < s.re := by linarith
    have hsR : ‖s‖ ≤ ‖s0‖ + 1 := by
      have := norm_sub_norm_le s s0
      linarith
    have hs1 : ‖s - 1‖ ≤ ‖s0‖ + 1 + 1 := by
      have := norm_sub_le s 1
      rw [norm_one] at this
      linarith
    have hp : ((n : ℝ) + 1) ^ (-s.re - 1) ≤ ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by linarith)
    calc ‖dz s n‖ ≤ ‖s - 1‖ * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := norm_dz_le hpos n
      _ ≤ (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) := by gcongr
  have hsum : Summable (fun n : ℕ =>
      (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1)) :=
    (summable_shift (by linarith)).mul_left _
  have hD : DifferentiableOn ℂ (fun s => ∑' n, dz s n) U :=
    differentiableOn_tsum_of_summable_norm hsum hdiff hU hbound
  exact (hD.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt
end Formalism.ZF.ComplexPowerDifferenceIntegral
