-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_dil_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:58:16.026375+00:00
-- url     : https://prove2.me/submissions/c88b9ac6-c66b-404c-a48a-0ce20acda703

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (g : ℂ → E) (hgc : Continuous g) (hgs : HasCompactSupport g) (ζ : ℂ) (hζ : ζ ≠ 0) :
    Tendsto (fun ρ : ℂ => ∫ z, ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2) (𝓝 ζ) (𝓝 0) := by
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hgs
  obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hζ0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hzero : ∀ w : ℂ, max R 0 < ‖w‖ → g w = 0 := by
    intro w hw
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    linarith [le_max_left R 0]
  have hR0 : 0 ≤ max R 0 := le_max_right R 0
  have hr0 : 0 ≤ 2 * max R 0 / ‖ζ‖ := by positivity
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (F := fun ρ z => ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2)
    (f := fun z => ‖‖ζ‖ • g (ζ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2)
    (μ := volume) (l := 𝓝 ζ)
    ((Metric.closedBall (0 : ℂ) (2 * max R 0 / ‖ζ‖)).indicator fun _ => (3 * ‖ζ‖ * M) ^ 2) ?_ ?_ ?_ ?_
  · simpa using hlim
  · refine Filter.Eventually.of_forall fun ρ => ?_
    have hc : Continuous fun z => ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 := by fun_prop
    exact hc.aestronglyMeasurable
  · have hball : Metric.ball ζ (‖ζ‖ / 2) ∈ 𝓝 ζ := Metric.ball_mem_nhds ζ (by positivity)
    filter_upwards [hball] with ρ hρ
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hρ
    have hρlo : ‖ζ‖ / 2 ≤ ‖ρ‖ := by
      have h1 := norm_sub_norm_le ζ ρ
      rw [norm_sub_rev] at h1
      linarith
    have hρhi : ‖ρ‖ ≤ 2 * ‖ζ‖ := by
      have h1 := norm_le_insert' ρ ζ
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) (2 * max R 0 / ‖ζ‖)
    · rw [Set.indicator_of_mem hz]
      have h1 : ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ≤ 3 * ‖ζ‖ * M := by
        calc ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖
            ≤ ‖‖ρ‖ • g (ρ * z)‖ + ‖‖ζ‖ • g (ζ * z)‖ := norm_sub_le _ _
          _ = ‖ρ‖ * ‖g (ρ * z)‖ + ‖ζ‖ * ‖g (ζ * z)‖ := by
              rw [norm_smul, norm_smul, norm_norm, norm_norm]
          _ ≤ 2 * ‖ζ‖ * M + ‖ζ‖ * M :=
              add_le_add (mul_le_mul hρhi (hM _) (norm_nonneg _) (by positivity))
                (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
          _ = 3 * ‖ζ‖ * M := by ring
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · rw [Set.indicator_of_notMem hz]
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
      have e1 : g (ρ * z) = 0 := by
        apply hzero
        rw [norm_mul]
        calc max R 0 = ‖ζ‖ / 2 * (2 * max R 0 / ‖ζ‖) := by field_simp
          _ < ‖ζ‖ / 2 * ‖z‖ := by gcongr
          _ ≤ ‖ρ‖ * ‖z‖ := by gcongr
      have e2 : g (ζ * z) = 0 := by
        apply hzero
        rw [norm_mul]
        calc max R 0 ≤ ‖ζ‖ / 2 * (2 * max R 0 / ‖ζ‖) := by field_simp; rfl
          _ < ‖ζ‖ / 2 * ‖z‖ := by gcongr
          _ ≤ ‖ζ‖ * ‖z‖ := by gcongr; linarith
      rw [e1, e2]
      simp
  · exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  · refine Filter.Eventually.of_forall fun z => ?_
    have hc : Continuous fun ρ : ℂ => ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 := by fun_prop
    exact hc.tendsto ζ
end Formalism.FourierDecayAlt.P.PBK
