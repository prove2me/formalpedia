-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_source_slack_exact_signed_fatou_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:43:29.833199+00:00
-- url     : https://prove2.me/submissions/42ccf7f0-ac17-4bb7-8917-ab06bea51a19

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_ennreal_liminf_scaled_tendsto_one
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_scaled_signed_source_mean_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_source_slack_exact_pointwise_rescale
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_source_slack_ratio_tendsto_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory
open AvramDividend.Classical
open scoped ENNReal
open scoped Topology
noncomputable section

/-- Normalise a genuine signed source inequality with a vanishing deterministic
grid error, preserving the combined L1 source and the original lower Fatou limit. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ) (hw : 0 < w) (Y : Ω → ℝ)
    (F M B : ℕ → Ω → ℝ) (e : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n)
    (he0 : Filter.Tendsto e Filter.atTop (nhds (0 : ℝ)))
    (hMeas : ∀ n, Measurable (F n))
    (hInt : ∀ n, Integrable (F n) P)
    (hPos : ∀ n, 0 ≤ᵐ[P] F n)
    (hSigned : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w + (M n ω + B n ω) + e n)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        Filter.liminf (fun n => ENNReal.ofReal (F n ω)) Filter.atTop) :
    ∃ F' M' B' : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n) ∧ Integrable (F' n) P ∧
        0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M' n ω + B' n ω) P ∧
        (∫ ω, M' n ω + B' n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P, F' n ω ≤
        w + (M' n ω + B' n ω)) ∧
      (∀ᵐ ω ∂P, ENNReal.ofReal (Y ω) ≤
        Filter.liminf (fun n => ENNReal.ofReal (F' n ω)) Filter.atTop) := by
  let a : ℕ → ℝ := fun n => w / (w + e n)
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    exact div_nonneg hw.le (add_nonneg hw.le (he n))
  let A : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (a n)
  have hA : Tendsto A atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [A, a] using
      avram_p3_grid4_source_slack_ratio_tendsto_one w hw e he0
  refine ⟨(fun n ω => a n * F n ω), (fun n ω => a n * M n ω),
    (fun n ω => a n * B n ω), ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨(hMeas n).const_mul _, (hInt n).const_mul _, ?_⟩
    filter_upwards [hPos n] with ω hω
    exact mul_nonneg (ha n) hω
  · intro n
    simpa only [mul_add] using
      avram_p3_grid4_scaled_signed_source_mean_nonpos P
        (fun n ω => M n ω + B n ω) a ha hSigned n
  · intro n
    filter_upwards [hPath n] with ω hω
    simpa only [mul_add] using
      avram_p3_grid4_source_slack_exact_pointwise_rescale
        w (e n) (F n ω) (M n ω + B n ω) hw (he n) hω
  · filter_upwards [hFatou] with ω hω
    calc
      ENNReal.ofReal (Y ω) ≤
          liminf (fun n => ENNReal.ofReal (F n ω)) atTop := hω
      _ ≤ liminf (fun n => ENNReal.ofReal (a n * F n ω)) atTop := by
        have hlim := avram_p3_grid4_ennreal_liminf_scaled_tendsto_one
          (fun n => ENNReal.ofReal (F n ω)) A hA
        have heq : (fun n => A n * ENNReal.ofReal (F n ω)) =
            (fun n => ENNReal.ofReal (a n * F n ω)) := by
          funext n
          exact (ENNReal.ofReal_mul (ha n)).symm
        simpa only [heq] using hlim
