-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB118_bounded_ae_L2_loss_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:18:00.250196+00:00
-- url     : https://prove2.me/submissions/53134f7e-f115-4017-9003-5ad124ec096a

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ m, AEStronglyMeasurable (f m) μ)
    (hg : AEStronglyMeasurable g μ)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ m, ∀ᵐ a ∂μ, |f m a| ≤ B)
    (hgb : ∀ᵐ a ∂μ, |g a| ≤ B)
    (hae : ∀ᵐ a ∂μ,
      Tendsto (fun m => f m a) atTop (𝓝 (g a))) :
    Tendsto (fun m => ∫ a, (f m a - g a) ^ 2 ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  have hF (m : ℕ) :
      AEStronglyMeasurable (fun a => (f m a - g a) ^ 2) μ :=
    ((hf m).sub hg).pow 2
  have hConst : Integrable (fun _ : α => (2 * B) ^ 2) μ :=
    integrable_const _
  have hdom (m : ℕ) :
      ∀ᵐ a ∂μ, ‖(f m a - g a) ^ 2‖ ≤ (2 * B) ^ 2 := by
    filter_upwards [hfb m, hgb] with a hfa hga
    have hDiff : |f m a - g a| ≤ 2 * B := by
      calc
        _ ≤ |f m a| + |g a| := abs_sub _ _
        _ ≤ B + B := add_le_add hfa hga
        _ = 2 * B := by ring
    have h2B : 0 ≤ 2 * B := by positivity
    have hProd : 0 ≤ (2 * B - |f m a - g a|) *
        (2 * B + |f m a - g a|) :=
      mul_nonneg (sub_nonneg.mpr hDiff)
        (add_nonneg h2B (abs_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (f m a - g a)]
  have hlim : ∀ᵐ a ∂μ,
      Tendsto (fun m => (f m a - g a) ^ 2) atTop
        (𝓝 (0 : ℝ)) := by
    filter_upwards [hae] with a ha
    have hc : Tendsto (fun _ : ℕ => g a) atTop (𝓝 (g a)) :=
      tendsto_const_nhds
    have hsub : Tendsto (fun m => f m a - g a) atTop
        (𝓝 (0 : ℝ)) := by
      simpa only [sub_self] using ha.sub hc
    simpa using hsub.pow 2
  have hDCT :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : α => (2 * B) ^ 2) hF hConst hdom hlim
  simpa using hDCT
