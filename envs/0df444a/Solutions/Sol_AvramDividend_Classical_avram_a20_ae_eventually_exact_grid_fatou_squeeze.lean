-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_ae_eventually_exact_grid_fatou_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:07:58.295232+00:00
-- url     : https://prove2.me/submissions/a6d8a657-5092-4193-a022-504bb573edeb

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Almost-sure eventual physical grid equality and domination determine the exact source mean. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ≥0∞) (K : Ω → ℝ≥0∞) (r : ℝ≥0∞)
    (hFm : ∀ n, Measurable (F n))
    (hBound : ∀ᵐ ω ∂P, ∀ n, F n ω ≤ K ω)
    (hEventually : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, F n ω = K ω)
    (hRate : Tendsto (fun n => ∫⁻ ω, F n ω ∂P) atTop (𝓝 r)) :
    (∫⁻ ω, K ω ∂P) = r := by
  have hLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => F n ω) atTop (𝓝 (K ω)) := by
    filter_upwards [hEventually] with ω hω
    have hEq : (fun n : ℕ => F n ω) =ᶠ[atTop] (fun _ => K ω) := hω
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => K ω)
      atTop (𝓝 (K ω))).congr' hEq.symm
  have hFatou : (∫⁻ ω, K ω ∂P) ≤ r := by
    calc
      (∫⁻ ω, K ω ∂P) =
          ∫⁻ ω, liminf (fun n => F n ω) atTop ∂P := by
            apply lintegral_congr_ae
            filter_upwards [hLim] with ω hw
            exact hw.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop :=
        MeasureTheory.lintegral_liminf_le hFm
      _ = r := hRate.liminf_eq
  have hReverse : r ≤ (∫⁻ ω, K ω ∂P) :=
    le_of_tendsto hRate (Filter.Eventually.of_forall fun n =>
      lintegral_mono_ae (hBound.mono (fun ω hw => hw n)))
  exact le_antisymm hFatou hReverse
