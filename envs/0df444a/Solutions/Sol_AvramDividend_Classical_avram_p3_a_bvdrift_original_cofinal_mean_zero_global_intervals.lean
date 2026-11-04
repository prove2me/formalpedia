-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_mean_zero_global_intervals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:34:16.91654+00:00
-- url     : https://prove2.me/submissions/fab9b6e0-478a-4e04-b0b9-1dee5c316b16

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Mean-zero actual BV residual on arbitrary cofinal horizons yields one
all-time full-measure set supporting the true original jump decomposition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℕ → ℝ≥0) (hT : ∀ t : ℝ≥0, ∃ n, t ≤ T n)
    (hInt : ∀ n : ℕ, Integrable (fun ω : Ω =>
      ((T n : ℝ) * X.drift - X.X (T n) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T n then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) P)
    (hMean : ∀ n : ℕ, (∫ ω : Ω,
      (((T n : ℝ) * X.drift - X.X (T n) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T n then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      X.X t ω - X.X s ω =
        ((t : ℝ) - (s : ℝ)) * X.drift -
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by
  have hNat : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T n →
      X.X t ω - X.X s ω =
        ((t : ℝ) - (s : ℝ)) * X.drift -
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by
    intro n
    exact avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals
      X hBV (T n) (hInt n) (hMean n)
  filter_upwards [(ae_all_iff.mpr hNat)] with ω hω
  intro s t hst
  obtain ⟨n, htn⟩ := hT t
  exact hω n s t hst htn
