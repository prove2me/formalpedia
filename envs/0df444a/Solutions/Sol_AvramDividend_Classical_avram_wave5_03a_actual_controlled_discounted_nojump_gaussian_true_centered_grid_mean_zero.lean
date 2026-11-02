-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_nojump_gaussian_true_centered_grid_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:35:56.898838+00:00
-- url     : https://prove2.me/submissions/fa02cdca-b30a-45f7-9eae-91fda9180e3a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalSource_stoppedClippedFiniteGrid_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (T : ℝ≥0) (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i) :
    (∫ ω, ∑ i ∈ S,
      max (-K) (min K
        (if s i ≤ T then
          (Real.exp (-(q * (s i : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
          (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then
            (1 : ℝ) else 0)
        else 0)) *
      ((X.X (t i) ω - X.X (s i) ω) - ((t i - s i : ℝ≥0) : ℝ) * X.c) ∂P)
      = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have h0 : IsStoppingTime 𝓕.rightCont
      (fun _ : Ω => (0 : WithTop ℝ≥0)) := isStoppingTime_const 𝓕.rightCont 0
  have hb0 : ∀ ω : Ω, (0 : ℝ≥0) ≤ (0 : ℝ≥0) := by intro ω; exact le_rfl
  let φ : ι → ℝ → ℝ := fun i y => y - ((t i - s i : ℝ≥0) : ℝ) * X.c
  have hφ : ∀ i ∈ S, Measurable (φ i) := by
    intro i hi
    exact measurable_id.sub measurable_const
  have hInt : ∀ i ∈ S, Integrable
      (fun ω => φ i (X.X (t i - s i) ω)) P := by
    intro i hi
    have hm := avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
      X hν (fun _ : Ω => 0) h0 0 hb0 (t i - s i)
    have hh : MemLp (fun ω =>
        X.X (t i - s i) ω - ((t i - s i : ℝ≥0) : ℝ) * X.c) 2 P := by
      simpa only [zero_add, X.X_zero, sub_zero] using hm
    exact hh.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hmean : ∀ i ∈ S,
      (∫ ω, φ i (X.X (t i - s i) ω) ∂P) = 0 := by
    intro i hi
    have hm := avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero
      X hν (fun _ : Ω => 0) h0 0 hb0 (t i - s i)
    simpa only [φ, zero_add, X.X_zero, sub_zero] using hm
  simpa only [φ] using
    (avram_wave3_04_originalSource_stoppedClippedFiniteGrid_mean_zero
      X x D hD w q K hK T S s t hst φ hφ hInt hmean)
