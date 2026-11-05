-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_nu_quadratic_tail_l2_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:36:35.592541+00:00
-- url     : https://prove2.me/submissions/882842e9-2cc6-42f2-8d14-ac89763ac3bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_l2_cauchy_of_uniform_band_tail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (C : ℝ)
    (hFinite : ∀ n : ℕ, (∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
        ENNReal.ofReal (z ^ 2) ∂X.ν) ≠ ⊤)
    (hBandBound : ∀ t n m, n ≤ m →
      dist (M n t) (M m t) ≤
        C * Real.sqrt ((∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
        ENNReal.ofReal (z ^ 2) ∂X.ν).toReal)) :
    ∀ t, CauchySeq (fun n => M n t) := by
  let e : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
      ENNReal.ofReal (z ^ 2) ∂X.ν
  have he : Tendsto e atTop (𝓝 0) := by
    simpa [e] using
      avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero X
  have her : Tendsto (fun n => (e n).toReal) atTop (𝓝 (0 : ℝ)) := by
    exact (ENNReal.tendsto_toReal_zero_iff (f := e) (by
      intro n
      exact hFinite n)).2 he
  have hs : Tendsto (fun n => Real.sqrt ((e n).toReal))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      ((Real.continuous_sqrt.tendsto (0 : ℝ)).comp her)
  have hρ : Tendsto (fun n => C * Real.sqrt ((e n).toReal))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hs)
  apply avram_leanlevy_bridge_original_l2_cauchy_of_uniform_band_tail X M
    (fun n => C * Real.sqrt ((e n).toReal))
  · intro ε hε
    exact Filter.Eventually.exists_forall_of_atTop
      (hρ.eventually (eventually_lt_nhds hε))
  · intro t n m hnm
    simpa [e] using hBandBound t n m hnm
