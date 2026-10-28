-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_weighted_killed_survival_inner_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:01:13.961593+00:00
-- url     : https://prove2.me/submissions/ff94c7d8-cf1d-4dcf-9bb9-638f51bac1aa

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_killed_survival_inner_lintegral_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω) (β θ : ℝ) (hβ : 0 < β) :
    (∫⁻ (x : ℝ),
      Set.indicator
        {y : ℝ | 0 < y ∧ ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}
        (fun y => ENNReal.ofReal
          (Real.exp (-β * y) *
            Real.exp (θ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) x ∂volume) =
    ENNReal.ofReal
      (Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
    ENNReal.ofReal
      (Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) := by
  let m : ℝ := sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}
  let S : Set ℝ := {y | 0 < y ∧ ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}
  have hb := levy_path_bddBelow_finite_horizon X t ω
  have hS : MeasurableSet S := by
    have heq : S = {y : ℝ | 0 < y ∧ 0 ≤ y + m} := by
      ext y
      exact and_congr_right fun _ =>
        (lower_survival_running_infimum_equiv X t ω hb y)
    rw [heq]
    exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_const (measurable_id.add_const m))
  let c : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (θ * X.X t ω -
      (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))
  have hbase : Measurable (fun y : ℝ =>
      S.indicator (fun z => ENNReal.ofReal (Real.exp (-β * z))) y) :=
    (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_id.const_mul (-β)))).indicator hS
  change (∫⁻ y, S.indicator
    (fun z => ENNReal.ofReal (Real.exp (-β * z) *
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) y ∂volume) = _
  calc
    (∫⁻ y, S.indicator
      (fun z => ENNReal.ofReal (Real.exp (-β * z) *
        Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) y ∂volume) =
      (∫⁻ y, (S.indicator
        (fun z => ENNReal.ofReal (Real.exp (-β * z))) y) * c ∂volume) := by
        apply lintegral_congr
        intro y
        by_cases hy : y ∈ S
        · simp only [Set.indicator_of_mem hy, c]
          exact ENNReal.ofReal_mul (Real.exp_nonneg _)
        · simp [Set.indicator_of_notMem hy]
    _ = (∫⁻ y, S.indicator
      (fun z => ENNReal.ofReal (Real.exp (-β * z))) y ∂volume) * c :=
      MeasureTheory.lintegral_mul_const c hbase
    _ = _ := by
      rw [killed_survival_inner_lintegral_envelope X t ω β hβ]
