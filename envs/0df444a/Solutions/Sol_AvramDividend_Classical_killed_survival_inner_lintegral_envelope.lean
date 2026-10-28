-- Prove2me | solution 1 for AvramDividend.Classical.killed_survival_inner_lintegral_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:51:46.998242+00:00
-- url     : https://prove2.me/submissions/d0da6d85-cc66-4096-a13b-629becf3765e

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_pathwise_killed_survival_laplace_envelope_all_paths

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Evaluating the nonnegative capital kernel gives the reflected-infimum envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ (x : ℝ),
      Set.indicator
        {y : ℝ | 0 < y ∧ ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}
        (fun y => ENNReal.ofReal (Real.exp (-θ * y))) x ∂volume) =
    ENNReal.ofReal
      (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ) := by
  let m : ℝ := sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}
  let S : Set ℝ :=
    {y : ℝ | 0 < y ∧ ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}
  have hb := levy_path_bddBelow_finite_horizon X t ω
  have hset : S = {y : ℝ | 0 < y ∧ 0 ≤ y + m} := by
    ext y
    change (0 < y ∧ ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω) ↔
      (0 < y ∧ 0 ≤ y + m)
    constructor
    · rintro ⟨hy, hs⟩
      exact ⟨hy, (lower_survival_running_infimum_equiv X t ω hb y).mp hs⟩
    · rintro ⟨hy, hs⟩
      exact ⟨hy, (lower_survival_running_infimum_equiv X t ω hb y).mpr hs⟩
  have hS : MeasurableSet S := by
    rw [hset]
    exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_const (measurable_id.add_const m))
  have hsub : S ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact hy.1
  have hn : -θ < 0 := neg_lt_zero.mpr hθ
  have hbase : IntegrableOn (fun y : ℝ => Real.exp (-θ * y))
      (Ioi (0 : ℝ)) volume :=
    integrableOn_exp_mul_Ioi hn 0
  have hint : IntegrableOn (fun y : ℝ => Real.exp (-θ * y)) S volume :=
    hbase.mono_set hsub
  have hKilled : Integrable
      (S.indicator (fun y : ℝ => Real.exp (-θ * y))) volume :=
    hint.integrable_indicator hS
  have hNonneg : ∀ y, 0 ≤ S.indicator
      (fun z : ℝ => Real.exp (-θ * z)) y := by
    intro y
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy]
      exact Real.exp_nonneg _
    · rw [Set.indicator_of_notMem hy]
  change (∫⁻ y, S.indicator
    (fun z : ℝ => ENNReal.ofReal (Real.exp (-θ * z))) y ∂volume) = _
  calc
    (∫⁻ y, S.indicator
      (fun z : ℝ => ENNReal.ofReal (Real.exp (-θ * z))) y ∂volume) =
        (∫⁻ y, ENNReal.ofReal
          (S.indicator (fun z : ℝ => Real.exp (-θ * z)) y) ∂volume) := by
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ S
      · simp only [Set.indicator_of_mem hy]
      · simp only [Set.indicator_of_notMem hy, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal
        (∫ y, S.indicator (fun z : ℝ => Real.exp (-θ * z)) y ∂volume) :=
      (ofReal_integral_eq_lintegral_ofReal hKilled
        (Filter.Eventually.of_forall hNonneg)).symm
    _ = ENNReal.ofReal
        (∫ y in S, Real.exp (-θ * y) ∂volume) := by
      rw [integral_indicator hS]
    _ = _ := by
      exact congrArg ENNReal.ofReal
        (pathwise_killed_survival_laplace_envelope_all_paths X t ω θ hθ)
