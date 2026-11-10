-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_singular_pure_jump_process_exists_granular_header
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:41:08.557202+00:00
-- url     : https://prove2.me/submissions/b6bc80a5-7ae6-4022-80a8-cb31b889c51c

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_ProbabilityTheory_exists_isLevyProcess_pureJump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- An explicit negative-jump Lévy density yields a genuine pure-jump process. -/
theorem solution :
    ∃ (ν : Measure ℝ) (hν : IsLevyMeasure ν),
      ν = volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0) ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure μ ∧ IsLevyProcess X μ ∧
        (∀ t, Measurable (X t)) := by
  let f : ℝ → ℝ≥0∞ := fun z =>
    if z ∈ Ioo (-1 : ℝ) 0
    then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0
  let ν : Measure ℝ := volume.withDensity f
  have hf : Measurable f := by
    dsimp [f]
    exact Measurable.ite measurableSet_Ioo
      ((measurable_abs).pow_const (-(3 / 2 : ℝ))).ennreal_ofReal
      measurable_const
  have hν : IsLevyMeasure ν := by
    constructor
    · exact (withDensity_absolutelyContinuous volume f) (by simp)
    · let g : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min 1 (z ^ 2))
      have hg : Measurable g := by
        dsimp [g]
        exact (measurable_const.min (measurable_id'.pow_const (2 : ℕ))).ennreal_ofReal
      have hbound (z : ℝ) :
          f z * g z ≤ (Ioo (-1 : ℝ) 0).indicator (fun _ => (1 : ℝ≥0∞)) z := by
        by_cases hz : z ∈ Ioo (-1 : ℝ) 0
        · have hp : 0 < |z| := abs_pos.mpr (ne_of_lt hz.2)
          have hle : |z| ≤ 1 := by
            rw [abs_of_neg hz.2]
            linarith [hz.1]
          have hpow :
              |z| ^ (-(3 / 2 : ℝ)) * (z ^ 2) = |z| ^ (1 / 2 : ℝ) := by
            calc
              _ = |z| ^ (-(3 / 2 : ℝ)) * |z| ^ (2 : ℕ) := by rw [sq_abs]
              _ = |z| ^ (1 / 2 : ℝ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_add hp]
                congr 1
                norm_num
          simp only [f, g, if_pos hz, Set.indicator_of_mem hz]
          calc
            ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) *
                ENNReal.ofReal (min 1 (z ^ 2))
                ≤ ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) *
                    ENNReal.ofReal (z ^ 2) := by
                  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (min_le_right _ _)) _
            _ = ENNReal.ofReal (|z| ^ (1 / 2 : ℝ)) := by
                  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg z) _), hpow]
            _ ≤ 1 := (ENNReal.ofReal_le_one).2
                  (Real.rpow_le_one (abs_nonneg z) hle (by norm_num))
        · simp only [f, Set.indicator, if_neg hz, zero_mul, le_refl]
      change (∫⁻ z, g z ∂volume.withDensity f) < ⊤
      rw [lintegral_withDensity_eq_lintegral_mul volume hf hg]
      calc
        (∫⁻ z, f z * g z ∂volume) ≤
            ∫⁻ z, (Ioo (-1 : ℝ) 0).indicator (fun _ => (1 : ℝ≥0∞)) z ∂volume :=
          lintegral_mono hbound
        _ = volume (Ioo (-1 : ℝ) 0) := by
          rw [lintegral_indicator measurableSet_Ioo]
          simp
        _ < ⊤ := measure_Ioo_lt_top
  refine ⟨ν, hν, rfl, ?_⟩
  obtain ⟨Ω, mΩ, μ, X, hμ, hX, hmeas, _⟩ :=
    ProbabilityTheory.exists_isLevyProcess_pureJump 0 hν
  exact ⟨Ω, mΩ, μ, X, hμ, hX, hmeas⟩
