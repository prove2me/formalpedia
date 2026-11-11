-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_uniform_negative_mark_bv_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:58:50.294879+00:00
-- url     : https://prove2.me/submissions/4897d497-c410-4f1d-920f-c30d61dfa90e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- A compactly supported finite negative-jump law has both the Lévy
quadratic moment and finite small-jump variation required by the BV record. -/
theorem solution :
    (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2))
      ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) < ⊤ ∧
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y|
      ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) < ⊤ := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)
  have hmass : ν Set.univ = 1 := by
    simp [ν, Measure.restrict_apply_univ, Real.volume_Ioo]
  have hquadratic : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤ := by
    have hb (y : ℝ) :
        ENNReal.ofReal (min 1 (y ^ 2)) ≤ (1 : ENNReal) := by
      simpa using
        (ENNReal.ofReal_le_ofReal (min_le_left (1 : ℝ) (y ^ 2)))
    calc
      (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν)
          ≤ ∫⁻ _ : ℝ, (1 : ENNReal) ∂ν := lintegral_mono hb
      _ = 1 := by simpa [hmass]
      _ < ⊤ := ENNReal.one_lt_top
  have hvariation :
      (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂ν) < ⊤ := by
    have hb :
        ∀ᵐ y ∂(ν.restrict (Ioo (-1 : ℝ) 0)),
          ENNReal.ofReal |y| ≤ (1 : ENNReal) := by
      filter_upwards [ae_restrict_mem (μ := ν) measurableSet_Ioo] with y hy
      have hle : |y| ≤ (1 : ℝ) := by
        apply abs_le.mpr
        constructor <;> linarith [hy.1, hy.2]
      simpa using ENNReal.ofReal_le_ofReal hle
    calc
      (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂ν)
          ≤ ∫⁻ _ in Ioo (-1 : ℝ) 0, (1 : ENNReal) ∂ν :=
            lintegral_mono_ae hb
      _ = ν (Ioo (-1 : ℝ) 0) := by simp
      _ ≤ ν Set.univ := measure_mono (subset_univ _)
      _ = 1 := hmass
      _ < ⊤ := ENNReal.one_lt_top
  exact ⟨hquadratic, hvariation⟩
