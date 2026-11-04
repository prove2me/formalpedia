-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_finite_cap_stopped_terminal_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:13:48.18207+00:00
-- url     : https://prove2.me/submissions/c206019d-33ae-46df-bf35-d8a2b9f141ee

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_zero_extended_continuous_value_bounded_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True stopped terminal is deterministically bounded at a finite cap,
including ruin overshoots and the original right-limit dividend state. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ω, |Term ω| ≤ B := by
  obtain ⟨B, hB0, hBound⟩ :=
    avram_p4_f_assembly_zero_extended_continuous_value_bounded_on_finite_cap
      w c hc hw_cont hw_neg
  have hWcap :=
    avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
      X x c hc hxc D hD τ W hW
  refine ⟨B, hB0, ?_⟩
  intro ω
  have he : Real.exp (-(q * (τ ω : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg hq (NNReal.coe_nonneg (τ ω)))
  calc
    |Term ω| = Real.exp (-(q * (τ ω : ℝ))) * |w (W ω)| := by
      rw [hTerm ω, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-(q * (τ ω : ℝ))) * B :=
      mul_le_mul_of_nonneg_left (hBound (W ω) (hWcap ω))
        (le_of_lt (Real.exp_pos _))
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right he hB0
    _ = B := one_mul B
