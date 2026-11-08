-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps15_original_weighted_stopped_Taylor_energy_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:30:48.652058+00:00
-- url     : https://prove2.me/submissions/7a93c6e0-6401-480c-97e4-5b0f93557922

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The original negative-jump energy envelope survives predictable weighting and a further stop. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (a : (ℝ≥0 × Ω) → ℝ) (ha : ∀ p, |a p| ≤ 1)
    (σ : Ω → ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1.1 ≤ σ p.1.2 then a p.1 * HS p else 0
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ p : ((ℝ≥0 × Ω) × ℝ), p.2 < 0 →
        |G p| ≤ M * min 1 (p.2 ^ 2) := by
  intro Y H HS G
  obtain ⟨M, hM, hbound⟩ :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_envelope
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
  refine ⟨M, hM, ?_⟩
  intro p hz
  change |if p.1.1 ≤ σ p.1.2 then a p.1 * HS p else 0| ≤
    M * min 1 (p.2 ^ 2)
  by_cases hstop : p.1.1 ≤ σ p.1.2
  · simp only [if_pos hstop, abs_mul]
    calc
      |a p.1| * |HS p| ≤ 1 * |HS p| :=
        mul_le_mul_of_nonneg_right (ha p.1) (abs_nonneg _)
      _ = |HS p| := one_mul _
      _ ≤ M * min 1 (p.2 ^ 2) := hbound p.1 p.2 hz
  · simp only [if_neg hstop, abs_zero]
    exact mul_nonneg hM (le_min (by norm_num) (sq_nonneg _))
