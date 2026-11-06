-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_compact_negative_jump_finite_base_quadratic_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:16:58.801706+00:00
-- url     : https://prove2.me/submissions/128ef610-226d-465a-94a5-5acfeac3ec7d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_negative_jump_uniform_nu_square_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform same-source negative-mark quadratic energy integrates over any finite physical time-probability localisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    {S : Type*} [mS : MeasurableSpace S]
    (μ : Measure S) (hμ : μ Set.univ < ⊤)
    (U : S → ℝ) (hU : ∀ s, U s ∈ Icc δ K) :
    (∫⁻ s, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal
        ((w (U s + z) - w (U s)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  obtain ⟨E, hE, hEu⟩ :=
    avram_p4_f3_original_compact_negative_jump_uniform_nu_square_energy
      X w C hw_cont hw_neg hw_smooth δ K hδ hδK hK
  have hPoint (s : S) :
      (∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((w (U s + z) - w (U s)) ^ 2) ∂X.ν) ≤ E :=
    hEu (U s) (hU s)
  calc
    (∫⁻ s, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal
        ((w (U s + z) - w (U s)) ^ 2) ∂X.ν ∂μ) ≤
        (∫⁻ _s : S, E ∂μ) := lintegral_mono hPoint
    _ = E * μ Set.univ := by
      simp [MeasureTheory.lintegral_const, mul_comm]
    _ < ⊤ := ENNReal.mul_lt_top hE hμ
