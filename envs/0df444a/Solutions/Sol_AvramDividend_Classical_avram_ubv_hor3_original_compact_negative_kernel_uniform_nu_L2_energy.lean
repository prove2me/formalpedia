-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_compact_negative_kernel_uniform_nu_L2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:17:58.852064+00:00
-- url     : https://prove2.me/submissions/1d0046e4-dc6c-42b8-a27a-1ce0aeae9b81

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
    (hK : ENNReal.ofReal K < C) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧
      ∀ u ∈ Icc δ K,
        (∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν) ≤ A := by
  obtain ⟨M, hM0, hBound⟩ :=
    avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
      w C hw_cont hw_neg hw_smooth δ K hδ hδK hK
  let core : ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (min (1 : ℝ) (z ^ 2))
  have hCoreMeas : Measurable core := by
    dsimp [core]
    fun_prop
  have hν : (∫⁻ z, core z ∂X.ν) < ⊤ := X.ν_integrable
  let A : ℝ≥0∞ := ENNReal.ofReal M * ∫⁻ z, core z ∂X.ν
  have hAFin : A < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν
  refine ⟨A, hAFin, ?_⟩
  intro u hu
  let f : ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal ((w (u + z) - w u) ^ 2)
  have hDom : (Iio (0 : ℝ)).indicator f ≤
      fun z => ENNReal.ofReal M * core z := by
    intro z
    by_cases hz : z ∈ Iio (0 : ℝ)
    · have hMinNN : 0 ≤ min (1 : ℝ) (z ^ 2) :=
        le_min (by norm_num) (sq_nonneg z)
      have hReal := hBound u hu z hz
      have hCast := ENNReal.ofReal_le_ofReal hReal
      rw [ENNReal.ofReal_mul hM0] at hCast
      simpa only [Set.indicator_of_mem hz, f, core] using hCast
    · simp [Set.indicator_of_notMem hz]
  have hInt :
      (∫⁻ z, (Iio (0 : ℝ)).indicator f z ∂X.ν) =
      ∫⁻ z in Iio (0 : ℝ), f z ∂X.ν :=
    lintegral_indicator (by simp : MeasurableSet (Iio (0 : ℝ))) f
  change (∫⁻ z in Iio (0 : ℝ), f z ∂X.ν) ≤ A
  rw [← hInt]
  calc
    (∫⁻ z, (Iio (0 : ℝ)).indicator f z ∂X.ν) ≤
        ∫⁻ z, ENNReal.ofReal M * core z ∂X.ν := lintegral_mono hDom
    _ = A := by
      dsimp [A]
      exact lintegral_const_mul _ hCoreMeas
