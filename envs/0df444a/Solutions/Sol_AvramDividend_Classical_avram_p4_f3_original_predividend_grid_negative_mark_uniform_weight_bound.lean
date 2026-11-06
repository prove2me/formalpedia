-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_predividend_grid_negative_mark_uniform_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:07:21.984614+00:00
-- url     : https://prove2.me/submissions/1579cd07-3400-4c44-91d1-b665a9bc8454

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical original clipped pre-dividend grid coefficients are uniformly bounded across negative mark cells. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (grid : ℕ → ℝ≥0) (z : ι → ℕ → ℝ)
    (hz : ∀ j i, z j i < 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ j i ω,
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (grid i)
      let u := if y ∈ Icc δ K then y else δ
      |w (u + z j i) - w u| ≤ L := by
  obtain ⟨M, hM0, hM⟩ :=
    avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
      w C hw_cont hw_neg hw_smooth δ K hδ hδK hK
  refine ⟨M + 1, by linarith, ?_⟩
  intro j i ω
  let y : ℝ := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (grid i)
  let u : ℝ := if y ∈ Icc δ K then y else δ
  have hu : u ∈ Icc δ K := by
    dsimp [u]
    split_ifs with hp
    · exact hp
    · exact ⟨le_refl δ, hδK⟩
  change |w (u + z j i) - w u| ≤ M + 1
  have hsquare : (w (u + z j i) - w u) ^ 2 ≤ M := by
    calc
      (w (u + z j i) - w u) ^ 2
          ≤ M * min 1 ((z j i) ^ 2) := hM u hu (z j i) (hz j i)
      _ ≤ M := by
        have hmin : min (1 : ℝ) ((z j i) ^ 2) ≤ 1 :=
          min_le_left _ _
        nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hmin)]
  have hEq : |w (u + z j i) - w u| ^ 2 =
      (w (u + z j i) - w u) ^ 2 := by
    simp
  nlinarith
    [sq_nonneg (|w (u + z j i) - w u| - (1 / 2 : ℝ))]
