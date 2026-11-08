-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_actual_masked_terminal_bracket_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:29:49.652771+00:00
-- url     : https://prove2.me/submissions/c23f02b8-2f71-4cab-b613-159421a576a6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_stopped_gradient_gaussian_bracket_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_uniform_terminal_square_bracket_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped-gradient Gaussian source has an L¹ terminal bracket. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (μtime : Measure ℝ≥0) [SFinite μtime]
    (T : ℝ≥0) (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    Integrable (fun ω => ∫ t in Ioc (0 : ℝ≥0) T,
      (G (t, ω)) ^ 2 ∂μtime) P := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
  have hw1 : ContDiffOn ℝ 1 w (Ioo a b) := hw.of_le (by norm_num)
  obtain ⟨C, hC, hB⟩ :=
    avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
      X x D hD w a b u v hw1 hau huv hvb
  have hA : Adapted 𝓕.rightCont (fun t ω =>
      ∫ s in Ioc (0 : ℝ≥0) t, (G (s, ω)) ^ 2 ∂μtime) :=
    avram_ubv_gaussian10_actual_stopped_gradient_gaussian_bracket_adapted
      X x D hD w a b u v hw hau huv hvb μ hμ μtime
  have hm : Measurable (fun ω => ∫ t in Ioc (0 : ℝ≥0) T,
      (G (t, ω)) ^ 2 ∂μtime) :=
    (hA T).mono (𝓕.rightCont.le T) le_rfl
  change Integrable (fun ω => ∫ t in Ioc (0 : ℝ≥0) T,
    (G (t, ω)) ^ 2 ∂μtime) P
  exact avram_ubv_gaussian10_uniform_terminal_square_bracket_L1
    G μtime T hFinite C hC hB hm
