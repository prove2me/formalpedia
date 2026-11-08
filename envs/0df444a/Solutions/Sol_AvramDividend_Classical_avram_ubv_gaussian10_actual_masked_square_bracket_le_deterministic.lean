-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_actual_masked_square_bracket_le_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:56:13.656201+00:00
-- url     : https://prove2.me/submissions/e772a00e-2656-4795-8239-23b1d8f4657f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_uniform_square_bracket_le_deterministic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped Gaussian square energy has an all-path deterministic cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μtime : Measure ℝ≥0) (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω,
      (∫ t in Ioc (0 : ℝ≥0) T, (G (t, ω)) ^ 2 ∂μtime) ≤
        C ^ 2 * (μtime.restrict (Ioc (0 : ℝ≥0) T)).real Set.univ := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
  obtain ⟨C, hC, hBound⟩ :=
    avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
      X x D hD w a b u v hw hau huv hvb
  change ∃ C : ℝ, 0 ≤ C ∧ ∀ ω,
    (∫ t in Ioc (0 : ℝ≥0) T, (G (t, ω)) ^ 2 ∂μtime) ≤
      C ^ 2 * (μtime.restrict (Ioc (0 : ℝ≥0) T)).real Set.univ
  exact ⟨C, hC, avram_ubv_gaussian10_uniform_square_bracket_le_deterministic
    G μtime T hFinite C hC hBound⟩
