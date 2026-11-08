-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_actual_capped_stopped_bracket_le_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:02:52.535845+00:00
-- url     : https://prove2.me/submissions/1ecd94f3-6f75-42b7-ab4d-3a6ff5db9d5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_square_energy_integrableOn
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_square_bracket_le_deterministic
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_capped_ruin_bracket_le_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform cap on the true original Gaussian square bracket at a random clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (μtime : Measure ℝ≥0) (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤)
    (τ : Ω → ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω,
      (∫ t in Ioc (0 : ℝ≥0) (min (τ ω) T),
        (G (t, ω)) ^ 2 ∂μtime) ≤
      C ^ 2 * (μtime.restrict (Ioc (0 : ℝ≥0) T)).real Set.univ := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
  have hEnergy : ∀ ω, IntegrableOn
      (fun t : ℝ≥0 => (G (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) T) μtime :=
    avram_ubv_gaussian10_actual_masked_square_energy_integrableOn
      X x D hD w a b u v hw hau huv hvb μ hμ μtime T hFinite
  have hw1 : ContDiffOn ℝ 1 w (Ioo a b) := hw.of_le (by norm_num)
  obtain ⟨C, hC, hBound⟩ :=
    avram_ubv_gaussian10_actual_masked_square_bracket_le_deterministic
      X x D hD w a b u v hw1 hau huv hvb μtime T hFinite
  change ∃ C : ℝ, 0 ≤ C ∧ ∀ ω,
    (∫ t in Ioc (0 : ℝ≥0) (min (τ ω) T),
      (G (t, ω)) ^ 2 ∂μtime) ≤
      C ^ 2 * (μtime.restrict (Ioc (0 : ℝ≥0) T)).real Set.univ
  refine ⟨C, hC, ?_⟩
  intro ω
  exact (avram_ubv_gaussian10_original_capped_ruin_bracket_le_horizon
    X G μtime τ T hEnergy ω).trans (hBound ω)
