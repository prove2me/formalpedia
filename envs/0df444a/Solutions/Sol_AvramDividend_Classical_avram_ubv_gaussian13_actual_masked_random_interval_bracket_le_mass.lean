-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian13_actual_masked_random_interval_bracket_le_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:24:35.689509+00:00
-- url     : https://prove2.me/submissions/266980ea-f7e0-44f4-8027-984ab6b673ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original masked Gaussian bracket increments, between arbitrary random times,
are bounded by one common constant times the physical time-measure mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μtime : Measure ℝ≥0) (s t : Ω → ℝ≥0)
    (hFinite : ∀ ω, μtime (Ioc (s ω) (t ω)) < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω,
      (∫ r in Ioc (s ω) (t ω), (G (r, ω)) ^ 2 ∂μtime) ≤
        K ^ 2 * (μtime.restrict (Ioc (s ω) (t ω))).real Set.univ := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
  obtain ⟨K, hK, hBound⟩ :=
    avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
      X x D hD w a b u v hw hau huv hvb
  change ∃ K : ℝ, 0 ≤ K ∧ ∀ ω,
    (∫ r in Ioc (s ω) (t ω), (G (r, ω)) ^ 2 ∂μtime) ≤
      K ^ 2 * (μtime.restrict (Ioc (s ω) (t ω))).real Set.univ
  refine ⟨K, hK, ?_⟩
  intro ω
  letI : IsFiniteMeasure (μtime.restrict (Ioc (s ω) (t ω))) :=
    (isFiniteMeasure_restrict).2 (hFinite ω).ne
  calc
    (∫ r in Ioc (s ω) (t ω), (G (r, ω)) ^ 2 ∂μtime)
        ≤ |∫ r in Ioc (s ω) (t ω), (G (r, ω)) ^ 2 ∂μtime| :=
            le_abs_self _
    _ = ‖∫ r in Ioc (s ω) (t ω), (G (r, ω)) ^ 2 ∂μtime‖ :=
          (Real.norm_eq_abs _).symm
    _ ≤ K ^ 2 * (μtime.restrict (Ioc (s ω) (t ω))).real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [] with r
      have h0 := abs_nonneg (G (r, ω))
      have h1 := hBound (r, ω)
      have h2 : 0 ≤ K - |G (r, ω)| := sub_nonneg.mpr h1
      have h3 : 0 ≤ K + |G (r, ω)| := add_nonneg hK h0
      have hh := mul_nonneg h2 h3
      simp only [Real.norm_eq_abs, abs_pow]
      nlinarith
