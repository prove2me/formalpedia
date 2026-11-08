-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_discounted_true_stopped_generator_L1_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:18:21.140701+00:00
-- url     : https://prove2.me/submissions/a7b5890a-aaf1-4187-9bc1-e9ff560ef60d

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_discounted_compact_stopped_generator_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuinely stopped compact source generator has a nonpositive pathwise
time integral, and the resulting random variable is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C.toReal)
    (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (ρ p * (if Y p ∈ Icc (u + δ) v then
          X.generator w (Y p) - q * w (Y p) else 0))
    Integrable (fun ω => ∫ t : ℝ≥0,
      if t ≤ σ ω then R (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∀ ω, (∫ t : ℝ≥0,
      if t ≤ σ ω then R (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ≤ 0)  := by
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let ρ : ℝ≥0 × Ω → ℝ := fun p =>
    if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
  let R : ℝ≥0 × Ω → ℝ := fun p =>
    Real.exp (-(q * (p.1 : ℝ))) *
      (ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0))
  have hIntegrable := avram_ubv_finite9_discounted_compact_stopped_generator_L1
    X x D C hD hC hFinite w hw_smooth hw_cont hw_neg q hq
    hw_gen hw_grad u v δ hu hδ hδone huv hv T σ hσstop
  have hR : ∀ p : ℝ≥0 × Ω, R p ≤ 0 := by
    intro p
    by_cases hlo : u + δ ≤ Y p
    · by_cases hhi : Y p ≤ v
      · by_cases hruin : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
        · have hpos : 0 < Y p := by linarith
          have hbelow : Y p < C.toReal := lt_of_le_of_lt hhi hv
          have hcap : ENNReal.ofReal (Y p) < C :=
            (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hpos) hFinite).2 hbelow
          have hgen := (hw_gen (Y p) hpos hcap).2
          simpa [R, ρ, mem_Icc, hlo, hhi, hruin] using
            (mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hgen)
        · simp [R, ρ, mem_Icc, hlo, hhi, hruin]
      · simp [R, ρ, mem_Icc, hlo, hhi]
    · simp [R, ρ, mem_Icc, hlo]
  dsimp only at hIntegrable ⊢
  constructor
  · exact hIntegrable
  · intro ω
    apply integral_nonpos_of_ae
    filter_upwards [] with t
    by_cases hclock : t ≤ σ ω
    · simpa [R, ρ, Y, hclock] using hR (t, ω)
    · simp [hclock]
