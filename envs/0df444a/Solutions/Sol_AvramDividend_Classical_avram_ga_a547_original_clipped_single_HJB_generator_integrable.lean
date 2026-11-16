-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a547_original_clipped_single_HJB_generator_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:57:21.7035+00:00
-- url     : https://prove2.me/submissions/bf719d3b-e364-49b8-a140-5a34ebba3fb5

import Theorems.Thm_AvramDividend_Classical_avram_ga_a542_original_generator_cell_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
import Theorems.Thm_AvramDividend_Classical_avram_gledger157_original_postpayment_compact_generator_uniform_pointwise_abs_bound
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Cg : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if 0 < ρ ω ∧ s < ρ ω then
        (Δ : ℝ) * E s * X.generator w (Y s)
      else 0
    ∀ m i : ℕ, i < m → Integrable (Cg m i) P := by
  classical
  intro Cg m i hi
  letI : IsProbabilityMeasure P := X.isProbability
  have hMeas := avram_ga_a542_original_generator_cell_aestronglyMeasurable
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen
    x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m i hi
  change AEStronglyMeasurable (Cg m i) P at hMeas
  obtain ⟨M,hM,hjet⟩ :=
    avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
      X x hx D hD.1.1 w C hTopCap hw_smooth ρ j hprefix
  obtain ⟨K,hK,hGen⟩ :=
    avram_gledger157_original_postpayment_compact_generator_uniform_pointwise_abs_bound
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen
      x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let E : ℝ := Real.exp (-(q * (s : ℝ)))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg hq.le (by positivity))
  have hD0 : (0 : ℝ) ≤ Δ := by positivity
  have hCoeff : 0 ≤ (Δ : ℝ) * E ∧ (Δ : ℝ) * E ≤ Δ := by
    constructor
    · exact mul_nonneg hD0 hE0
    · nlinarith [mul_nonneg hD0 (sub_nonneg.mpr hE1)]
  have hBudget : 0 ≤ K + q*M :=
    add_nonneg hK (mul_nonneg hq.le hM)
  have hDom : Integrable (fun _ : Ω => (Δ : ℝ) * (K+q*M)) P :=
    integrable_const _
  apply hDom.mono' hMeas
  filter_upwards [hjet,hGen] with ω hjetω hGenω
  by_cases hactive : 0 < ρ ω ∧ s < ρ ω
  · let y : ℝ := x + X.X s ω - rightLimit D s ω
    have hW : |w y| ≤ M := (hjetω s hactive.2).1
    have hG : |X.generator w y - q*w y| ≤ K := hGenω s hactive.2
    have hGam : |X.generator w y| ≤ K+q*M := by
      calc
        |X.generator w y| = |(X.generator w y - q*w y)+q*w y| := by ring
        _ ≤ |X.generator w y - q*w y| + |q*w y| := abs_add_le _ _
        _ ≤ K + q*M := by
          rw [abs_mul, abs_of_nonneg hq.le]
          exact add_le_add hG (mul_le_mul_of_nonneg_left hW hq.le)
    have hcg : Cg m i ω = (Δ : ℝ) * E * X.generator w y := by
      simp [Cg, Δ, s, E, y, hactive]
    have hle := mul_le_mul_of_nonneg_left hGam hCoeff.1
    have hle2 := mul_le_mul_of_nonneg_right hCoeff.2 hBudget
    rw [hcg, Real.norm_eq_abs, abs_mul, abs_of_nonneg hCoeff.1]
    exact le_trans hle hle2
  · have hz : Cg m i ω = 0 := by simp [Cg, Δ, s, hactive]
    simpa [hz] using mul_nonneg hD0 hBudget
