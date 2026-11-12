-- Prove2me | solution 2 for AvramDividend.Classical.avram_gledger39_original_bounded_stop_discount_mesh_error_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:25:23.567202+00:00
-- url     : https://prove2.me/submissions/2f7ad072-0143-481b-bf4b-3e27c1fb20a8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger42_original_strict_discounted_cash_mesh_error_L1
import Theorems.Thm_AvramDividend_Classical_avram_gledger98_original_random_strict_open_mass_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger104_original_nnreal_clipped_final_strict_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger107_original_ruinclipped_mesh_error_pointwise_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger108_nonnegative_shifted_domination_L1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The clipped original strict contact error is dominated by the proved real-mesh L1 error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let u : ℝ≥0 := ρ ω - Δ
      q * (Δ : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (E m) P ∧ (∫ ω, E m ω ∂P) ≤ ε := by
  let δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let M : Ω → ℝ := fun ω => (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal
  let F : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Tc : ℕ → Ω → ℝ := fun m ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ ω - δ m : ℝ≥0) : ℝ) (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Tr : ℕ → Ω → ℝ := fun m ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ ω : ℝ) - (n : ℝ) / ((m : ℝ) + 2)) (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let E : ℕ → Ω → ℝ := fun m ω => q * (δ m : ℝ) * M ω + Tc m ω
  let B : ℕ → Ω → ℝ := fun m ω => q * ((n : ℝ) / ((m : ℝ) + 2)) * Real.exp (q * (n : ℝ)) * F ω + Tr m ω
  change ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
    Integrable (E m) P ∧ (∫ ω, E m ω ∂P) ≤ ε
  have hρMeas : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hMMeas : Measurable M := (avram_gledger98_original_random_strict_open_mass_measurable
    D hD.1.1 ρ hρMeas).ennreal_toReal
  have hδR (m : ℕ) : (δ (m + 1) : ℝ) = (n : ℝ) / ((m : ℝ) + 2) := by
    simp only [δ, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast]
    push_cast
    ring
  have hpoint (m : ℕ) (ω : Ω) : E (m + 1) ω ≤ B m ω := by
    have hp := avram_gledger107_original_ruinclipped_mesh_error_pointwise_bound
      X x D hD.1.1 ω q (le_of_lt hq) (n : ℝ≥0) (ρ ω) (δ (m + 1))
      (hρbound ω) (hρruin ω)
    simpa only [E, B, M, F, Tc, Tr, hδR m, NNReal.coe_natCast] using hp
  have hEmeas (m : ℕ) : Measurable (E (m + 1)) := by
    have ht := avram_gledger104_original_nnreal_clipped_final_strict_cash_measurable
      X x D hD.1.1 q ρ hρMeas (δ (m + 1))
    exact (hMMeas.const_mul _).add ht.ennreal_toReal
  have hEnonneg (m : ℕ) (ω : Ω) : 0 ≤ E m ω := by
    dsimp [E, M, Tc]
    positivity
  have hBnonneg (m : ℕ) (ω : Ω) : 0 ≤ B m ω := by
    dsimp [B, F, Tr]
    positivity
  have h42 := avram_gledger42_original_strict_discounted_cash_mesh_error_L1 X hX x C D hD q hq n hn ρ hρstop hρbound
  change ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
    Integrable (B m) P ∧ (∫ ω, B m ω ∂P) ≤ ε at h42
  exact avram_gledger108_nonnegative_shifted_domination_L1
    E B h42 hEmeas (fun m ω => hEnonneg (m + 1) ω) hBnonneg hpoint
