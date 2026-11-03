-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_ruin_discounted_strict_interior_mass_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:20:42.221287+00:00
-- url     : https://prove2.me/submissions/7b215132-25cc-4aee-a4d5-dca1a839035f

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_strict_interior_mass_vanish

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Discounted original full Stieltjes mass on the shrinking strictly
pre-ruin final cell vanishes without counting the ruin-time right payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (τ : ℝ≥0) (hτ : 0 < τ)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < τ)
    (hlim : Tendsto u atTop (𝓝 τ)) :
    Tendsto (fun n => ∫⁻ t in Ioo (u n : ℝ) (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (𝓝 0) := by
  let μ : Measure ℝ := dividendMeasure D ω
  have hmass :
      Tendsto (fun n => μ (Ioo (u n : ℝ) (τ : ℝ))) atTop (𝓝 0) :=
    avram_wave6_08_original_positive_ruin_strict_interior_mass_vanish
      D hD ω τ hτ u hu hlim
  have hbound (n : ℕ) :
      (∫⁻ t in Ioo (u n : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
          μ (Ioo (u n : ℝ) (τ : ℝ)) := by
    have hae : ∀ᵐ t ∂μ.restrict (Ioo (u n : ℝ) (τ : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ≤ (1 : ℝ≥0∞) := by
      refine (ae_restrict_mem measurableSet_Ioo).mono ?_
      intro t ht
      have h0 : (0 : ℝ) ≤ t :=
        le_trans (NNReal.coe_nonneg (u n)) (le_of_lt ht.1)
      have hqt : 0 ≤ q * t := mul_nonneg hq h0
      have hexp : Real.exp (-(q * t)) ≤ 1 := by
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqt)
      simpa using (ENNReal.ofReal_le_ofReal hexp)
    calc
      (∫⁻ t in Ioo (u n : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
          ∫⁻ t in Ioo (u n : ℝ) (τ : ℝ), (1 : ℝ≥0∞) ∂μ :=
            lintegral_mono_ae hae
      _ = μ (Ioo (u n : ℝ) (τ : ℝ)) := by simp
  have hnonneg (n : ℕ) :
      (0 : ℝ≥0∞) ≤ (∫⁻ t in Ioo (u n : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) := bot_le
  change Tendsto (fun n => ∫⁻ t in Ioo (u n : ℝ) (τ : ℝ),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) atTop (𝓝 0)
  exact Filter.Tendsto.squeeze tendsto_const_nhds hmass hnonneg hbound
