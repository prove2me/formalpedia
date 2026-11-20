-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_actual_discounted_cash_rightmesh_tends_to_subclock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:56:15.106545+00:00
-- url     : https://prove2.me/submissions/2cf89316-17c6-4661-a84b-082599aaed88

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_weighted_inclusive_cash_rightclock_limit
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_delayed_clock_real_min_tends_to_stopped
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω)
    (σ τ : ℝ≥0) (hστ : σ ≤ τ) :
    Tendsto (fun m : ℕ =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iic ((min τ (σ + (1 : ℝ≥0) /
            ((m : ℝ≥0) + 1)) : ℝ≥0) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) atTop
      (𝓝 ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal)) := by
  let a : ℕ → ℝ := fun m =>
    (min τ (σ + (1 : ℝ≥0) / ((m : ℝ≥0) + 1)) : ℝ)
  let A : Set ℝ := paymentTimes (ruinTime X x D ω)
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  have hf : Measurable f := by fun_prop
  have hA : MeasurableSet A :=
    avram_p4_d_dividend_original_paymentTimes_measurableSet _
  have ha : Antitone a := by
    intro i j hij
    dsimp [a]
    gcongr
  have hl : Tendsto a atTop (𝓝 (σ : ℝ)) := by
    simpa only [a, NNReal.coe_min, NNReal.coe_add, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_natCast] using
      avram_f6_original_delayed_clock_real_min_tends_to_stopped σ τ hστ
  have hfull : (∫⁻ t in A ∩ Iic (τ : ℝ),
      f t ∂(dividendMeasure D ω)) ≠ ∞ := by
    dsimp [A, f]
    rw [avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
      X x D hD ω τ q hq]
    exact ENNReal.ofReal_ne_top
  have hset : A ∩ Iic (a 0) ⊆ A ∩ Iic (τ : ℝ) := by
    intro t ht
    refine ⟨ht.1, Set.mem_Iic.mpr (le_trans (Set.mem_Iic.mp ht.2) ?_)⟩
    dsimp only [a]
    exact min_le_left _ _
  have hfinite : ∃ i, (∫⁻ t in A ∩ Iic (a i),
      f t ∂(dividendMeasure D ω)) ≠ ∞ := by
    refine ⟨0, ne_top_of_le_ne_top hfull ?_⟩
    exact lintegral_mono_set hset
  change Tendsto (fun m => (∫⁻ t in A ∩ Iic (a m),
    f t ∂(dividendMeasure D ω)).toReal) atTop
    (𝓝 ((∫⁻ t in A ∩ Iic (σ : ℝ),
      f t ∂(dividendMeasure D ω)).toReal))
  exact (avram_f6_original_weighted_inclusive_cash_rightclock_limit
      (dividendMeasure D ω) f hf A hA a (σ : ℝ) ha hl hfinite)
