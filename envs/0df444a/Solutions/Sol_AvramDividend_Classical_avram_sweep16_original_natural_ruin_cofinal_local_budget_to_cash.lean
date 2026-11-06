-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_natural_ruin_cofinal_local_budget_to_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:20:28.869269+00:00
-- url     : https://prove2.me/submissions/7ac40457-c136-4b02-b0df-a88ace50d63d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_natural_clock_cofinal_stieltjes_cash_eventually_exact
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_natural_ruin_cofinal_local_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ruin_clock_localized_cash_fatou_no_ui
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-! Physical local-stopped cash expectations imply the natural ruin-clock cash
    budget, with no assumed global stopped martingale uniform integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (n : ℕ) (w : ℝ → ℝ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k))
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ ω, (⨆ k : ℕ, S k ω) = ⊤)
    (hBudget : ∀ k : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (w x) := by
  let τ : Ω → ℝ≥0 :=
    fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  let LocalCash : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iic (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
    intro ω
    rfl
  have hMeas : ∀ k, Measurable (LocalCash k) := by
    simpa only [LocalCash] using
      avram_sweep16_original_natural_ruin_cofinal_local_cash_measurable
        X x C D hD q n S hSstop
  have hLocalBudget : ∀ k,
      (∫⁻ ω, LocalCash k ω ∂P) ≤ ENNReal.ofReal (w x) := by
    intro k
    exact hBudget k
  have hLiminf : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      Filter.liminf (fun k : ℕ => LocalCash k ω) Filter.atTop := by
    filter_upwards [] with ω
    obtain ⟨K, hK⟩ :=
      avram_sweep16_original_natural_clock_cofinal_stieltjes_cash_eventually_exact
        X x C D hD q n S hSstop hSmono hSsup ω
    have hEv : (fun k : ℕ => LocalCash k ω) =ᶠ[Filter.atTop]
        (fun _ : ℕ =>
          ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
      filter_upwards [Filter.eventually_ge_atTop K] with k hk
      exact hK k hk
    have hEq :
        Filter.liminf (fun k : ℕ => LocalCash k ω) Filter.atTop =
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
      calc
        _ = Filter.liminf (fun _ : ℕ =>
              ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
                ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
              Filter.atTop := Filter.liminf_congr hEv
        _ = _ := Filter.liminf_const _
    exact le_of_eq hEq.symm
  exact avram_sweep16_original_ruin_clock_localized_cash_fatou_no_ui
    X q x w D n τ hτeq LocalCash hMeas hLocalBudget hLiminf
