-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_finitecap_preupcross_source_bounds_force_inclusive_cash_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:35:45.783658+00:00
-- url     : https://prove2.me/submissions/9eee8f65-0d35-4450-8f84-09d13f206483

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_preUpcrossing_stieltjesReward_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u σ : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hBound : ∀ s : ℝ≥0, s ≤ σ → X.X s ω ≤ a - x)
    (q : ℝ) :
    (∫⁻ s in paymentTimes (ruinTime X x (barrierStrategy X x a) ω) ∩ Iic (σ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by
  have hσle : σ ≤ u := by
    have hInf : (σ : ℝ≥0∞) ≤ (u : ℝ≥0∞) := by
      rw [hu]
      refine le_iInf fun s => le_iInf fun hs => ?_
      have hlt : σ < s := by
        by_contra hnot
        have hsσ : s ≤ σ := le_of_not_gt hnot
        exact (not_lt_of_ge (hBound s hsσ)) hs
      exact_mod_cast (le_of_lt hlt)
    exact_mod_cast hInf
  have hBase :=
    barrierStrategy_preUpcrossing_stieltjesReward_zero
      X x a hx hxa ω u hu
      (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s))))
  have hReal : (σ : ℝ) ≤ (u : ℝ) := by exact_mod_cast hσle
  apply le_antisymm
  · calc
      (∫⁻ s in paymentTimes (ruinTime X x (barrierStrategy X x a) ω) ∩ Iic (σ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure (barrierStrategy X x a) ω)) ≤
        (∫⁻ s in Icc (0 : ℝ) (u : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure (barrierStrategy X x a) ω)) := by
          apply lintegral_mono_set
          intro s hs
          exact ⟨hs.1.1, le_trans hs.2 hReal⟩
      _ = 0 := hBase
  · exact bot_le
