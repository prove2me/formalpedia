-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_natural_clock_cofinal_stieltjes_cash_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:59:36.893798+00:00
-- url     : https://prove2.me/submissions/ccd61078-9d34-47b4-a8a7-650883b801a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (n : ℕ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k))
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ ω, (⨆ k : ℕ, S k ω) = ⊤) :
    ∀ ω, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  intro ω
  have hlt : (n : ℝ≥0∞) < (⨆ k : ℕ, S k ω) := by
    rw [hSsup ω]
    simp
  obtain ⟨K, hK⟩ := lt_iSup_iff.mp hlt
  refine ⟨K, ?_⟩
  intro k hk
  have hτle : min (ruinTime X x D ω) (n : ℝ≥0∞) ≤ S k ω :=
    (min_le_right _ _).trans ((le_of_lt hK).trans (hSmono ω hk))
  rw [min_eq_left hτle]
