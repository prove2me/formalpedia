-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_instantRuin_allHorizon_correctedStieltjesBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:04:46.371354+00:00
-- url     : https://prove2.me/submissions/d5a8379d-8aff-47ef-a1b7-df55538f0812

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zero_horizon_bound
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every almost-surely instantly ruined capped controlled Lévy policy
satisfies the full original Stieltjes verification at all horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hRuin : ∀ᵐ ω ∂P, ruinTime X x D ω = 0)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hzero := avram_wave3_04_corrected_ubv_zero_horizon_bound
    X q x w C hw0 hw_cont hw_smooth hw_grad D hD hxc hjump
  have hSet : paymentTimes (0 : ℝ≥0∞) = ({0} : Set ℝ) := by
    simpa using (paymentTimes_min_zero_eq_singleton_zero (0 : ℝ≥0∞))
  have heq : (fun ω => ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =ᵐ[P]
    (fun ω => ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    filter_upwards [hRuin] with ω hr
    have hSets : paymentTimes (ruinTime X x D ω) ∩ Iic T =
        paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ) := by
      rw [hr, hSet]
      ext t
      simp only [mem_inter_iff, mem_singleton_iff, mem_Iic]
      constructor
      · intro ht
        rcases ht with ⟨rfl, _⟩
        exact ⟨rfl, le_refl 0⟩
      · intro ht
        rcases ht with ⟨rfl, _⟩
        exact ⟨rfl, hT⟩
    rw [hSets]
  calc
    _ = (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) :=
      lintegral_congr_ae heq
    _ ≤ ENNReal.ofReal (w x) := hzero
