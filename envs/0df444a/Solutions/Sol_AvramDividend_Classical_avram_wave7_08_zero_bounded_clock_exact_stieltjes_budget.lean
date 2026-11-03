-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_zero_bounded_clock_exact_stieltjes_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:53:28.971601+00:00
-- url     : https://prove2.me/submissions/4ad4083b-8dad-4ca0-b390-9066945fd290

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zero_horizon_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hpayment (ω : Ω) :
      paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)) ∩ Iic T =
        paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ) := by
    have hleft :
        paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)) ∩ Iic T =
          ({0} : Set ℝ) := by
      ext t
      constructor
      · intro ht
        change t = 0
        rcases ht.1.2 with heq | hlt
        · exact heq
        · have hmin : min (ruinTime X x D ω) (0 : ℝ≥0∞) = 0 := by simp
          have : ENNReal.ofReal t < (0 : ℝ≥0∞) := by
            simpa only [hmin] using hlt
          have hnot : ¬ ENNReal.ofReal t < (0 : ℝ≥0∞) := by simp
          exact (hnot this).elim
      · intro ht
        have heq : t = 0 := by simpa using ht
        subst t
        simp [paymentTimes, hT]
    have hright :
        paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ) = ({0} : Set ℝ) := by
      ext t
      constructor
      · intro ht
        have hnonneg : 0 ≤ t := ht.1.1
        have hupper : t ≤ 0 := ht.2
        change t = 0
        exact le_antisymm hupper hnonneg
      · intro ht
        have heq : t = 0 := by simpa using ht
        subst t
        simp [paymentTimes]
    exact hleft.trans hright.symm
  have hzero := avram_wave3_04_corrected_ubv_zero_horizon_bound
    X q x w C hw0 hw_cont (hw_smooth.of_le (by norm_num))
    hw_grad D hD hxc hjump
  simpa only [hpayment] using hzero
