-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_all_n_zero_horizon_bounded_clock_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:07:03.764167+00:00
-- url     : https://prove2.me/submissions/27f1b4cd-a578-4c3a-a3be-ca5404a919c6

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
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
    (n : ℕ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hpoint (σ : ℝ≥0∞) :
      paymentTimes σ ∩ Iic (0 : ℝ) = ({0} : Set ℝ) := by
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
  have hpayment (ω : Ω) :
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (0 : ℝ) =
        paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ) :=
    (hpoint _).trans (hpoint _).symm
  have hzero := avram_wave3_04_corrected_ubv_zero_horizon_bound
    X q x w C hw0 hw_cont (hw_smooth.of_le (by norm_num))
    hw_grad D hD hxc hjump
  simpa only [hpayment] using hzero
