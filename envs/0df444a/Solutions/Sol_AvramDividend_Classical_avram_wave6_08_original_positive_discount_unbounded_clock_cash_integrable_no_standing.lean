-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_discount_unbounded_clock_cash_integrable_no_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:56:25.994324+00:00
-- url     : https://prove2.me/submissions/7c43f361-5c11-404d-9673-04d1068b00b7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_cash_integrable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (τ : Ω → ℝ≥0)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) P := by
  have hcont : ContinuousWithinAt X.ψ (Ioi (0 : ℝ)) 0 :=
    ((levy_laplace_exponent_continuousOn_nonnegative X) 0
      (show (0 : ℝ) ∈ Ici 0 by simp)).mono (by
        intro y hy
        exact le_of_lt (Set.mem_Ioi.mp hy))
  have hnhds : (Iio q : Set ℝ) ∈ 𝓝 (X.ψ 0) := by
    rw [levy_laplace_exponent_zero X]
    exact IsOpen.mem_nhds isOpen_Iio hq
  have hEv : ∀ᶠ θ in 𝓝[Ioi (0 : ℝ)] (0 : ℝ), X.ψ θ < q :=
    hcont.tendsto.eventually hnhds
  have hEvPos : ∀ᶠ θ in 𝓝[Ioi (0 : ℝ)] (0 : ℝ), 0 < θ :=
    self_mem_nhdsWithin
  obtain ⟨θ, hθψ, hθpos⟩ := (hEv.and hEvPos).exists
  exact avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_cash_integrable
    X x C D hD θ hθpos q (le_of_lt hθψ) τ hτmeas
