-- Prove2me | solution 6 for AvramDividend.Classical.avram_wave7_08_ubv_positive_n_positive_horizon_source_ito_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:30:03.61489+00:00
-- url     : https://prove2.me/submissions/4af15a46-b920-47fc-9e97-09ec5a8f7996
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_original_natural_terminal_integrable_HJB_mean_upper
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_truncated_cash_le_actual_stopped_clock
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- Direct positive-n,T cash bound from the exact stopped expected
payoff, retaining all physical endpoints and the postpayment W. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  haveI : IsProbabilityMeasure P := X.isProbability
  have hDS : IsDividendStrategy 𝓕 D := hD.1.1
  have hRuinMeas : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hDS
  have hRuinStop : IsStoppingTime 𝓕.rightCont (ruinTime X x D) :=
    ruinTime_stopping_rightCont_filtration X x D hDS
  obtain ⟨τ, hτeq, hτmeas, hτstop⟩ :=
    avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
      X x D n hRuinMeas hRuinStop
  obtain ⟨W, Cash, Term, hW, hCash, hTerm, hTermMeas, hCashI⟩ :=
    avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
      X x C D hD w hw_cont hw_neg q n τ hτeq hτmeas hτstop
  obtain ⟨hTermI, hMean⟩ :=
    avram_p4_f7_original_natural_terminal_integrable_HJB_mean_upper
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI
  let A : Ω → ℝ := fun ω => Term ω + Cash ω
  let avg : ℝ := ∫ ω, A ω ∂P
  let M : Ω → ℝ := fun ω => A ω - avg
  let G : Ω → ℝ := fun _ => avg - w x
  let H : Ω → ℝ := fun _ => 0
  have hAI : Integrable A P := hTermI.add hCashI
  have hMI : Integrable M P := hAI.sub (integrable_const avg)
  have hGI : Integrable G P := integrable_const _
  have hHI : Integrable H P := integrable_const _
  have hMzero : (∫ ω, M ω ∂P) = 0 := by
    change (∫ ω, A ω - avg ∂P) = 0
    rw [integral_sub hAI (integrable_const avg)]
    simp [avg]
  have hAvg : avg ≤ w x := by simpa [avg, A] using hMean
  have hSign : ∀ᵐ ω ∂P, G ω + H ω ≤ 0 := by
    filter_upwards with ω
    dsimp [G, H]
    linarith
  have hUpper : ∀ᵐ ω ∂P, Term ω + Cash ω ≤
      w x + M ω + G ω + H ω := by
    filter_upwards with ω
    dsimp [M, G, H, A]
    apply le_of_eq
    ring
  have hActual :=
    avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
      X hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD n hn τ hτeq hτmeas hτstop
      W Cash Term M G H hW hCash hTerm hTermMeas
      hMI hGI hHI hMzero hSign hUpper
  exact (avram_wave7_08_truncated_cash_le_actual_stopped_clock
    X q x D n hn T).trans hActual
