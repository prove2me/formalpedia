-- Prove2me | solution 9 for AvramDividend.Classical.avram_wave7_08_ubv_positive_n_positive_horizon_source_ito_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T06:11:03.363834+00:00
-- url     : https://prove2.me/submissions/65066d68-41c5-48a6-8ffd-f19156345a20
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_original_gaussian_only_topcap_true_stopped_single_centered_source
import Theorems.Thm_AvramDividend_Classical_avram_original_gaussian_only_finitecap_true_stopped_single_centered_source
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_purejump_original_expected_reward_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_five_witness_gaussian_plus_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_single_centered_source_nat_horizon_cash_budget
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

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
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨τ, hτ, hτmeas, hτstop⟩ :=
    avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping X x D n
      (ruinTime_measurable X x D hD.1.1)
      (ruinTime_stopping_rightCont_filtration X x D hD.1.1)
  obtain ⟨W, Cash, Term, hW, hCash, hTerm, hTermMeas, hCashI⟩ :=
    avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
      X x C D hD w hw_cont hw_neg q n τ hτ hτmeas hτstop

  have centered : ∃ M : Ω → ℝ, Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      ∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω := by
    by_cases hν : X.ν = 0
    · by_cases hTop : C = ⊤
      · exact avram_original_gaussian_only_topcap_true_stopped_single_centered_source
          X hX hBV hν q hq w C hC hTop hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
          x hx hxc D hD hw_nonneg hjump n hn τ hτ hτmeas hτstop
          W Cash Term hW hCash hTerm hTermMeas hCashI
      · exact avram_original_gaussian_only_finitecap_true_stopped_single_centered_source
          X hX hBV hν q hq w C hC hTop hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
          x hx hxc D hD hw_nonneg hjump n hn τ hτ hτmeas hτstop
          W Cash Term hW hCash hTerm hTermMeas hCashI
    · by_cases hσ : X.σ = 0
      · obtain ⟨hPayoffI, hMean⟩ :=
          avram_p4_f4_purejump_original_expected_reward_budget
            X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
            x hx hxc D hD hw_nonneg hjump n hn τ hτ hτmeas hτstop
            W Cash Term hW hCash hTerm hTermMeas hCashI
        let m : ℝ := ∫ ω, Term ω + Cash ω ∂P
        have hm : m ≤ w x := hMean
        have hConst : Integrable (fun _ : Ω => m) P := integrable_const m
        refine ⟨fun ω => Term ω + Cash ω - m, hPayoffI.sub hConst, ?_, ?_⟩
        · rw [integral_sub hPayoffI hConst]
          simp [integral_const, m]
        · apply Filter.Eventually.of_forall
          intro ω
          change Term ω + Cash ω ≤ w x + (Term ω + Cash ω - m)
          linarith only [hm]
      · obtain ⟨Mc, Ms, Ml, G, R, hIc, hIs, hIl, _, hc, hs, hl, hG, hR, hUpper⟩ :=
          avram_p4_f4_original_five_witness_gaussian_plus_jump
            X hX hBV hσ hν q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
            x hx hxc D hD hw_nonneg hjump n hn τ hτ hτmeas hτstop
            W Cash Term hW hCash hTerm hTermMeas hCashI
        refine ⟨fun ω => Mc ω + Ms ω + Ml ω, (hIc.add hIs).add hIl, ?_, ?_⟩
        · calc
            (∫ ω, Mc ω + Ms ω + Ml ω ∂P) =
                (∫ ω, Mc ω + Ms ω ∂P) + (∫ ω, Ml ω ∂P) :=
              integral_add (hIc.add hIs) hIl
            _ = 0 := by simp only [integral_add hIc hIs, hc, hs, hl, add_zero]
        · filter_upwards [hG, hR, hUpper] with ω hg hr hu
          change Term ω + Cash ω ≤ w x + (Mc ω + Ms ω + Ml ω)
          linarith only [hu, hg, hr]

  obtain ⟨M, hMI, hM0, hBound⟩ := centered
  exact avram_ubv_hor3_original_single_centered_source_nat_horizon_cash_budget
    X hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD n hn T τ hτ hτmeas hτstop W Cash Term M (fun _ => 0)
    hW hCash hTerm hTermMeas hMI hM0 (Filter.Eventually.of_forall fun _ => le_rfl)
    (by simpa only [add_zero] using hBound)
