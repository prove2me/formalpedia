-- Prove2me | solution 14 for AvramDividend.Classical.admissible_cap_truncated_ubv_stochastic_core_corrected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T06:48:28.039821+00:00
-- url     : https://prove2.me/submissions/b009c10a-d294-4cd3-b402-50226896aeba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bvb38_original_finitecap_C1_slope_candidate_affine_reserve_floor
import Theorems.Thm_AvramDividend_Classical_avram_original_gaussian_only_topcap_true_stopped_single_centered_source
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_five_witness_gaussian_plus_jump
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_purejump_original_expected_reward_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_single_centered_source_nat_horizon_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_zeroCap_or_zeroHorizon
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_positive_clock_horizon_cash_le_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_admissible_initial_reserve_either_clock_ubv_value
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_gaussian_finitecap_diagonal_cash_bound_of_discount_boundary_lt_drift
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

-- The clock reduction and the nonzero-jump cases adapt the published sketches
-- https://prove2.me/submissions/b0fc73c1-6a62-4718-80c9-b83a302c5ede
-- https://prove2.me/submissions/65066d68-41c5-48a6-8ffd-f19156345a20

private theorem positiveClockCashBudget
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
  have hAdmissibleTop : IsAdmissibleLe X x ⊤ D :=
    ⟨hD.1, fun _ _ _ => le_top⟩
  have gaussianTopCash (v : ℝ → ℝ) (hν : X.ν = 0)
      (hv0 : 0 ≤ v 0) (hvCont : ContinuousOn v (Ici 0))
      (hvNeg : ∀ y < 0, v y = 0)
      (hvSmooth : ContDiffOn ℝ 2 v {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ⊤})
      (hvGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ⊤ →
        X.GeneratorIntegrable v y ∧ X.generator v y - q * v y ≤ 0)
      (hvGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ⊤ → 1 ≤ deriv v y)
      (hvNonneg : ∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ v (riskProcess X x D t ω))
      (hvJump : ∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          v (riskProcess X x D t ω) -
            v (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) :
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (v x) := by
    have hTop : (0 : ℝ≥0∞) < ⊤ := by simp
    have hxTop : ENNReal.ofReal x ≤ ⊤ := le_top
    obtain ⟨W, Cash, Term, hW, hCash, hTerm, hTermMeas, hCashI⟩ :=
      avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
        X x ⊤ D hAdmissibleTop v hvCont hvNeg q n τ hτ hτmeas hτstop
    obtain ⟨M, hMI, hM0, hBound⟩ :=
      avram_original_gaussian_only_topcap_true_stopped_single_centered_source
        X hX hBV hν q hq v ⊤ hTop rfl hv0 hvCont hvNeg hvSmooth hvGen hvGrad
        x hx hxTop D hAdmissibleTop hvNonneg hvJump n hn τ hτ hτmeas hτstop
        W Cash Term hW hCash hTerm hTermMeas hCashI
    exact avram_ubv_hor3_original_single_centered_source_nat_horizon_cash_budget
      X hBV q hq v ⊤ hTop hv0 hvCont hvNeg hvSmooth hvGen hvGrad
      x hx hxTop D hAdmissibleTop n hn T τ hτ hτmeas hτstop W Cash Term M (fun _ => 0)
      hW hCash hTerm hTermMeas hMI hM0 (Filter.Eventually.of_forall fun _ => le_rfl)
      (by simpa only [add_zero] using hBound)
  by_cases hν : X.ν = 0
  · by_cases hTop : C = ⊤
    · subst C
      exact gaussianTopCash w hν hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad hw_nonneg hjump
    · by_cases hAffine : X.c ≤ q * w 0
      · let v : ℝ → ℝ := fun y => if y < 0 then 0 else w 0 + y
        have v_of_nonneg (y : ℝ) (hy : 0 ≤ y) : v y = w 0 + y := by
          simp [v, not_lt_of_ge hy]
        have hv0 : 0 ≤ v 0 := by simpa [v] using hw0
        have hvNeg (y : ℝ) (hy : y < 0) : v y = 0 := by simp [v, hy]
        have hAffineCont : Continuous (fun y : ℝ => w 0 + y) :=
          continuous_const.add continuous_id
        have hvCont : ContinuousOn v (Ici 0) :=
          hAffineCont.continuousOn.congr fun y hy =>
            v_of_nonneg y (Set.mem_Ici.mp hy)
        have hLinear : ContDiff ℝ 2 (fun y : ℝ => w 0 + y) :=
          contDiff_const.add contDiff_id
        have hvSmooth : ContDiffOn ℝ 2 v {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ⊤} :=
          hLinear.contDiffOn.congr fun y hy => v_of_nonneg y hy.1.le
        have hvLocal (y : ℝ) (hy : 0 < y) :
            v =ᶠ[𝓝 y] fun z : ℝ => w 0 + z := by
          filter_upwards [Ioi_mem_nhds hy] with z hz
          exact v_of_nonneg z (Set.mem_Ioi.mp hz).le
        have hvDeriv (y : ℝ) (hy : 0 < y) : deriv v y = 1 := by
          rw [(hvLocal y hy).deriv_eq]
          exact deriv_const_add_id (w 0)
        have hvSecond (y : ℝ) (hy : 0 < y) : iteratedDeriv 2 v y = 0 := by
          calc
            iteratedDeriv 2 v y = iteratedDeriv 2 (fun z : ℝ => w 0 + z) y :=
              (hvLocal y hy).iteratedDeriv_eq 2
            _ = iteratedDeriv 2 id y :=
              iteratedDeriv_const_add (f := id) (by decide : 0 < (2 : ℕ)) (w 0)
            _ = 0 := by simp [iteratedDeriv_id]
        have hvGen (y : ℝ) (hy : 0 < y) (_ : ENNReal.ofReal y < ⊤) :
            X.GeneratorIntegrable v y ∧ X.generator v y - q * v y ≤ 0 := by
          constructor
          · simpa [SpectrallyNegativeLevy.GeneratorIntegrable, hν, IntegrableOn] using
              (integrable_zero_measure (f := SpectrallyNegativeLevy.generatorIntegrand v y))
          · simp [SpectrallyNegativeLevy.generator, hν, hvSecond y hy,
              hvDeriv y hy, v_of_nonneg y hy.le]
            have hqy : 0 ≤ q * y := mul_nonneg hq.le hy.le
            nlinarith only [hAffine, hqy]
        have hvNonneg (ω : Ω) (t : ℝ≥0) (_ : 0 < t)
            (_ : (t : ℝ≥0∞) < ruinTime X x D ω) :
            0 ≤ v (riskProcess X x D t ω) := by
          by_cases hr : 0 ≤ riskProcess X x D t ω
          · rw [v_of_nonneg _ hr]
            exact add_nonneg hw0 hr
          · exact le_of_eq (hvNeg _ (lt_of_not_ge hr)).symm
        have hvJump (ω : Ω) (t : ℝ≥0)
            (ha : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
            rightLimit D t ω - D t ω ≤
              v (riskProcess X x D t ω) -
                v (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) := by
          have hPaid := hD.1.2 ω t ha
          have hPaidNN : 0 ≤ rightLimit D t ω - D t ω :=
            sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD.1.1 ω t)
          rw [v_of_nonneg _ (hPaidNN.trans hPaid),
            v_of_nonneg _ (sub_nonneg.mpr hPaid)]
          linarith
        have hxReal : x ≤ C.toReal := by
          rw [← ENNReal.toReal_ofReal hx.le]
          exact ENNReal.toReal_mono hTop hxc
        have hC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
          hw_smooth.of_le (by norm_num)
        have hVle : v x ≤ w x := by
          rw [v_of_nonneg x hx.le]
          exact avram_bvb38_original_finitecap_C1_slope_candidate_affine_reserve_floor
            C hC hTop w hw_cont hC1 hw_grad x hx.le hxReal
        exact (gaussianTopCash v hν hv0 hvCont hvNeg hvSmooth hvGen
          (fun y hy _ => (hvDeriv y hy).ge) hvNonneg hvJump).trans
            (ENNReal.ofReal_le_ofReal hVle)
      · exact (avram_wave7_08_positive_clock_horizon_cash_le_clock X q x D n hn T).trans
          (gaussian_finitecap_diagonal_cash_bound_of_discount_boundary_lt_drift
            X hX hBV hν q hq w C hC hTop hw0 (lt_of_not_ge hAffine)
            hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc
            D hD hw_nonneg hjump n hn)
  · obtain ⟨W, Cash, Term, hW, hCash, hTerm, hTermMeas, hCashI⟩ :=
      avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
        X x C D hD w hw_cont hw_neg q n τ hτ hτmeas hτstop
    have centered : ∃ M : Ω → ℝ, Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
        ∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω := by
      by_cases hσ : X.σ = 0
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

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  by_cases hz : T = 0
  · exact avram_wave5_05_corrected_ubv_zeroCap_or_zeroHorizon
      X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hxc D hD hw_nonneg hjump T hT (Or.inr hz)
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hz)
    apply avram_wave7_11_admissible_initial_reserve_either_clock_ubv_value
      X hBV q w C hw0 x hxc D hD T hT
    intro hx
    left
    obtain ⟨n, hnT⟩ := exists_nat_gt T
    refine ⟨n, hnT, ?_⟩
    have hn : 0 < n := by
      exact_mod_cast (lt_of_le_of_lt hT hnT)
    have hC : 0 < C :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hx) hxc
    exact positiveClockCashBudget
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hTpos n hn
