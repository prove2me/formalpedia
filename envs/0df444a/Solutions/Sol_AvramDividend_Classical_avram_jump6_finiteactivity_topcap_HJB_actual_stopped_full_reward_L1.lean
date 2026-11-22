-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_finiteactivity_topcap_HJB_actual_stopped_full_reward_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T19:49:31.802088+00:00
-- url     : https://prove2.me/submissions/ae8a7f35-0d5a-4d43-9b09-0da66c7d6b5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_UBV_topcap_HJB_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Infinite-cap source terminal and cash L1 from original HJB growth. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x)
    (k : ℕ) (hk : 0 < k)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCashI : Integrable Cash P)
    (hTop : C = ⊤)
    (hTermMeas : AEStronglyMeasurable Term P) :
    (0 < X.σ) ∧
    Integrable Term P ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | τ ω ≠ 0} := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hFiniteMass : X.ν (Iio (0 : ℝ)) < ⊤ :=
    lt_top_iff_ne_top.mpr hFinite
  have hSigma : 0 < X.σ :=
    avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
      X hBV hFiniteMass
  have hGrad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y := by
    intro y hy hc
    have heq := (hw_hjb y hy hc).2
    have hle : 1 - deriv w y ≤ 0 := by
      calc
        1 - deriv w y ≤
            max (X.generator w y - q * w y) (1 - deriv w y) :=
          le_max_right _ _
        _ = 0 := heq
    linarith
  have hGenerator : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧
          X.generator w y - q * w y ≤ 0 := by
    intro y hy hc
    obtain ⟨hi, heq⟩ := hw_hjb y hy hc
    refine ⟨hi, ?_⟩
    calc
      X.generator w y - q * w y ≤
          max (X.generator w y - q * w y) (1 - deriv w y) :=
        le_max_left _ _
      _ = 0 := heq
  obtain ⟨θ, K, hθ, hK, hGrowth⟩ :=
    avram_f6_original_finiteactivity_UBV_topcap_HJB_exponential_growth
      X hX hBV hFiniteMass q hq w C hC hTop hw0 hw_cont
      hw_neg hw_smooth hGenerator hGrad
  have hGlobalGrowth : ∀ y : ℝ,
      w y ≤ K * Real.exp (θ * y) := by
    intro y
    by_cases hy : 0 ≤ y
    · exact hGrowth y hy
    · have hyneg : y < 0 := lt_of_not_ge hy
      rw [hw_neg y hyneg]
      exact mul_nonneg hK (le_of_lt (Real.exp_pos _))
  have hClockBound : ∀ ω, τ ω ≤ (k : ℝ≥0) :=
    (avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD k hk τ τ hτeq (fun ω => le_refl (τ ω))).1
  have hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω := by
    have hs :=
      avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
        X hBV w C hC hw0 hw_cont hw_neg hw_smooth hGrad
        x hxc D hD q τ W Term hW hTerm
    exact Filter.Eventually.of_forall hs
  have hTermI : Integrable Term P :=
    avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
      X C x D hD τ W Term hτmeas hτstop
      (k : ℝ≥0) hClockBound hW w q θ K hθ hK
      hGlobalGrowth hTerm hTermMeas hTermNonneg
  have hClockEvent : MeasurableSet[𝓕.rightCont 0]
      {ω : Ω | τ ω ≠ 0} :=
    avram_ubv_finite12_positive_clock_initial_measurable τ hτstop
  exact ⟨hSigma, hTermI, hTermI.add hCashI, hClockEvent⟩
