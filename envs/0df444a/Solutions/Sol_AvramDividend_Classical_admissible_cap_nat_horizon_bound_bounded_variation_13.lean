-- Prove2me | solution 13 for AvramDividend.Classical.admissible_cap_nat_horizon_bound_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:15:52.270649+00:00
-- url     : https://prove2.me/submissions/7f71c32f-3ce3-4242-98c9-46e4f944bf09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_avram_a19_top_cap_original_full_T_HJB_source
import Theorems.Thm_AvramDividend_Classical_avram_a19_finite_cap_original_full_T_HJB_source
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_clock_real_budget_to_ennreal
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_uniform_closed_cash_budget_implies_all_natural_stopped

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  classical
  obtain ⟨hw_gen, hw_grad, hw_nonneg, hjump⟩ :=
    local_verification_stochastic_core_side_conditions X q w C hw_cont hw0
      ⟨fun hn => (hn hBV).elim, fun _ => hw_smooth⟩ hw_hjb x hxc D hD
  apply avram_limit2_original_uniform_closed_cash_budget_implies_all_natural_stopped
    X q x D (ENNReal.ofReal (w x))
  intro A hA
  let T : ℝ := A + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have hAT : A < T := by dsimp [T]; linarith
  let S : ℝ≥0 := ⟨T, hT.le⟩
  let F : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  have hF : Integrable F P :=
    (avram_p3_bv_original_strict_reward_L1_nonnegative X hBV x C D hD
      w hw_cont hw_neg q hq.le T hT.le hT hw_nonneg).1
  have hBudget : (∫ ω, F ω ∂P) ≤ w x := by
    by_cases hTop : C = ⊤
    · exact avram_a19_top_cap_original_full_T_HJB_source
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
        x hx hxc D hD hw_nonneg hjump T hT.le hT hTop
    · exact avram_a19_finite_cap_original_full_T_HJB_source
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
        x hx hxc D hD hw_nonneg hjump T hT.le hT hTop
  have hCashL1 :=
    avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
      X x C D hD A hA q
  apply avram_wave7_03_original_full_clock_real_budget_to_ennreal
    X x C D hD A hA q (w x)
  refine (integral_mono_ae hCashL1 hF ?_).trans hBudget
  filter_upwards [] with ω
  have hMono :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic A,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    exact lintegral_mono_set (fun t ht => ⟨ht.1, ht.2.trans_lt hAT⟩)
  have hFin := avram_limit2_original_strict_discounted_cash_finite_all_paths
    X q hq.le x D hD.1.1 ω T hT.le
  have hTerm : 0 ≤
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) := by
    split_ifs with hsurv
    · exact mul_nonneg (Real.exp_pos _).le (hw_nonneg ω S hT hsurv)
    · exact le_rfl
  exact (ENNReal.toReal_mono hFin hMono).trans (le_add_of_nonneg_right hTerm)
