-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys60_original_finitecap_uniform_strict_cash_terminal_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:32:03.357944+00:00
-- url     : https://prove2.me/submissions/eba36c3e-ffa2-4dd6-8e86-6b03db916d80

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys44_original_cap_reward_bounded_below_cap
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∃ K : Ω → ℝ, Integrable K P ∧
      ∀ n : ℕ, ∀ ω : Ω, F n ω ≤ K ω := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F
  have hδnonneg (n : ℕ) : 0 ≤ δ n := by
    dsimp [δ]
    positivity
  have hσnonneg (n : ℕ) : 0 ≤ T - δ n := by
    dsimp [δ]
    apply sub_nonneg.mpr
    have hden : 0 < (n : ℝ) + 2 := by positivity
    apply (div_le_iff₀ hden).mpr
    have hm : 0 ≤ T * ((n : ℝ) + 1) :=
      mul_nonneg (le_of_lt hT) (by positivity)
    nlinarith
  let σ : ℕ → Ω → ℝ≥0 := fun n _ => ⟨T - δ n, hσnonneg n⟩
  have hσmeas (n : ℕ) :
      Measurable (fun ω : Ω => (σ n ω : ℝ)) := measurable_const
  have hσbound (n : ℕ) (ω : Ω) : σ n ω ≤ S := by
    apply NNReal.coe_le_coe.mp
    change T - δ n ≤ T
    linarith [hδnonneg n]
  obtain ⟨hCashI, _, hCashBounds⟩ :=
    avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
      X x C D hD q hq S σ hσmeas hσbound
  obtain ⟨R, hR0, hRw⟩ :=
    avram_bvb_phys44_original_cap_reward_bounded_below_cap
      w hw_cont hw_neg C.toReal ENNReal.toReal_nonneg
  have hcap (ω : Ω) :
      riskProcess X x D S ω ≤ C.toReal := by
    have he :=
      admissibleLe_riskProcess_le_cap_all_times
        X x C D hD hxc ω S
    have ht := ENNReal.toReal_mono hFinite he
    have hmax : max (riskProcess X x D S ω) 0 ≤ C.toReal := by
      simpa only [ENNReal.toReal_ofReal'] using ht
    exact (le_max_left _ _).trans hmax
  have hterm (ω : Ω) :
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) ≤ R := by
    split_ifs with hsurv
    · have hw := hRw (riskProcess X x D S ω) (hcap ω)
      have hwle := (le_abs_self (w (riskProcess X x D S ω))).trans hw
      have hexp0 : 0 ≤ Real.exp (-(q * T)) :=
        le_of_lt (Real.exp_pos _)
      have hexp1 : Real.exp (-(q * T)) ≤ 1 := by
        calc
          _ ≤ Real.exp 0 := Real.exp_le_exp.mpr
            (neg_nonpos.mpr (mul_nonneg hq (le_of_lt hT)))
          _ = 1 := by simp
      by_cases hy : 0 ≤ w (riskProcess X x D S ω)
      · nlinarith [mul_nonneg (sub_nonneg.mpr hexp1) hy]
      · have hh := mul_nonpos_of_nonneg_of_nonpos hexp0 (le_of_lt (lt_of_not_ge hy))
        linarith
    · exact hR0
  let K : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal + R
  have hKI : Integrable K P := by
    dsimp [K]
    exact hCashI.add (integrable_const R)
  refine ⟨K, hKI, ?_⟩
  intro n ω
  have hc := (hCashBounds n ω).2
  have hsc : (σ n ω : ℝ) = T - δ n := rfl
  rw [hsc] at hc
  dsimp [F, K]
  exact add_le_add hc (hterm ω)
