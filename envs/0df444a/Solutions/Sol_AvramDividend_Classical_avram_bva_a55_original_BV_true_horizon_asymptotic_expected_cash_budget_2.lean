-- Prove2me | solution 2 for AvramDividend.Classical.avram_bva_a55_original_BV_true_horizon_asymptotic_expected_cash_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:01:03.710959+00:00
-- url     : https://prove2.me/submissions/62befe4d-dd73-4084-a8e3-1cc82f57297f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a62_original_BV_strict_prehorizon_ruinclipped_expected_physical_supermartingale_budget
import Theorems.Thm_AvramDividend_Classical_avram_bva_a63_original_BV_strict_prehorizon_terminal_Fatou_liminf_and_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_C1_closed_cap_payoff_above_reserve
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici
    0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y →
    ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0),
    (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (T : ℝ) (hT : 0 < T) (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal + (if (S : ℝ≥0∞) < ruinTime X x D ω then Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in (atTop : Filter ℕ), (∫ ω, F m ω ∂P) ≤ w x + ε := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F ε hε
  let r : ℕ → ℝ≥0 := fun n => Real.toNNReal (T - δ n)
  let G : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal
    ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (r n : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (r n : ℝ))) * w (riskProcess X x D (r n) ω) else 0))
  have hI := avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD hw_nonneg hjump T hT hInfinite
  have hA63 := avram_bva_a63_original_BV_strict_prehorizon_terminal_Fatou_liminf_and_measurable
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD hw_nonneg hjump T hT hInfinite
  change (∀ n, Measurable (G n)) ∧
      ∀ n, ∀ᵐ ω ∂P, ENNReal.ofReal (F n ω) ≤
        liminf (fun m : ℕ => G m ω) atTop at hA63
  obtain ⟨hGMeas, hDom⟩ := hA63
  have hWx : 0 ≤ w x := le_trans hx
    (avram_limit2_bv_C1_closed_cap_payoff_above_reserve
      C hC w hw0 hw_cont hw_smooth hw_grad x hx hxc)
  have hSpos : (0 : ℝ≥0) < S := by exact_mod_cast hT
  have hFnNonneg (n : ℕ) : 0 ≤ᵐ[P] F n := by
    filter_upwards [] with ω
    change 0 ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    apply add_nonneg ENNReal.toReal_nonneg
    split_ifs with hs
    · exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (hw_nonneg ω S hSpos hs)
    · exact le_refl 0
  have hrpos (m : ℕ) : 0 < r m := by
    change 0 < Real.toNNReal (T - T / ((m : ℝ) + 2))
    rw [Real.toNNReal_pos]
    have hd : 0 < ((m : ℝ) + 2) := by positivity
    have hm : (1 : ℝ) < ((m : ℝ) + 2) := by
      have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact sub_pos.mpr (div_lt_self hT hm)
  have hrlt (m : ℕ) : (r m : ℝ) < T := by
    have hpos : 0 < T - δ m := Real.toNNReal_pos.mp (hrpos m)
    change (Real.toNNReal (T - δ m) : ℝ) < T
    rw [Real.coe_toNNReal _ (le_of_lt hpos)]
    have hd : 0 < ((m : ℝ) + 2) := by positivity
    have hdv : 0 < T / ((m : ℝ) + 2) := div_pos hT hd
    dsimp [δ]
    linarith
  have hGMean (m : ℕ) : (∫⁻ ω, G m ω ∂P) ≤ ENNReal.ofReal (w x) := by
    simpa only [G] using
      (avram_bva_a62_original_BV_strict_prehorizon_ruinclipped_expected_physical_supermartingale_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
        x hx hxc D hD hw_nonneg hjump T hT hInfinite (r m) (hrpos m) (hrlt m))
  have hEnnMean (n : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) ≤ ENNReal.ofReal (w x) := by
    calc
      _ ≤ (∫⁻ ω, liminf (fun m : ℕ => G m ω) atTop ∂P) :=
        lintegral_mono_ae (hDom n)
      _ ≤ liminf (fun m : ℕ => ∫⁻ ω, G m ω ∂P) atTop :=
        lintegral_liminf_le hGMeas
      _ ≤ ENNReal.ofReal (w x) := by
        apply Filter.liminf_le_of_le
        · exact ⟨0, Filter.Eventually.of_forall
            (fun y : ℝ≥0∞ => bot_le)⟩
        · intro b hb
          obtain ⟨m, hm⟩ := hb.exists
          exact hm.trans (hGMean m)
  have hMean (n : ℕ) : (∫ ω, F n ω ∂P) ≤ w x := by
    have hRewrite := integral_eq_lintegral_of_nonneg_ae
      (hFnNonneg n) (hI n).aestronglyMeasurable
    rw [hRewrite]
    have hB := ENNReal.toReal_mono
      (by simp : ENNReal.ofReal (w x) ≠ ⊤) (hEnnMean n)
    simpa only [ENNReal.toReal_ofReal hWx] using hB
  filter_upwards [] with n
  linarith [hMean n]
