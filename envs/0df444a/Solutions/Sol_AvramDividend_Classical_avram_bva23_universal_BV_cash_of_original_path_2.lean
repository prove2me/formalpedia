-- Prove2me | solution 2 for AvramDividend.Classical.avram_bva23_universal_BV_cash_of_original_path
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:15:40.614097+00:00
-- url     : https://prove2.me/submissions/61fbd472-fd41-45f9-9111-02434976c60d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_BV_every_inner_horizon_expected_cash_terminal_le
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_signed_closed_budget_of_strict_prebudget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Independent inner-horizon route to closed cash, retaining the original source premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hEnvelope : ¬ (x + T * X.drift ≤ w x))
    (hSource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ((t : ℝ) * X.drift - X.X t ω) -
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0) = 0) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤ w x := by
  have hTpos : 0 < T := (avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
    X hX hBV q hq w C hC hw_cont hw0 hw_smooth hw_grad x hx hxc D hD T hT hEnvelope).1
  let S : ℝ≥0 := ⟨T, le_of_lt hTpos⟩
  let u : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 2)
  have hmono : Monotone u := by intro a b hab; dsimp [u]; gcongr
  have hu (n : ℕ) : 0 ≤ u n := by
    dsimp [u]
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_nonneg (le_of_lt hTpos) (show 0 ≤ (n : ℝ) + 1 by positivity)]
  have hbelow (n : ℕ) : u n ≤ (S : ℝ) := by
    change T - T / ((n : ℝ) + 2) ≤ T
    exact sub_le_self _ (div_nonneg (le_of_lt hTpos) (by positivity))
  have hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n := by
    intro s hs
    have hgap : 0 < T - s := by change s < T at hs; linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (T / (T - s))
    have hnreal : T / (T - s) < (n : ℝ) := by exact_mod_cast hn
    have hfirst : T < (n : ℝ) * (T - s) := (div_lt_iff₀ hgap).1 hnreal
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hsecond : T / ((n : ℝ) + 2) < T - s := (div_lt_iff₀ hden).2 (by nlinarith)
    refine ⟨n, ?_⟩; dsimp [u]; linarith
  have hInner := avram_bvb_original_BV_every_inner_horizon_expected_cash_terminal_le
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hTpos
  have hMesh (n : ℕ) : (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω) else 0) ∂P) ≤ w x := by
    exact hInner n
  have hStrict : (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω) else 0) ∂P) ≤ w x :=
    avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) S u hmono hu hbelow hcover (w x) hMesh
  let Term : Ω → ℝ := fun ω => if (S : ℝ≥0∞) < ruinTime X x D ω then Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) else 0
  have hTermNonneg : (0 : ℝ) ≤ ∫ ω, Term ω ∂P := by
    apply integral_nonneg; intro ω; dsimp [Term]
    split_ifs with hruin
    · exact mul_nonneg (Real.exp_pos _).le
        (avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
          X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hx hxc D hD ω S)
    · exact le_rfl
  have hSigned : (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal ∂P) + (∫ ω, Term ω ∂P) ≤ w x := by
    exact avram_p3_bv_original_signed_closed_budget_of_strict_prebudget
        X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hx hxc D hD q
        (le_of_lt hq) S (by exact_mod_cast hTpos) hjump hStrict
  linarith
