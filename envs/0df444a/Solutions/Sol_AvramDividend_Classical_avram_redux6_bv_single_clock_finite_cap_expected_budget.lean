-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux6_bv_single_clock_finite_cap_expected_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:19:26.030197+00:00
-- url     : https://prove2.me/submissions/f31a75c4-0146-424a-a57f-01a1da850795
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_finite_cap_original_full_T_HJB_source
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
import Theorems.Thm_AvramDividend_Classical_avram_a19_discounted_cash_terminal_prefix_budget_mono

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite-cap strict-clock budget follows from the original full-horizon
stochastic source and exact monotonicity of the actual Stieltjes cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∀ s : ℝ, 0 ≤ s → s < T →
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio s,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x := by
  dsimp
  intro s hs hst
  let S : ℝ≥0 := ⟨T, hT⟩
  let Terminal : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
  have hCashT := avram_p3_bv_original_strict_cash_L1
    X x C D hD q (le_of_lt hq) T hT
  have hCashS := avram_p3_bv_original_strict_cash_L1
    X x C D hD q (le_of_lt hq) s hs
  have hFin : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤ := by
    filter_upwards [] with ω
    exact avram_limit2_original_strict_discounted_cash_finite_all_paths
      X q (le_of_lt hq) x D hD.1.1 ω T hT
  have hTerm : Integrable Terminal P := by
    have hPre :=
      (avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
        X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hx hxc D hD q hjump S).2.1
    exact hPre
  have hPrefix := avram_a19_discounted_cash_terminal_prefix_budget_mono
    P D (fun ω => ruinTime X x D ω) q s T (le_of_lt hst)
    Terminal hFin hCashS hCashT hTerm
  have hFull := avram_a19_finite_cap_original_full_T_HJB_source
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
    hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos hFinite
  exact le_trans hPrefix hFull
