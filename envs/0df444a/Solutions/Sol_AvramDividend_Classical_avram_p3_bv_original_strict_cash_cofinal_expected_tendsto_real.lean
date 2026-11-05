-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_expected_tendsto_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:06:15.569795+00:00
-- url     : https://prove2.me/submissions/822fd9ba-fc69-4c93-a3c4-7b5cb9412d2d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cash_strict_horizon_mono
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_rightlimit_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_tendsto_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On an increasing nonnegative cofinal grid, expectations of the exact
original stopped Stieltjes dividend cash converge to the fixed horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n)
    (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n) :
    Tendsto (fun n => ∫ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal ∂P)
      atTop (nhds (∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal ∂P)) := by
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal
  let G : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal
  have hGI : Integrable G P :=
    avram_p3_bv_original_strict_cash_L1 X x C D hD q hq (S : ℝ) S.property
  have hFI (n : ℕ) : Integrable (F n) P :=
    avram_p3_bv_original_strict_cash_L1 X x C D hD q hq (u n) (hu n)
  have hbound (n : ℕ) (ω : Ω) : ‖F n ω‖ ≤ G ω := by
    have hfin :
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) < ⊤ :=
      lt_of_le_of_lt
        (avram_p3_bv_original_strict_cash_rightlimit_bound
          D hD.1.1 ω (ruinTime X x D ω) S q hq)
        ENNReal.ofReal_lt_top
    change ‖(∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono (ne_of_lt hfin)
      (avram_p3_bv_original_cash_strict_horizon_mono
        X x q (u n) (S : ℝ) (hbelow n) D ω)
  have hFM : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (F n) P :=
    Filter.Eventually.of_forall (fun n => (hFI n).aestronglyMeasurable)
  have hFB : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ G ω :=
    Filter.Eventually.of_forall (fun n => Filter.Eventually.of_forall (hbound n))
  have hFL : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (nhds (G ω)) :=
    Filter.Eventually.of_forall (fun ω =>
      avram_p3_bv_original_strict_cash_cofinal_tendsto_real
        X x C D hD q hq S ω u hmono hbelow hcover)
  change Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (nhds (∫ ω, G ω ∂P))
  exact tendsto_integral_filter_of_dominated_convergence G hFM hFB hGI hFL
