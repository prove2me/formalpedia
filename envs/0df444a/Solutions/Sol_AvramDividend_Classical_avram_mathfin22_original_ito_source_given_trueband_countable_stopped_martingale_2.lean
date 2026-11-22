-- Prove2me | solution 2 for AvramDividend.Classical.avram_mathfin22_original_ito_source_given_trueband_countable_stopped_martingale
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:16:08.03397+00:00
-- url     : https://prove2.me/submissions/b3231447-93b8-416f-a6ab-f1902b5d9d2d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_original_trueband_given_compensated_Lp2_and_gaussian_caplinear
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_continuous_isometry_of_all_Lp2_simple
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_continuous_centering_of_all_Lp2_simple
import Theorems.Thm_AvramDividend_Classical_avram_gbB140_original_stopped_upperstrip_undiscounted_occupation_charge
import Theorems.Thm_AvramDividend_Classical_avram_gbB136_original_upperstrip_positive_drift_finitegrid_sum_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
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
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hBand : ∀ (K : ℝ≥0) (a b : ℕ) (hab : a ≤ b)
      (σ : Ω → WithTop ℝ≥0)
      (hσ : IsStoppingTime 𝓕.rightCont σ)
      (hσBound : ∀ ω, σ ω ≤ (K : WithTop ℝ≥0))
      (hσCount : (Set.range σ).Countable),
        let B : Set ℝ :=
          Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
        let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
          ((Measure.count.restrict {s : ℝ≥0 |
            0 < s ∧ X.X s ω -
              Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
            (fun s : ℝ≥0 => (s, X.X s ω -
              Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
        let J : Ω → ℝ := fun ω =>
          (∫ p in Ioc 0 (σ ω).untopA ×ˢ B, p.2 ∂NX ω) -
            (((σ ω).untopA : ℝ) * (∫ z in B, z ∂X.ν))
        Integrable J P ∧ (∫ ω, J ω ∂P) = 0) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  apply AvramDividend.Classical.avram_bridge20261122_original_trueband_given_compensated_Lp2_and_gaussian_caplinear X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm hTermMeas hCashI hBand
  exact ⟨AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_isometry_of_all_Lp2_simple X,
    AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_centering_of_all_Lp2_simple X,
    AvramDividend.Classical.avram_gbB140_original_stopped_upperstrip_undiscounted_occupation_charge X,
    AvramDividend.Classical.avram_gbB136_original_upperstrip_positive_drift_finitegrid_sum_bound X⟩
