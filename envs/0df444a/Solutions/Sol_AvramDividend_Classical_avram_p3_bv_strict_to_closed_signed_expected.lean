-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_strict_to_closed_signed_expected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:27:20.574702+00:00
-- url     : https://prove2.me/submissions/ce853128-6f74-40e2-bca4-fd9c94150074

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_canonical_signed_horizon_correction
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Exact original closed-horizon signed verification follows from an L1
strict stopped budget. All horizon atoms and the post-rightpayment terminal
are preserved by the imported source-specific pointwise correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Strict : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0)
    Integrable Strict P → (∫ ω, Strict ω ∂P) ≤ w x →
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∂P) +
    (∫ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω)
      else 0 ∂P) ≤ w x := by
  intro S Strict hStrictInt hStrictBudget
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  let Term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω)
    else 0
  have hJoint := avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add
    X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad x D hD T hT hTpos
  have hInt : Integrable (fun ω => Cash ω + Term ω) P := by
    exact hJoint.1
  have hAdd : (∫ ω, Cash ω + Term ω ∂P) =
      (∫ ω, Cash ω ∂P) + (∫ ω, Term ω ∂P) := hJoint.2
  have hPoint (ω : Ω) : Cash ω + Term ω ≤ Strict ω := by
    have hST : (S : ℝ) = T := rfl
    simpa only [Cash, Term, Strict, hST] using
      (avram_p3_c_bvchain_original_canonical_signed_horizon_correction
        X x C D hD w hjump ω S (by exact_mod_cast hTpos)
        q (le_of_lt hq))
  have hMean : (∫ ω, Cash ω + Term ω ∂P) ≤
      (∫ ω, Strict ω ∂P) :=
    integral_mono hInt hStrictInt hPoint
  change (∫ ω, Cash ω ∂P) + (∫ ω, Term ω ∂P) ≤ w x
  calc
    (∫ ω, Cash ω ∂P) + (∫ ω, Term ω ∂P) =
        (∫ ω, Cash ω + Term ω ∂P) := hAdd.symm
    _ ≤ ∫ ω, Strict ω ∂P := hMean
    _ ≤ w x := hStrictBudget
