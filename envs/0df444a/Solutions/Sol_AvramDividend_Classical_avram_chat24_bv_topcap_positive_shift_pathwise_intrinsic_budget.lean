-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_bv_topcap_positive_shift_pathwise_intrinsic_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:32:01.828261+00:00
-- url     : https://prove2.me/submissions/e556e145-94ab-4aa4-af7e-e06ba7baffce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_positive_shift_intrinsic_chain_with_generator_remainder
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
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
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hTop : C = ⊤) (δ : ℝ) (hδ : 0 < δ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let a : ℝ := min δ 1 / 2
    let b : ℝ := x + δ + T * X.drift + 1
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => (x + δ) + X.X s p.2 - rightLimit D s p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) ∧
          Y p.1 ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let μ : Measure ℝ≥0 :=
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω + δ)
         else 0) ≤ w (x + δ) +
        ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
          (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μ)) := by   classical
  intro S a b τ Y NX H μ
  have ha : 0 < a := by dsimp [a]; positivity
  have hp := avram_chat24_bv_positive_shift_intrinsic_chain_with_generator_remainder
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
    (fun y hy hc => (hw_gen y hy hc).1) hw_grad x hx hxc D hD
    hw_nonneg hjump T hT hTpos hTop δ hδ
  filter_upwards [hp] with ω hω
  have hneg : (∫ t, if (t : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) ∧ Y (t, ω) ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) *
        (X.generator w (Y (t, ω)) - q * w (Y (t, ω))) else 0 ∂μ) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [] with t
    split_ifs with h
    · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
        (hw_gen _ (lt_of_lt_of_le ha h.2.1) (by simp [hTop])).2
    · exact le_refl 0
  exact le_trans hω (add_le_of_nonpos_right hneg)
