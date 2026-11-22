-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261122_BV_budget_given_full_and_strict_cash_mesh
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:37:38.990565+00:00
-- url     : https://prove2.me/submissions/465b23fa-9afd-49d7-bbad-a96fcca76f4b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_strict_HJB_to_signed_full
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
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
    (hSourceCashMesh : ∀ (ω : Ω) (m n : ℕ),
      let S : ℝ≥0 := ⟨T, hT⟩
          let τ : ℝ≥0 :=
            (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
          let u : ℕ → ℝ≥0 := fun j =>
            min (((min j (m + 1) : ℕ) : ℝ≥0) *
              (S / (m + 1))) τ
          (ENNReal.ofReal (rightLimit D 0 ω) +
            (∑ i ∈ Finset.range n,
              ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
                (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
                    Ioc (u i : ℝ) (u (i + 1) : ℝ),
                  (1 : ℝ≥0∞) ∂(dividendMeasure D ω))) ≤
            ENNReal.ofReal (rightLimit D 0 ω) +
            (∑ i ∈ Finset.range n,
              (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
                  Ioc (u i : ℝ) (u (i + 1) : ℝ),
                ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))) ∧
          (ENNReal.ofReal (rightLimit D 0 ω) +
            (∑ i ∈ Finset.range n,
              (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
                  Ioc (u i : ℝ) (u (i + 1) : ℝ),
                ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ≤
            ENNReal.ofReal (rightLimit D 0 ω) +
            (∑ i ∈ Finset.range n,
              ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
                (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
                    Ioc (u i : ℝ) (u (i + 1) : ℝ),
                  (1 : ℝ≥0∞) ∂(dividendMeasure D ω))))
    )
    (hStrictCashMesh : ∀ (ω : Ω) (m n : ℕ),
      let S : ℝ≥0 := ⟨T, hT⟩
          let τ : ℝ≥0 :=
            (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
          let u : ℕ → ℝ≥0 := fun j =>
            min (((min j (m + 1) : ℕ) : ℝ≥0) *
              (S / (m + 1))) τ
          (ENNReal.ofReal (rightLimit D 0 ω) +
            ∑ i ∈ Finset.range n,
              (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩
                    Iio (S : ℝ)) ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ),
                ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ≤
            ENNReal.ofReal (rightLimit D 0 ω) +
            ∑ i ∈ Finset.range n,
              ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
                (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
                    Ioc (u i : ℝ) (u (i + 1) : ℝ),
                  (1 : ℝ≥0∞) ∂(dividendMeasure D ω))
    ) :
    let S : ℝ≥0 := ⟨T,hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x    := by
  have hStrict :=
    avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
  have hFull :=
    avram_p3_bv_strict_HJB_to_signed_full
      X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_grad x D hD hjump T hT hTpos hStrict
  dsimp
  exact hFull
