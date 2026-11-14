-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_bv_positive_shift_actual_uniform_grid_prefix_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:50:44.555293+00:00
-- url     : https://prove2.me/submissions/f35898cd-ca9e-4822-b9a6-71320abea946

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_positive_shift_actual_uniform_grid_source_time_limit
import Theorems.Thm_AvramDividend_Classical_avram_chat24_original_strict_cash_uniform_grid_limit
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
    (∀ ω (B : ℝ≥0), 0 < B → B ≤ S →
      (B : ℝ≥0∞) < ruinTime X x D ω → ∀ n : ℕ,
    let N : ℕ := n + 1
    let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / (N : ℝ≥0)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let U : ℕ → ℝ := fun i => riskProcess X x D (u i) ω + δ
    let Z : ℕ → ℝ := fun i => x + δ + X.X (u (i + 1)) ω - D (u i) ω
    (∑ i ∈ Finset.range N, e i * (D (u (i + 1)) ω - D (u i) ω)) + e N * w (U N) ≤
      w (x + δ) + (∑ i ∈ Finset.range N,
        ((e (i + 1) - e i) * w (U i) + e (i + 1) * (w (Z i) - w (U i)))) +
        q * ((B : ℝ) / (N : ℝ)) * D B ω) →
    ∀ᵐ ω ∂P, ∀ B : ℝ≥0, 0 < B → B ≤ S →
      (B : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ t in Ico (0 : ℝ) (B : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * (B : ℝ))) * w (riskProcess X x D B ω + δ) ≤
      w (x + δ) +
        (∫ p, if (p.1 : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧
            Y (p.1, ω) ∈ Icc a b ∧ p.2 < 0 then
          Real.exp (-(q * (p.1 : ℝ))) *
            (w (Y (p.1, ω) + p.2) - w (Y (p.1, ω))) else 0 ∂(NX ω)) +
        (∫ t, if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y (t, ω) ∈ Icc a b then
          Real.exp (-(q * (t : ℝ))) *
            (X.drift * deriv w (Y (t, ω)) - q * w (Y (t, ω))) else 0 ∂μ) := by
  classical
  intro S a b τ Y NX H μ hfinite
  filter_upwards [avram_chat24_bv_positive_shift_actual_uniform_grid_source_time_limit
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    x hx hxc D hD hw_nonneg hjump T hT hTpos hTop δ hδ] with ω hsource
  intro B hB hBS hBruin
  have hcash := avram_chat24_original_strict_cash_uniform_grid_limit D hD.1.1 ω q hq.le B
  have herr : Tendsto (fun n : ℕ => q * ((B : ℝ) / ((n + 1 : ℕ) : ℝ)) * D B ω)
      atTop (nhds 0) := by
    have hh := (((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (B : ℝ)).const_mul q).mul_const (D B ω)
    simpa only [Nat.cast_add, Nat.cast_one, mul_one_div, mul_zero, zero_mul] using hh
  have hend (n : ℕ) : B * ((n + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) = B :=
    mul_div_cancel_right₀ B (by positivity)
  have hbound := fun n => hfinite ω B hB hBS hBruin n
  simp only [hend] at hbound
  have hl := hcash.add_const (Real.exp (-(q * (B : ℝ))) * w (riskProcess X x D B ω + δ))
  have hr := ((hsource B hB hBS hBruin).const_add (w (x + δ))).add herr
  have hh := le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall hbound)
  simpa only [a, b, Y, NX, μ, add_zero, add_assoc] using hh
