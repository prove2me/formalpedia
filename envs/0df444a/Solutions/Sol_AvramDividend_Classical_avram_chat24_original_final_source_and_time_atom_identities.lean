-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_original_final_source_and_time_atom_identities
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T14:12:06.184269+00:00
-- url     : https://prove2.me/submissions/c661a628-57f1-4217-9a0c-2e9bba24f7d1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat24_original_negative_jump_endpoint_fiber_public
import Theorems.Thm_AvramDividend_Classical_avram_chat24_physical_clock_endpoint_fiber_zero_public

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
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
    let K : Ω → ℝ≥0 → ℝ := fun ω B =>
      (∫⁻ t in Ico (0 : ℝ) (B : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let V : Ω → ℝ≥0 → ℝ := fun ω B =>
      Real.exp (-(q * (B : ℝ))) * w (riskProcess X x D B ω + δ)
    let R : Ω → ℝ≥0 → ℝ := fun ω B =>
      (∫ p, if (p.1 : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧
          Y (p.1, ω) ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1 : ℝ))) *
          (w (Y (p.1, ω) + p.2) - w (Y (p.1, ω))) else 0 ∂(NX ω)) +
      (∫ t, if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y (t, ω) ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) *
          (X.drift * deriv w (Y (t, ω)) - q * w (Y (t, ω))) else 0 ∂μ)
    let Kstop : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let J : Ω → ℝ := fun ω =>
      let z : ℝ := X.X (τ ω) ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) (τ ω)
      if Y (τ ω, ω) ∈ Icc a b ∧ z < 0 then
        Real.exp (-(q * (τ ω : ℝ))) * (w (Y (τ ω, ω) + z) - w (Y (τ ω, ω))) else 0
    ∀ᵐ ω ∂P, 0 < ruinTime X x D ω →
      ruinTime X x D ω ≤ (S : ℝ≥0∞) →
      (∫ p : ℝ≥0 × ℝ,
        if p.1 = τ ω ∧ Y (p.1, ω) ∈ Icc a b ∧ p.2 < 0 then
          Real.exp (-(q * (p.1 : ℝ))) * (w (Y (p.1, ω) + p.2) - w (Y (p.1, ω))) else 0 ∂(NX ω)) = J ω ∧
      (∫ t : ℝ≥0, if t = τ ω ∧ Y (t, ω) ∈ Icc a b then
          Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Y (t, ω)) - q * w (Y (t, ω))) else 0 ∂μ) = 0 := by
  classical
  intro S a b τ Y NX H μ K V R Kstop J
  refine Filter.Eventually.of_forall (fun ω hσ hσS => ?_)
  have hmin : min (ruinTime X x D ω) (S : ℝ≥0∞) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top)
  have hτeq : (τ ω : ℝ≥0∞) = min (ruinTime X x D ω) (S : ℝ≥0∞) :=
    ENNReal.coe_toNNReal hmin
  have hSpos : (0 : ℝ≥0∞) < (S : ℝ≥0∞) := by exact_mod_cast hTpos
  have hτpos : 0 < τ ω := by
    have hp : (0 : ℝ≥0∞) < (τ ω : ℝ≥0∞) := by rw [hτeq]; exact lt_min hσ hSpos
    exact_mod_cast hp
  constructor
  · have hs := avram_chat24_original_negative_jump_endpoint_fiber_public X ω (τ ω) hτpos
      (fun t => Y (t, ω) ∈ Icc a b)
      (fun p => Real.exp (-(q * (p.1 : ℝ))) * (w (Y (p.1, ω) + p.2) - w (Y (p.1, ω))))
    exact hs
  · have ht := avram_chat24_physical_clock_endpoint_fiber_zero_public T (τ ω)
      (fun t => if Y (t, ω) ∈ Icc a b then Real.exp (-(q * (t : ℝ))) *
        (X.drift * deriv w (Y (t, ω)) - q * w (Y (t, ω))) else 0)
    simpa only [ite_and] using ht
