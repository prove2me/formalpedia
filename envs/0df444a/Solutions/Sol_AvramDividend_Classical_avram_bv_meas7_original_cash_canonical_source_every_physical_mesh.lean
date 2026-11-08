-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_cash_canonical_source_every_physical_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:30:35.264217+00:00
-- url     : https://prove2.me/submissions/ce1e0daa-92fd-4ad6-93cf-790d2f7dda7f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_cash_grid_signed_witness_separately_centered
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_raw_physical_J_eq_canonical_NX_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every original stopped physical cash-grid inequality uses the same
intrinsic centred Levy jump integral, uniformly in finite mesh count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (q : ℝ) (hq : 0 ≤ q) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (T : ℝ≥0) (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2) (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω => (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict
        {z : ℝ≥0 | 0 < z ∧
          X.X z ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z,
          X.X z ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
    let F : (ℝ≥0 × Ω) → ℝ := fun p => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) +
         (∫ z in Iio (0 : ℝ),
            w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
            w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
         q * w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1))
      else 0
    let Comp : Ω → ℝ := fun ω => ∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)
    let B : Ω → ℝ := fun ω => ∫ t, F (t, ω)
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)
    let J : Ω → ℝ := fun ω => ∫ p, H ((p.1, ω), p.2) ∂(NX ω)
    ∀ m : ℕ,
      (∀ᵐ ω ∂P,
        (let u : ℕ → ℝ≥0 := fun i =>
          min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
         let V : ℝ → ℝ := fun z =>
           if C = ⊤ then w z else if z ≤ C.toReal then w z
           else w C.toReal + (z - C.toReal)
         let cash : ℕ → ℝ := fun i =>
           (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Ioc (u i : ℝ) (u (i + 1) : ℝ),
             ENNReal.ofReal (Real.exp (-(q * t)))
               ∂(dividendMeasure D ω)).toReal
         let post : ℕ → ℝ := fun i =>
           w (x + X.X (u i) ω - rightLimit D (u i) ω)
         let source : ℕ → ℝ := fun i =>
           V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
           V (x + X.X (u i) ω - rightLimit D (u i) ω)
         0 < τ ω → ∃ k : ℕ, k ≤ m + 1 ∧ u k < τ ω ∧
           rightLimit D 0 ω +
             (∑ i ∈ Finset.range (m + 1), cash i) + post k ≤
           w x + (J ω - Comp ω + B ω) +
             max ((∑ i ∈ Finset.range k, source i) +
               (∑ i ∈ (Finset.range (m + 1)).filter
                 (fun i => u i < τ ω ∧ u (i + 1) = τ ω), cash i) -
               (J ω - Comp ω + B ω)) 0) ∧
        (let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
         let Eω : Set (ℝ≥0 × ℝ) :=
           {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
         let K : ℝ≥0 × ℝ → ℝ := fun p =>
           if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
         let R : ℝ≥0 × ℝ → ℝ := fun p =>
           (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
             (if p ∈ Eω then K p else 0)
         let Δ : ℝ≥0 → ℝ := fun v =>
           X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
         let u : ℕ → ℝ≥0 := fun i =>
           min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
         let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (R p)
         let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
           ENNReal.ofReal ((-1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
             (if p ∈ Eω then K p else 0))
         J ω =
           (∑ i ∈ Finset.range (m + 1),
             ∑' v : ℝ≥0,
               if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
                 Fp (v, Δ v) else 0).toReal -
           (∑ i ∈ Finset.range (m + 1),
             ∑' v : ℝ≥0,
               if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
                 Fm (v, Δ v) else 0).toReal)) ∧
      Integrable (fun ω => J ω - Comp ω + B ω) P ∧
      (∫ ω, J ω - Comp ω + B ω ∂P) ≤ 0 ∧
      Integrable (fun ω => J ω - Comp ω) P ∧
      (∫ ω, J ω - Comp ω ∂P) = 0 ∧
      Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0 := by
  intro τ E G H NX F Comp B J m
  obtain ⟨Jm, hGrid, hInt, hExp, hMInt, hMMean, hBInt, hBMean⟩ :=
    avram_bv_meas7_original_cash_grid_signed_witness_separately_centered
      X hBV x C hC hxc D hD w hw_cont hw_neg hwC1 hw_grad hjump
      q hq hw_gen T a b ha ha2 hab hBand n m
  have hEq : (fun ω => Jm ω) =ᵐ[P] J :=
    (avram_bv_meas7_original_raw_physical_J_eq_canonical_NX_integral
      X hBV x C D hD w hw_cont hw_neg hwC1 q hq hw_gen
      T a b ha ha2 hab hBand n m Jm
      (hGrid.mono (fun ω hω => hω.2))).1
  have hSourceEq : (fun ω => Jm ω - Comp ω + B ω) =ᵐ[P] (fun ω => J ω - Comp ω + B ω) := by
    filter_upwards [hEq] with ω hω
    simp only [← hω]
  have hMEq : (fun ω => Jm ω - Comp ω) =ᵐ[P] (fun ω => J ω - Comp ω) := by
    filter_upwards [hEq] with ω hω
    simp only [← hω]
  refine ⟨?_, ?_, ?_, ?_, ?_, hBInt, hBMean⟩
  · filter_upwards [hGrid, hEq] with ω hω he
    rw [he] at hω
    exact hω
  · exact hInt.congr hSourceEq
  · rw [← integral_congr_ae hSourceEq]
    exact hExp
  · exact hMInt.congr hMEq
  · rw [← integral_congr_ae hMEq]
    exact hMMean
