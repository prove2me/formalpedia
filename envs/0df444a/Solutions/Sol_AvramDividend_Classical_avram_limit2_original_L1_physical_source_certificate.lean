-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_L1_physical_source_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:26:10.621207+00:00
-- url     : https://prove2.me/submissions/d82a8f82-2c20-4052-a841-23c798ea6900

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_e2_original_stopped_source_finite_grid_expected_upper
import Theorems.Thm_AvramDividend_Classical_avram_limit2_L1mesh_signed_certificate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An original compensated-jump and drift stopped mesh with physical
    L¹ payoff convergence gives all six canonical signed BV clauses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (Snn : ℝ≥0) (hSnn : (Snn : ℝ) = T)
    (τ : ℕ → Ω → ℝ≥0)
    (hτBound : ∀ n ω, τ n ω ≤ Snn)
    (hτ : ∀ n, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ n ω : WithTop ℝ≥0)))
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBandWide : ∀ n, Icc ((a n) / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (E : ℕ → Set (ℝ≥0 × Ω))
    (hEm : ∀ n, MeasurableSet[𝓕.rightCont.predictable] (E n))
    (hEregion : ∀ n, ∀ p ∈ E n,
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n))
    (Mmesh Bmesh Fmesh : ℕ → Ω → ℝ)
    (hSource : ∀ n, let Upre : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
    Function.leftLim (fun v : ℝ≥0 =>
      x + X.X v p.2 - rightLimit D v p.2) p.1);
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := (fun p : (ℝ≥0 × Ω) × ℝ =>
    if p.1 ∈ E n ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
       (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
        w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
    else 0);
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ n p.1.2 : ℝ≥0∞) then G p else 0;
  let F : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
    if p ∈ E n then Real.exp (-(q * (p.1 : ℝ))) *
      (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 =>
          x + X.X v p.2 - rightLimit D v p.2) p.1) +
       (∫ z in Iio (0 : ℝ),
          w (Function.leftLim (fun v : ℝ≥0 =>
            x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
          w (Function.leftLim (fun v : ℝ≥0 =>
            x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
       q * w (Function.leftLim (fun v : ℝ≥0 =>
          x + X.X v p.2 - rightLimit D v p.2) p.1))
    else 0);
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict
{u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω -
Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)));
  let M : Ω → ℝ := fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z)
∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (Snn : ℝ))).map Real.toNNReal));
  let B : Ω → ℝ := fun ω => (∫ t, F (t, ω) ∂(((volume : Measure ℝ).restrict (Icc 0 (Snn : ℝ))).map Real.toNNReal));
  Mmesh n = M ∧ Bmesh n = B)
    (hFm : ∀ n, Measurable (Fmesh n))
    (hFi : ∀ n, Integrable (Fmesh n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] Fmesh n)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      Fmesh n ω ≤ w x + (Mmesh n ω + Bmesh n ω))
    (R : Ω → ℝ)
    (hRm : AEStronglyMeasurable R P)
    (hL1 : Tendsto (fun n => eLpNorm (Fmesh n - R) 1 P)
      atTop (nhds 0)) :
    ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        ENNReal.ofReal (R ω) ≤
          liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hMean : ∀ n, (∫ ω, Fmesh n ω ∂P) ≤ w x :=
    avram_p3_e2_original_stopped_source_finite_grid_expected_upper
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hT hTpos Snn hSnn τ hτBound hτ
      a b ha ha2 hab hBandWide E hEm hEregion
      Mmesh Bmesh Fmesh hSource hFm hFi hFn hBudget
  exact avram_limit2_L1mesh_signed_certificate
    Fmesh R (w x) hFm hFi hFn hMean hRm hL1
