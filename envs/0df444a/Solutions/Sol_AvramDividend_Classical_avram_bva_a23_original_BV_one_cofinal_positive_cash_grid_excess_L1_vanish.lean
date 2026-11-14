-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a23_original_BV_one_cofinal_positive_cash_grid_excess_L1_vanish
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:51:12.924197+00:00
-- url     : https://prove2.me/submissions/f199e1e1-2fe1-4c8d-ad69-1fda3a839b9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_bva_a24_original_BV_fixed_band_cash_positive_excess_limit_vanishes_cofinally
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp16_diagonal_from_pointwise_fixed_band_errors
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (T : ℝ) (hT : 0 < T) (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) (u : ℕ → ℕ → ℝ≥0) (hu0 : ∀ n, u n 0 = 0) (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    : ∃ (a b : ℕ → ℝ), (∀ n, 0 < a n) ∧ (∀ n, a n ≤ 2) ∧ (∀ n, a n ≤ b n) ∧ (∀ n, Icc (a n / 2) (b n) ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧ (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) ∧ (
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal + (if (S : ℝ≥0∞) < ruinTime X x D ω then Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    let N : ℕ → Ω → ℝ := fun n ω =>
      let M : ℝ≥0 → Ω → ℝ := fun S ω =>
        let τ : Ω → ℝ≥0 := fun ω' => (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
        let E : Set (ℝ≥0 × Ω) := {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧ Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
        let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => if p.1 ∈ E ∧ p.2 < 0 then Real.exp (-(q * (p.1.1 : ℝ))) * (w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0
        let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
        let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω' => ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v ≠ 0}).map (fun v : ℝ≥0 => (v, X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v)))
        (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
      (Finset.sum (Finset.range (n + 1)) (fun i => M (u n (i + 1)) ω - M (u n i) ω)) + (0 : ℝ)
    Tendsto (fun m => ∫ ω, max (F m ω - (w x + N m ω)) 0 ∂P) atTop (𝓝 (0 : ℝ))) := by
  classical
  obtain ⟨a, b, ha, ha2, hab, hinside, hcover, B, hB, hFix⟩ :=
    avram_bva_a24_original_BV_fixed_band_cash_positive_excess_limit_vanishes_cofinally
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hInfinite
      u hu0 huniform
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  let N : ℕ → ℕ → Ω → ℝ := fun k n ω =>
    let M : ℝ≥0 → Ω → ℝ := fun S ω =>
      let τ : Ω → ℝ≥0 := fun ω' =>
        (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
      let E : Set (ℝ≥0 × Ω) := {p |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a k) (b k)}
      let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if p.1 ∈ E ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
        else 0
      let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω' =>
        ((Measure.count.restrict
          {v : ℝ≥0 | 0 < v ∧
            X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v ≠ 0}).map
          (fun v : ℝ≥0 => (v,
            X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v)))
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
    (Finset.sum (Finset.range (n + 1))
      (fun i => M (u n (i + 1)) ω - M (u n i) ω)) + (0 : ℝ)
  let E : ℕ → ℕ → ℝ := fun k n => ∫ ω, max (F n ω - (w x + N k n ω)) 0 ∂P
  have hErr (k : ℕ) : Tendsto (fun n => E k n - B k) atTop (𝓝 (0 : ℝ)) := by
    convert (hFix k).sub (show Tendsto (fun _ : ℕ => B k) atTop (𝓝 (B k)) from tendsto_const_nhds) using 1 <;> simp [E]
  obtain ⟨κ, _, hκtop, hdiag⟩ := avram_p3_comp16_diagonal_from_pointwise_fixed_band_errors
      (fun k n => E k n - B k) hErr
  have hCoverDiag (y : ℝ) (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a (κ n)) (b (κ n)) := by
    obtain ⟨N, hN⟩ := hcover y hy hyC
    obtain ⟨j, hj⟩ := eventually_atTop.1 ((tendsto_atTop.1 hκtop) N)
    exact ⟨j, fun n hn => hN (κ n) (hj n hn)⟩
  refine ⟨(fun n => a (κ n)), (fun n => b (κ n)), (fun n => ha (κ n)), (fun n => ha2 (κ n)),
    (fun n => hab (κ n)), (fun n => hinside (κ n)),
    hCoverDiag, ?_⟩
  change Tendsto (fun m => E (κ m) m) atTop (𝓝 (0 : ℝ))
  convert (hdiag.add (hB.comp hκtop)) using 1
  funext n
  all_goals simp [Function.comp_apply, sub_add_cancel]
