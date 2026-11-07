-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_finite_physical_grid_increment_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:14:27.607185+00:00
-- url     : https://prove2.me/submissions/bc6c3c30-52fc-4f15-ad69-3e9d1034407e

import Mathlib
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_compact_stopped_clock_increment_centered

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- On the same original probability space and Lévy jump source, the
difference of genuine ruin-stopped compensated integrals at two bounded
physical clocks is integrable and exactly centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n k : ℕ) (u : ℕ → ℝ≥0) :
    let M : ℝ≥0 → Ω → ℝ := fun S ω =>
      let τ : Ω → ℝ≥0 := fun ω' =>
        (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
      let E : Set (ℝ≥0 × Ω) := {p |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
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
          {u : ℝ≥0 | 0 < u ∧
            X.X u ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') u)))
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
    Integrable (fun ω => Finset.sum (Finset.range k)
      (fun i => M (u (i + 1)) ω - M (u i) ω)) P ∧
    (∫ ω, (Finset.sum (Finset.range k)
      (fun i => M (u (i + 1)) ω - M (u i) ω)) ∂P) = 0 := by
  have hIncr :=
    avram_bv_meas7_original_compact_stopped_clock_increment_centered
      X hBV x C D hD w hw_cont hw_neg hw_smooth q hq hw_gen
      a b ha ha2 hab hBand n (u 0) (u k)
  let M : ℝ≥0 → Ω → ℝ := fun S ω =>
      let τ : Ω → ℝ≥0 := fun ω' =>
        (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
      let E : Set (ℝ≥0 × Ω) := {p |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
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
          {u : ℝ≥0 | 0 < u ∧
            X.X u ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') u)))
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
  have hTel (ω : Ω) : ∀ m : ℕ,
      Finset.sum (Finset.range m) (fun i => M (u (i + 1)) ω - M (u i) ω) =
        M (u m) ω - M (u 0) ω := by
    intro m
    induction m with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  change Integrable (fun ω => Finset.sum (Finset.range k)
    (fun i => M (u (i + 1)) ω - M (u i) ω)) P ∧
    (∫ ω, (Finset.sum (Finset.range k)
      (fun i => M (u (i + 1)) ω - M (u i) ω)) ∂P) = 0
  dsimp only at hIncr
  simpa only [hTel] using hIncr
