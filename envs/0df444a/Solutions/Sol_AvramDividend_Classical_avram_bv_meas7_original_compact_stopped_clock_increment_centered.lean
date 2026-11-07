-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_compact_stopped_clock_increment_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:51:32.056965+00:00
-- url     : https://prove2.me/submissions/21899ecf-f9c6-44d9-8d35-662348a7a6af

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_indexed_compact_separate_source
import Mathlib.Analysis.Calculus.ContDiff.Defs

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
    (n : ℕ) (T₀ T₁ : ℝ≥0) :
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
    Integrable (fun ω => M T₁ ω - M T₀ ω) P ∧
      (∫ ω, M T₁ ω - M T₀ ω ∂P) = 0 := by
  have h₀ :=
    (avram_bv_meas7_original_indexed_compact_separate_source
      X hBV x C D hD w hw_cont hw_neg hw_smooth q hq hw_gen
      T₀ a b ha ha2 hab hBand n).1
  have h₁ :=
    (avram_bv_meas7_original_indexed_compact_separate_source
      X hBV x C D hD w hw_cont hw_neg hw_smooth q hq hw_gen
      T₁ a b ha ha2 hab hBand n).1
  dsimp only
  refine ⟨h₁.1.sub h₀.1, ?_⟩
  rw [integral_sub h₁.1 h₀.1, h₁.2, h₀.2, sub_self]
