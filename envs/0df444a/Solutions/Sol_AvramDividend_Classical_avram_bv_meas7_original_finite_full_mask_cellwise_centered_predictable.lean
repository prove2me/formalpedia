-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_finite_full_mask_cellwise_centered_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:02:48.821639+00:00
-- url     : https://prove2.me/submissions/6979c24c-0147-40ac-9699-79d51d09ad60

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_finite_full_predictable_compact_bands
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_uniform_physical_cellwise_predictable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Every fixed strict-interior reserve eventually enters the actual
finite-cap original predictable stopped jump mask [a_n,b_n]; every physical
cell compensated X.ν increment is L1 centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTop : C ≠ ⊤)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (T : ℝ) (hT : 0 < T) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N,
        y ∈ Icc (a n) (b n)) ∧
      ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0) ∧
      (∀ n, ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n i, i < n + 1 →
        (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2)) ∧
      ∀ n : ℕ,
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
        ∀ i : ℕ, i < n + 1 →
          let S : ℝ≥0 := u n (i + 1)
          let τ : Ω → ℝ≥0 := fun ω =>
            (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
          let E : Set (ℝ≥0 × Ω) := {p |
            (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
          (Integrable (fun ω => M (u n (i + 1)) ω - M (u n i) ω) P ∧
           (∫ ω, M (u n (i + 1)) ω - M (u n i) ω ∂P) = 0) ∧
          ((∀ ω, τ ω ≤ S) ∧
           IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
           MeasurableSet[𝓕.rightCont.predictable] E ∧
           (∀ p ∈ E, Function.leftLim
             (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)) ∧
           (∀ p ∈ E, p.1 ≤ S)) := by
  obtain ⟨a, b, ha, ha2, hab, hBand, hEvent⟩ :=
    avram_bv_meas7_finite_full_predictable_compact_bands C hC hTop
  obtain ⟨u, hu0, huEnd, huMono, huWidth, hCells⟩ :=
    avram_bv_meas7_original_uniform_physical_cellwise_predictable
      X hBV x C D hD w hw_cont hw_neg hw_smooth q hq hw_gen
      a b ha ha2 hab hBand T hT
  exact ⟨a, b, ha, ha2, hab, hBand, hEvent, u, hu0, huEnd,
    huMono, huWidth, hCells⟩
