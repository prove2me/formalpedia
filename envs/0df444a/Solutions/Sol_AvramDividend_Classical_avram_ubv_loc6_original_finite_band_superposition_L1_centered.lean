-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_original_finite_band_superposition_L1_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:11:35.164612+00:00
-- url     : https://prove2.me/submissions/69d1b4dc-c734-49a0-ba88-e235b910eae2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_arbitrary_compact_negative_grid_L1_centered

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Sum finitely many genuine compensated jump-band increments, each centred
    at the same original-process right-continuous stopping clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (Cap : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x Cap D)
    (n : ℕ) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (S : Finset ι)
    (C : ι → ℕ → Set ℝ)
    (hC : ∀ j i, MeasurableSet (C j i))
    (hBand : ∀ j i, C j i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ j i, C j i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (N : ι → ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ j i, N j i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C j i))
    (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ j i, StronglyMeasurable[𝓕.rightCont (grid i)] (H j i))
    (hHL2 : ∀ j i, MemLp (H j i) 2 P)
    (τ σ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσle : ∀ ω, σ ω ≤ τ ω)
    (k : ℕ) :
    Integrable (fun ω => ∑ j ∈ S, ∑ i ∈ Finset.range k,
      (if (σ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
       then (0 : ℝ) else H j i ω) *
      ((N j i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C j i)).toReal)) P ∧
    (∫ ω, (∑ j ∈ S, ∑ i ∈ Finset.range k,
      (if (σ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
       then (0 : ℝ) else H j i ω) *
      ((N j i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C j i)).toReal)) ∂P) = 0 := by
  classical
  let J (j : ι) (ω : Ω) : ℝ := ∑ i ∈ Finset.range k,
    (if (σ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
     then (0 : ℝ) else H j i ω) *
    ((N j i ω).toReal -
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (C j i)).toReal)
  have hOne (j : ι) : Integrable (J j) P ∧ (∫ ω, J j ω ∂P) = 0 := by
    exact avram_ubv_loc6_original_arbitrary_compact_negative_grid_L1_centered
      X x Cap D hD n T cut grid hGrid hTime ε hε
      (C j) (hC j) (hBand j) (hCut j)
      (N j) (hActual j) (H j) (hH j) (hHL2 j)
      τ σ hτeq hσstop hσle k
  have hInt : Integrable (fun ω => ∑ j ∈ S, J j ω) P := by
    exact integrable_finset_sum S (fun j hj => (hOne j).1)
  have hMean : (∫ ω, (∑ j ∈ S, J j ω) ∂P) = 0 := by
    calc
      (∫ ω, (∑ j ∈ S, J j ω) ∂P) =
          ∑ j ∈ S, (∫ ω, J j ω ∂P) := by
            exact integral_finset_sum S (fun j hj => (hOne j).1)
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact (hOne j).2
  constructor
  · simpa only [J] using hInt
  · simpa only [J] using hMean
