-- Prove2me | solution 1 for AvramDividend.Classical.avram_pjmask15_original_mark_simple_stopped_initial_event_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:46:43.850674+00:00
-- url     : https://prove2.me/submissions/a20a0fa7-4f2f-4656-96fa-6a4856928b44

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_finite_mark_family_predictable_L2_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- The original stopped finite-mark compensation remains centred after
    multiplying all predictable weights by one initial-event mask. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (C : ι → ℕ → Set ℝ)
    (hC : ∀ j i, MeasurableSet (C j i))
    (hBand : ∀ j i, C j i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ j i, C j i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hν : ∀ j i, X.ν (C j i) < ⊤)
    (N : ι → ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ j i, N j i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C j i))
    (H : ι → ℕ → Ω → ℝ) (A : Set Ω) (hA : MeasurableSet A)
    (hHmask : ∀ j i, StronglyMeasurable[𝓕.rightCont (grid i)]
      (A.indicator (H j i)))
    (hHL2mask : ∀ j i, MemLp (A.indicator (H j i)) 2 P)
    (L : ι → ℝ)
    (hBoundmask : ∀ j i ω, |A.indicator (H j i) ω| ≤ L j)
    (n : ℕ) (F : Finset ι) :
    (∫ ω in A, ∑ j ∈ F, ∑ i ∈ Finset.range n,
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H j i ω) *
      ((N j i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C j i)).toReal) ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Hm : ι → ℕ → Ω → ℝ :=
    fun j i => A.indicator (H j i)
  have hMean :
      (∫ ω, ∑ j ∈ F, ∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else Hm j i ω) *
        ((N j i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C j i)).toReal) ∂P) = 0 := by
    exact (avram_p4_f3_original_stopped_finite_mark_family_predictable_L2_mean_zero
      X T cut τ hτstop grid hGrid hTime ε hε C hC hBand hCut hν
      N hActual Hm hHmask hHL2mask L hBoundmask n F).2
  have hPoint (ω : Ω) :
      A.indicator (fun η => ∑ j ∈ F, ∑ i ∈ Finset.range n,
        (if (τ η : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H j i η) *
        ((N j i η).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C j i)).toReal)) ω =
      ∑ j ∈ F, ∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else Hm j i ω) *
        ((N j i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C j i)).toReal) := by
    by_cases hω : ω ∈ A
    · simp only [Hm, Set.indicator_of_mem hω]
    · simp [Set.indicator, Hm, hω]
  calc
    (∫ ω in A, ∑ j ∈ F, ∑ i ∈ Finset.range n,
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H j i ω) *
      ((N j i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C j i)).toReal) ∂P) =
      ∫ ω, A.indicator (fun η => ∑ j ∈ F, ∑ i ∈ Finset.range n,
        (if (τ η : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H j i η) *
        ((N j i η).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C j i)).toReal)) ω ∂P := (integral_indicator hA).symm
    _ = (∫ ω, ∑ j ∈ F, ∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else Hm j i ω) *
        ((N j i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C j i)).toReal) ∂P) := by
        congr 1
        funext ω
        exact hPoint ω
    _ = 0 := hMean
