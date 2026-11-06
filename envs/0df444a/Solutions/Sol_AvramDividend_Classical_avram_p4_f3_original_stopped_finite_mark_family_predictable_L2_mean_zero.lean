-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_stopped_finite_mark_family_predictable_L2_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:13:17.050963+00:00
-- url     : https://prove2.me/submissions/fde62857-2970-4662-83b2-1a8a3e144c61

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_stopped_physical_grid_L2_mean_zero_joint
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Finite intrinsic negative mark families on the same physical stopped grid are predictable L² and exactly centred. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε)
    (C : ι → ℕ → Set ℝ)
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
    (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ j i, StronglyMeasurable[𝓕.rightCont (grid i)] (H j i))
    (hHL2 : ∀ j i, MemLp (H j i) 2 P)
    (L : ι → ℝ) (hBound : ∀ j i ω, |H j i ω| ≤ L j)
    (n : ℕ) (F : Finset ι) :
    let Z : ι → Ω → ℝ := fun j ω =>
      ∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H j i ω) *
          ((N j i ω).toReal -
            (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
              X.ν (C j i)).toReal)
    MemLp (fun ω => ∑ j ∈ F, Z j ω) 2 P ∧
      (∫ ω, ∑ j ∈ F, Z j ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Z : ι → Ω → ℝ := fun j ω =>
    ∑ i ∈ Finset.range n,
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H j i ω) *
        ((N j i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C j i)).toReal)
  change MemLp (fun ω => ∑ j ∈ F, Z j ω) 2 P ∧
    (∫ ω, ∑ j ∈ F, Z j ω ∂P) = 0
  have hSingle (j : ι) :
      MemLp (Z j) 2 P ∧ (∫ ω, Z j ω ∂P) = 0 := by
    exact
      avram_p4_s3_run1640_original_stopped_physical_grid_L2_mean_zero_joint
        X T cut τ hτstop grid hGrid hTime ε hε
        (C j) (hC j) (hBand j) (hCut j) (hν j)
        (N j) (hActual j) (H j) (hH j) (hHL2 j)
        (L j) (hBound j) n
  have hFunSum :
      (fun ω => ∑ j ∈ F, Z j ω) = ∑ j ∈ F, Z j := by
    funext ω
    simp
  have hMem (E : Finset ι) :
      MemLp (∑ j ∈ E, Z j) 2 P := by
    induction E using Finset.induction_on with
    | empty => simp
    | @insert j E hj ih =>
      simpa only [Finset.sum_insert hj] using ((hSingle j).1.add ih)
  constructor
  · rw [hFunSum]
    exact hMem F
  · rw [integral_finset_sum F (by
      intro j hj
      exact ((hSingle j).1).integrable (by norm_num))]
    have hMean (j : ι) : (∫ ω, Z j ω ∂P) = 0 :=
      (hSingle j).2
    simp only [hMean, Finset.sum_const_zero]
