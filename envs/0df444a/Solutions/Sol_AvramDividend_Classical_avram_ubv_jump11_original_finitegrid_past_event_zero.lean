-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump11_original_finitegrid_past_event_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:53:30.224711+00:00
-- url     : https://prove2.me/submissions/fa062574-b824-4960-90fe-c00831aac874

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (n : ℕ) (A : Set Ω)
    (hA : ∀ i, MeasurableSet[𝓕.rightCont (grid i)] A) :
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let Z : ℕ → Ω → ℝ := fun i ω => H i ω * ((N i ω).toReal - r i)
    (∫ ω in A, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by
  classical
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
  let r : ℕ → ℝ := fun i =>
    (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
      X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
  let Z : ℕ → Ω → ℝ := fun i ω => H i ω * ((N i ω).toReal - r i)
  change (∫ ω in A, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0
  have hCell (i : ℕ) :
      MemLp (Z i) 2 P ∧
      P[Z i | 𝓕.rightCont (grid i)] =ᵐ[P] (fun _ => 0) := by
    have hs := avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
      X (grid i) (grid (i + 1) - grid i) cut (H i) (hH i) L (hBound i)
    have hw : grid i + (grid (i + 1) - grid i) = grid (i + 1) :=
      add_tsub_cancel_of_le (hGrid i)
    simpa only [Z, N, r, hw] using And.intro hs.1 hs.2.1
  have hInt (i : ℕ) : Integrable (Z i) P :=
    (hCell i).1.integrable (by norm_num)
  have hZero (i : ℕ) : (∫ ω in A, Z i ω ∂P) = 0 :=
    avram_ubv_jump11_past_event_integral_of_condexp_zero
      (𝓕.rightCont (grid i)) ((𝓕.rightCont).le (grid i))
      (Z i) (hInt i) (hCell i).2 A (hA i)
  rw [integral_finset_sum (Finset.range n)
    (by intro i hi; exact (hInt i).integrableOn)]
  simp only [hZero, Finset.sum_const_zero]
