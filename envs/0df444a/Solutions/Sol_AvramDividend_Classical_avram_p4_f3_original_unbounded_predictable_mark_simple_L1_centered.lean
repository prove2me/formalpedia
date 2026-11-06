-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_unbounded_predictable_mark_simple_L1_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:18:43.337176+00:00
-- url     : https://prove2.me/submissions/cf8e7125-f61c-41d3-ab23-6e0056d3c220

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Original compensated marked jumps admit unbounded L2-predictable finite simple sums. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (a b : ι → ℝ≥0)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (hbT : ∀ i ∈ S, b i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hBand : ∀ i ∈ S, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i ∈ S, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ S, StronglyMeasurable[𝓕 (a i)] (H i))
    (hHL2 : ∀ i ∈ S, MemLp (H i) 2 P) :
    let N : ι → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (a i) (b i) ×ˢ B i)
    let r : ι → ℝ := fun i =>
      ((((b i - a i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal
    Integrable (fun ω => ∑ i ∈ S,
      H i ω * ((N i ω).toReal - r i)) P ∧
    (∫ ω, (∑ i ∈ S,
      H i ω * ((N i ω).toReal - r i)) ∂P) = 0 := by
  let N : ι → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (a i) (b i) ×ˢ B i)
  let r : ι → ℝ := fun i =>
    ((((b i - a i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal
  change Integrable (fun ω => ∑ i ∈ S,
    H i ω * ((N i ω).toReal - r i)) P ∧
    (∫ ω, (∑ i ∈ S,
      H i ω * ((N i ω).toReal - r i)) ∂P) = 0
  have hCell (i : ι) (hi : i ∈ S) :
      Integrable (fun ω => H i ω * ((N i ω).toReal - r i)) P ∧
      (∫ ω, H i ω * ((N i ω).toReal - r i) ∂P) = 0 := by
    exact avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
      X T cut (a i) (b i) (hab i hi) (hbT i hi)
      ε hε (B i) (hB i hi) (hBand i hi) (hCut i hi)
      (H i) (hH i hi) (hHL2 i hi)
  have hInt : ∀ i ∈ S,
      Integrable (fun ω => H i ω * ((N i ω).toReal - r i)) P := by
    intro i hi
    exact (hCell i hi).1
  constructor
  · exact integrable_finset_sum S hInt
  · rw [integral_finset_sum S hInt]
    apply Finset.sum_eq_zero
    intro i hi
    exact (hCell i hi).2
