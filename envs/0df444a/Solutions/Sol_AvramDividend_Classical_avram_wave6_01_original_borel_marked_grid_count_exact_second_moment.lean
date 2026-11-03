-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_borel_marked_grid_count_exact_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:49:48.473815+00:00
-- url     : https://prove2.me/submissions/a419847c-5583-4812-b612-cc8da76fe681

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_two_separated_marked_increment_cells_probability_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- The exact original Bernoulli marked-grid second moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, (∑ i ∈ Finset.range n,
      ({v : Ω | X.X (t (i + 1)) v - X.X (t i) v ∈ B}).indicator
        (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) =
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      if i = j then
        P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}
      else
        P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B} *
        P {ω | X.X (t (j + 1)) ω - X.X (t j) ω ∈ B} := by
  classical
  haveI := X.isProbability
  let S : Finset ℕ := Finset.range n
  let E : ℕ → Set Ω := fun i =>
    {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}
  let Y : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    (E i).indicator (fun _ => (1 : ℝ≥0∞)) ω
  have hXm (u : ℝ≥0) : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  have hE (i : ℕ) : MeasurableSet (E i) :=
    hB.preimage ((hXm _).sub (hXm _))
  have hY (i : ℕ) : Measurable (Y i) :=
    measurable_const.indicator (hE i)
  have hProd (i j : ℕ) :
      (fun ω : Ω => Y i ω * Y j ω) =
        (E i ∩ E j).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases hi : ω ∈ E i <;> by_cases hj : ω ∈ E j <;>
      simp [Y, hi, hj]
  have hProdMean (i j : ℕ) :
      (∫⁻ ω, Y i ω * Y j ω ∂P) = P (E i ∩ E j) := by
    calc
      (∫⁻ ω, Y i ω * Y j ω ∂P) =
        ∫⁻ ω, (E i ∩ E j).indicator
          (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
            exact congrArg
              (fun f : Ω → ℝ≥0∞ => ∫⁻ ω, f ω ∂P) (hProd i j)
      _ = P (E i ∩ E j) :=
        MeasureTheory.lintegral_indicator_one ((hE i).inter (hE j))
  have hPair (i j : ℕ) (hij : i < j) :
      P (E i ∩ E j) = P (E i) * P (E j) := by
    have h := avram_wave6_01_original_past_two_separated_marked_increment_cells_probability_product
      X 0 (t i) (t (i + 1)) (t j) (t (j + 1))
        (by positivity) (ht (Nat.le_succ i))
        (ht (Nat.succ_le_of_lt hij)) (ht (Nat.le_succ j))
        Set.univ MeasurableSet.univ B B hB hB
    simpa [E] using h
  have hCellPair (i j : ℕ) :
      (∫⁻ ω, Y i ω * Y j ω ∂P) =
        if i = j then P (E i) else P (E i) * P (E j) := by
    rw [hProdMean]
    by_cases hij : i = j
    · subst j
      simp
    · simp only [if_neg hij]
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact hPair i j hlt
      · rw [Set.inter_comm, hPair j i hgt, mul_comm]
  have hProdMeas (i j : ℕ) :
      Measurable (fun ω : Ω => Y i ω * Y j ω) :=
    (hY i).mul (hY j)
  have hSquare (ω : Ω) :
      (∑ i ∈ S, Y i ω) ^ 2 =
        ∑ i ∈ S, ∑ j ∈ S, Y i ω * Y j ω := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  change (∫⁻ ω, (∑ i ∈ S, Y i ω) ^ 2 ∂P) =
    ∑ i ∈ S, ∑ j ∈ S,
      if i = j then P (E i) else P (E i) * P (E j)
  calc
    (∫⁻ ω, (∑ i ∈ S, Y i ω) ^ 2 ∂P) =
        ∫⁻ ω, ∑ i ∈ S, ∑ j ∈ S,
          Y i ω * Y j ω ∂P := by
            exact congrArg
              (fun f : Ω → ℝ≥0∞ => ∫⁻ ω, f ω ∂P)
              (funext (fun ω => hSquare ω))
    _ = ∑ i ∈ S, ∫⁻ ω, ∑ j ∈ S, Y i ω * Y j ω ∂P := by
      apply MeasureTheory.lintegral_finset_sum
      intro i hi
      apply Finset.measurable_sum
      intro j hj
      exact hProdMeas i j
    _ = ∑ i ∈ S, ∑ j ∈ S,
        (∫⁻ ω, Y i ω * Y j ω ∂P) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply MeasureTheory.lintegral_finset_sum
      intro j hj
      exact hProdMeas i j
    _ = ∑ i ∈ S, ∑ j ∈ S,
        if i = j then P (E i) else P (E i) * P (E j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hCellPair i j
