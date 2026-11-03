-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_past_marked_grid_count_exact_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:21:00.965865+00:00
-- url     : https://prove2.me/submissions/64841fd0-abd3-4c2f-bfe7-160cf8fe4002

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_event_next_levy_increment_measure_product
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_two_separated_marked_increment_cells_probability_product
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_count_exact_second_moment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Original past events factor from the full source marked-grid quadratic moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t) (hst : s ≤ t 0)
    (n : ℕ) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω,
      (A.indicator (fun _ => (1 : ℝ≥0∞)) ω) *
      (∑ i ∈ Finset.range n,
        ({v : Ω | X.X (t (i + 1)) v - X.X (t i) v ∈ B}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) =
    P A * (∫⁻ ω,
      (∑ i ∈ Finset.range n,
        ({v : Ω | X.X (t (i + 1)) v - X.X (t i) v ∈ B}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) := by
  classical
  haveI := X.isProbability
  let S : Finset ℕ := Finset.range n
  let E : ℕ → Set Ω := fun i =>
    {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}
  let Y : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    (E i).indicator (fun _ => (1 : ℝ≥0∞)) ω
  let Z : Ω → ℝ≥0∞ := A.indicator (fun _ => (1 : ℝ≥0∞))
  have hXm (u : ℝ≥0) : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  have hE (i : ℕ) : MeasurableSet (E i) :=
    hB.preimage ((hXm _).sub (hXm _))
  have hY (i : ℕ) : Measurable (Y i) :=
    measurable_const.indicator (hE i)
  have hAambient : MeasurableSet A := (𝓕.le s) A hA
  have hZ : Measurable Z := measurable_const.indicator hAambient
  have hTriple (i j : ℕ) :
      (fun ω : Ω => Z ω * (Y i ω * Y j ω)) =
        (A ∩ (E i ∩ E j)).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hi : ω ∈ E i <;>
      by_cases hj : ω ∈ E j <;> simp [Y, Z, ha, hi, hj]
  have hTripleMean (i j : ℕ) :
      (∫⁻ ω, Z ω * (Y i ω * Y j ω) ∂P) =
        P (A ∩ (E i ∩ E j)) := by
    calc
      (∫⁻ ω, Z ω * (Y i ω * Y j ω) ∂P) =
        ∫⁻ ω, (A ∩ (E i ∩ E j)).indicator
          (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
            exact congrArg
              (fun f : Ω → ℝ≥0∞ => ∫⁻ ω, f ω ∂P)
              (hTriple i j)
      _ = P (A ∩ (E i ∩ E j)) :=
        MeasureTheory.lintegral_indicator_one
          (hAambient.inter ((hE i).inter (hE j)))
  have hPastCell (i : ℕ) :
      P (A ∩ E i) = P A * P (E i) := by
    have hsi : s ≤ t i := hst.trans (ht (Nat.zero_le i))
    have hAi : MeasurableSet[𝓕 (t i)] A := (𝓕.mono hsi) A hA
    exact chat04_past_event_next_levy_increment_measure_product
      X (t i) (t (i + 1)) (ht (Nat.le_succ i)) A hAi B hB
  have hPastPair (i j : ℕ) (hij : i < j) :
      P (A ∩ (E i ∩ E j)) = P A * P (E i) * P (E j) := by
    have hsi : s ≤ t i := hst.trans (ht (Nat.zero_le i))
    have h := avram_wave6_01_original_past_two_separated_marked_increment_cells_probability_product
      X s (t i) (t (i + 1)) (t j) (t (j + 1))
        hsi (ht (Nat.le_succ i))
        (ht (Nat.succ_le_of_lt hij)) (ht (Nat.le_succ j))
        A hA B B hB hB
    simpa [E] using h
  have hCell (i j : ℕ) :
      (∫⁻ ω, Z ω * (Y i ω * Y j ω) ∂P) =
        P A * (if i = j then P (E i) else P (E i) * P (E j)) := by
    rw [hTripleMean]
    by_cases hij : i = j
    · subst j
      simp only [if_pos rfl]
      rw [Set.inter_self]
      exact hPastCell i
    · simp only [if_neg hij]
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · rw [hPastPair i j hlt]
        rw [mul_assoc]
      · rw [Set.inter_comm (E i) (E j), hPastPair j i hgt]
        ac_rfl
  have hProdMeas (i j : ℕ) :
      Measurable (fun ω : Ω => Z ω * (Y i ω * Y j ω)) :=
    hZ.mul ((hY i).mul (hY j))
  have hSquare (ω : Ω) :
      (∑ i ∈ S, Y i ω) ^ 2 =
        ∑ i ∈ S, ∑ j ∈ S, Y i ω * Y j ω := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hExpand (ω : Ω) :
      Z ω * (∑ i ∈ S, Y i ω) ^ 2 =
        ∑ i ∈ S, ∑ j ∈ S, Z ω * (Y i ω * Y j ω) := by
    rw [hSquare]
    simp only [Finset.mul_sum]
  change (∫⁻ ω, Z ω * (∑ i ∈ S, Y i ω) ^ 2 ∂P) =
    P A * (∫⁻ ω, (∑ i ∈ S, Y i ω) ^ 2 ∂P)
  calc
    (∫⁻ ω, Z ω * (∑ i ∈ S, Y i ω) ^ 2 ∂P) =
        ∫⁻ ω, ∑ i ∈ S, ∑ j ∈ S,
          Z ω * (Y i ω * Y j ω) ∂P := by
            exact congrArg
              (fun f : Ω → ℝ≥0∞ => ∫⁻ ω, f ω ∂P)
              (funext (fun ω => hExpand ω))
    _ = ∑ i ∈ S, ∫⁻ ω, ∑ j ∈ S,
        Z ω * (Y i ω * Y j ω) ∂P := by
          apply MeasureTheory.lintegral_finset_sum
          intro i hi
          apply Finset.measurable_sum
          intro j hj
          exact hProdMeas i j
    _ = ∑ i ∈ S, ∑ j ∈ S,
        (∫⁻ ω, Z ω * (Y i ω * Y j ω) ∂P) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply MeasureTheory.lintegral_finset_sum
          intro j hj
          exact hProdMeas i j
    _ = ∑ i ∈ S, ∑ j ∈ S,
        P A * (if i = j then P (E i) else P (E i) * P (E j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hCell i j
    _ = P A * (∑ i ∈ S, ∑ j ∈ S,
        if i = j then P (E i) else P (E i) * P (E j)) := by
          simp only [Finset.mul_sum]
    _ = P A * (∫⁻ ω, (∑ i ∈ S, Y i ω) ^ 2 ∂P) := by
          rw [avram_wave6_01_original_borel_marked_grid_count_exact_second_moment
            X t ht n B hB]
