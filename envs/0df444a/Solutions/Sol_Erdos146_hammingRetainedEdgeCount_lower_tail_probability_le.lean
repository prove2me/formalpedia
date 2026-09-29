-- Prove2me | solution 1 for Erdos146.hammingRetainedEdgeCount_lower_tail_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:38:49.786955+00:00
-- url     : https://prove2.me/submissions/d07b4aac-8133-44f1-ba9a-43c04a60c010

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.InformationTheory.Hamming
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_Erdos146_hammingExpectedRetainedEdgeCount_eq
import Theorems.Thm_Erdos146_hammingRetainedEdgeCount_integral_eq
import Theorems.Thm_Erdos146_hammingRetentionMeasure_integrable
import Theorems.Thm_Erdos146_hammingRetentionMeasure_integral_eq_sum
import Theorems.Thm_Erdos146_hammingRetentionMeasure_isProbability
import Theorems.Thm_Erdos146_hammingRetentionMeasure_memLp_two
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_contains_finset
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_deviation_le
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_event_eq_sum
import Theorems.Thm_Erdos146_hammingWordEdgePairSharedLeft_sum_const
import Theorems.Thm_Erdos146_hammingWordEdge_sum_const

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem hammingRetentionMeasure_real_contains_edgePair
    (dimension : ℕ)
    (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} =
      hammingRetentionProbability dimension ^
        (2 +
          (if firstLeft = secondLeft then 0 else 1) +
          (if firstRight = secondRight then 0 else 1)) := by
  classical
  let required : Finset (Bool × HammingWord dimension) :=
    {(false, firstLeft), (true, firstRight),
      (false, secondLeft), (true, secondRight)}
  have hevent :
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} =
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ required, vertex ∈ retained} := by
    ext retained
    simp [required, and_left_comm]
  rw [hevent, hammingRetentionMeasure_real_contains_finset]
  by_cases hleft : firstLeft = secondLeft <;>
    by_cases hright : firstRight = secondRight
  · subst secondLeft
    subst secondRight
    simp [required]
  · subst secondLeft
    simp [required, hright]
  · subst secondRight
    simp [required, hleft]
  · simp [required, hleft, hright]

theorem hammingRetentionMeasure_real_contains_edgePair_le
    (dimension : ℕ)
    (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} ≤
      hammingRetentionProbability dimension ^ 4 +
        (if firstLeft = secondLeft then
          hammingRetentionProbability dimension ^ 3 else 0) +
        (if firstRight = secondRight then
          hammingRetentionProbability dimension ^ 3 else 0) +
        (if firstLeft = secondLeft ∧ firstRight = secondRight then
          hammingRetentionProbability dimension ^ 2 else 0) := by
  rw [hammingRetentionMeasure_real_contains_edgePair]
  have hnonnegative := (hammingRetentionProbability_pos dimension).le
  by_cases hleft : firstLeft = secondLeft <;>
    by_cases hright : firstRight = secondRight <;>
    simp only [hleft, hright, ↓reduceIte, add_zero, Nat.reduceAdd,
      and_self, and_false, and_true, le_add_iff_nonneg_left, ge_iff_le,
      Std.le_refl] <;>
    positivity

theorem hammingWordEdgePair_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              weight
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) ^ 2 *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
  classical
  have hinner (firstLeft firstRight : HammingWord dimension) :
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            weight
          else 0) =
        if hammingDist firstLeft firstRight ≤ radius then
          ((2 ^ dimension : ℕ) : ℝ) *
            ((∑ distance ∈ Finset.range (radius + 1),
              dimension.choose distance : ℕ) : ℝ) * weight
        else 0 := by
    by_cases hedge : hammingDist firstLeft firstRight ≤ radius
    · simp only [hedge, true_and, if_true]
      exact hammingWordEdge_sum_const dimension radius weight
    · simp [hedge]
  simp_rw [hinner]
  rw [hammingWordEdge_sum_const]
  ring

theorem hammingWordEdgePairSharedRight_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstRight = secondRight then weight else 0
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
  classical
  calc
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstRight = secondRight then weight else 0
            else 0) =
      (∑ firstRight : HammingWord dimension,
        ∑ firstLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            ∑ secondLeft : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if firstRight = secondRight then weight else 0
              else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro firstRight _
        apply Finset.sum_congr rfl
        intro firstLeft _
        rw [Finset.sum_comm]
    _ = ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
      simpa only [hammingDist_comm] using
        hammingWordEdgePairSharedLeft_sum_const dimension radius weight

theorem hammingWordEdgePairIdentical_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstLeft = secondLeft ∧ firstRight = secondRight then
                weight else 0
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) * weight := by
  classical
  calc
    _ = ∑ firstLeft : HammingWord dimension,
          ∑ firstRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius then weight else 0 := by
      apply Finset.sum_congr rfl
      intro firstLeft _
      apply Finset.sum_congr rfl
      intro firstRight _
      by_cases hedge : hammingDist firstLeft firstRight ≤ radius
      · simp only [hedge, true_and, if_true]
        have hpoint (secondLeft secondRight : HammingWord dimension) :
            (if hammingDist secondLeft secondRight ≤ radius then
              if firstLeft = secondLeft ∧ firstRight = secondRight then
                weight else 0
            else 0) =
              if firstLeft = secondLeft then
                if firstRight = secondRight then weight else 0
              else 0 := by
          split_ifs <;> simp_all
        simp_rw [hpoint]
        simp
      · simp [hedge]
    _ = _ := hammingWordEdge_sum_const dimension radius weight

theorem hammingExpectedRetainedEdgeCount_pos
    (dimension radius : ℕ) :
    0 < hammingExpectedRetainedEdgeCount dimension radius := by
  have hterm :
      1 ≤ ∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance := by
    have hzero := Finset.single_le_sum
      (s := Finset.range (radius + 1))
      (f := fun distance : ℕ => dimension.choose distance)
      (fun distance _ => Nat.zero_le _)
      (show 0 ∈ Finset.range (radius + 1) by simp)
    simpa using hzero
  have hdegree :
      0 < ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < ∑ distance ∈ Finset.range (radius + 1),
      dimension.choose distance by omega)
  rw [hammingExpectedRetainedEdgeCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  positivity

theorem hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius ≤
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                hammingRetentionProbability dimension ^ 4 +
                  (if firstLeft = secondLeft then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstLeft = secondLeft ∧
                      firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 2 else 0)
              else 0 := by
  unfold hammingExpectedRetainedEdgeSquare
  apply Finset.sum_le_sum
  intro firstLeft _
  apply Finset.sum_le_sum
  intro firstRight _
  apply Finset.sum_le_sum
  intro secondLeft _
  apply Finset.sum_le_sum
  intro secondRight _
  by_cases hedge :
      hammingDist firstLeft firstRight ≤ radius ∧
        hammingDist secondLeft secondRight ≤ radius
  · simp only [hedge]
    exact hammingRetentionMeasure_real_contains_edgePair_le
      dimension firstLeft firstRight secondLeft secondRight
  · simp [hedge]

theorem hammingExpectedRetainedEdgeSquare_le
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius ≤
      hammingExpectedRetainedEdgeCount dimension radius ^ 2 +
        hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  classical
  have hpoint
      (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
      (if hammingDist firstLeft firstRight ≤ radius ∧
          hammingDist secondLeft secondRight ≤ radius then
        hammingRetentionProbability dimension ^ 4 +
          (if firstLeft = secondLeft then
            hammingRetentionProbability dimension ^ 3 else 0) +
          (if firstRight = secondRight then
            hammingRetentionProbability dimension ^ 3 else 0) +
          (if firstLeft = secondLeft ∧ firstRight = secondRight then
            hammingRetentionProbability dimension ^ 2 else 0)
      else 0) =
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          hammingRetentionProbability dimension ^ 4 else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstLeft = secondLeft then
            hammingRetentionProbability dimension ^ 3 else 0
        else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstRight = secondRight then
            hammingRetentionProbability dimension ^ 3 else 0
        else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstLeft = secondLeft ∧ firstRight = secondRight then
            hammingRetentionProbability dimension ^ 2 else 0
        else 0) := by
    split <;> simp
  calc
    hammingExpectedRetainedEdgeSquare dimension radius ≤
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                hammingRetentionProbability dimension ^ 4 +
                  (if firstLeft = secondLeft then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstLeft = secondLeft ∧ firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 2 else 0)
              else 0 :=
        hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition
          dimension radius
    _ = hammingExpectedRetainedEdgeCount dimension radius ^ 2 +
        hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
      simp_rw [hpoint, Finset.sum_add_distrib]
      rw [hammingWordEdgePair_sum_const,
        hammingWordEdgePairSharedLeft_sum_const,
        hammingWordEdgePairSharedRight_sum_const,
        hammingWordEdgePairIdentical_sum_const,
        hammingExpectedRetainedEdgeCount_eq]
      ring

theorem hammingExpectedRetainedEdgeVariance_le
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2 ≤
      hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  have hsecond := hammingExpectedRetainedEdgeSquare_le dimension radius
  linarith

open Classical in
theorem hammingRetainedEdgeCount_sq
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedEdgeCount dimension radius retained ^ 2 =
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if (false, firstLeft) ∈ retained ∧
                    (true, firstRight) ∈ retained ∧
                    (false, secondLeft) ∈ retained ∧
                    (true, secondRight) ∈ retained
                then (1 : ℝ) else 0
              else 0 := by
  classical
  unfold hammingRetainedEdgeCount
  rw [pow_two, Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro firstLeft _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstRight _
  apply Finset.sum_congr rfl
  intro secondLeft _
  apply Finset.sum_congr rfl
  intro secondRight _
  by_cases hfirst_edge : hammingDist firstLeft firstRight ≤ radius <;>
    by_cases hsecond_edge : hammingDist secondLeft secondRight ≤ radius <;>
    by_cases hfirst_left : (false, firstLeft) ∈ retained <;>
    by_cases hfirst_right : (true, firstRight) ∈ retained <;>
    by_cases hsecond_left : (false, secondLeft) ∈ retained <;>
    by_cases hsecond_right : (true, secondRight) ∈ retained <;>
    simp [hfirst_edge, hsecond_edge, hfirst_left, hfirst_right,
      hsecond_left, hsecond_right]

theorem hammingRetainedEdgeCount_sq_integral_eq
    (dimension radius : ℕ) :
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained ^ 2
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeSquare dimension radius := by
  classical
  simp_rw [hammingRetainedEdgeCount_sq]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun firstLeft _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if (false, firstLeft) ∈ retained ∧
                    (true, firstRight) ∈ retained ∧
                    (false, secondLeft) ∈ retained ∧
                    (true, secondRight) ∈ retained
                then (1 : ℝ) else 0
              else 0))]
  unfold hammingExpectedRetainedEdgeSquare
  apply Finset.sum_congr rfl
  intro firstLeft _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun firstRight _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if (false, firstLeft) ∈ retained ∧
                  (true, firstRight) ∈ retained ∧
                  (false, secondLeft) ∈ retained ∧
                  (true, secondRight) ∈ retained
              then (1 : ℝ) else 0
            else 0))]
  apply Finset.sum_congr rfl
  intro firstRight _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun secondLeft _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            if (false, firstLeft) ∈ retained ∧
                (true, firstRight) ∈ retained ∧
                (false, secondLeft) ∈ retained ∧
                (true, secondRight) ∈ retained
            then (1 : ℝ) else 0
          else 0))]
  apply Finset.sum_congr rfl
  intro secondLeft _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun secondRight _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if (false, firstLeft) ∈ retained ∧
              (true, firstRight) ∈ retained ∧
              (false, secondLeft) ∈ retained ∧
              (true, secondRight) ∈ retained
          then (1 : ℝ) else 0
        else 0))]
  apply Finset.sum_congr rfl
  intro secondRight _
  by_cases hedge :
      hammingDist firstLeft firstRight ≤ radius ∧
        hammingDist secondLeft secondRight ≤ radius
  · simp only [hedge]
    rw [hammingRetentionMeasure_integral_eq_sum,
      hammingRetentionMeasure_real_event_eq_sum]
    apply Finset.sum_congr rfl
    intro retained _
    by_cases hretained :
        (false, firstLeft) ∈ retained ∧
          (true, firstRight) ∈ retained ∧
          (false, secondLeft) ∈ retained ∧
          (true, secondRight) ∈ retained <;>
      simp [hretained]
  · simp [hedge]

theorem hammingRetainedEdgeCount_variance_eq
    (dimension radius : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedEdgeCount dimension radius)
        (hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  rw [ProbabilityTheory.variance_eq_sub
    (hammingRetentionMeasure_memLp_two dimension
      (hammingRetainedEdgeCount dimension radius))]
  change
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained ^ 2
        ∂hammingRetentionMeasure dimension) -
      (∫ retained,
        hammingRetainedEdgeCount dimension radius retained
          ∂hammingRetentionMeasure dimension) ^ 2 =
      hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2
  rw [hammingRetainedEdgeCount_sq_integral_eq,
    hammingRetainedEdgeCount_integral_eq]

theorem hammingRetainedEdgeCount_variance_le
    (dimension radius : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedEdgeCount dimension radius)
        (hammingRetentionMeasure dimension) ≤
      hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  rw [hammingRetainedEdgeCount_variance_eq]
  exact hammingExpectedRetainedEdgeVariance_le dimension radius

theorem hammingRetainedEdgeCount_deviation_probability_le
    (dimension radius : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} ≤
      (hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        threshold ^ 2 := by
  have hchebyshev := hammingRetentionMeasure_real_deviation_le
    dimension (hammingRetainedEdgeCount dimension radius)
    threshold hthreshold
  rw [hammingRetainedEdgeCount_integral_eq] at hchebyshev
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} ≤
      ProbabilityTheory.variance
          (hammingRetainedEdgeCount dimension radius)
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := hchebyshev
    _ ≤
      (hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        threshold ^ 2 := by
      gcongr
      exact hammingRetainedEdgeCount_variance_le dimension radius

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension radius : ℕ) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ≤
      4 / hammingExpectedRetainedEdgeCount dimension radius +
        8 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hmean := hammingExpectedRetainedEdgeCount_pos dimension radius
  have hthreshold :
      0 < hammingExpectedRetainedEdgeCount dimension radius / 2 := by
    positivity
  have hchebyshev := hammingRetainedEdgeCount_deviation_probability_le
    dimension radius
    (hammingExpectedRetainedEdgeCount dimension radius / 2)
    hthreshold
  have hsubset :
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ⊆
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedEdgeCount dimension radius / 2 ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} := by
    intro retained hretained
    change
      hammingExpectedRetainedEdgeCount dimension radius / 2 ≤
        |hammingRetainedEdgeCount dimension radius retained -
          hammingExpectedRetainedEdgeCount dimension radius|
    have habsolute := neg_le_abs
      (hammingRetainedEdgeCount dimension radius retained -
        hammingExpectedRetainedEdgeCount dimension radius)
    change
      hammingRetainedEdgeCount dimension radius retained <
        hammingExpectedRetainedEdgeCount dimension radius / 2 at hretained
    linarith
  have hdegree_positive :
      0 < ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) := by
    have hterm :
        1 ≤ ∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance := by
      have hzero := Finset.single_le_sum
        (s := Finset.range (radius + 1))
        (f := fun distance : ℕ => dimension.choose distance)
        (fun distance _ => Nat.zero_le _)
        (show 0 ∈ Finset.range (radius + 1) by simp)
      simpa using hzero
    exact_mod_cast (show 0 < ∑ distance ∈ Finset.range (radius + 1),
      dimension.choose distance by omega)
  have hprobability := hammingRetentionProbability_pos dimension
  have hwords : 0 < ((2 ^ dimension : ℕ) : ℝ) := by
    positivity
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ≤
      (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedEdgeCount dimension radius / 2 ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} :=
        MeasureTheory.measureReal_mono hsubset
    _ ≤
      (hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        (hammingExpectedRetainedEdgeCount dimension radius / 2) ^ 2 :=
      hchebyshev
    _ = 4 / hammingExpectedRetainedEdgeCount dimension radius +
        8 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
      rw [hammingExpectedRetainedEdgeCount_eq]
      field_simp [hprobability.ne', hwords.ne', hdegree_positive.ne']
      ring
