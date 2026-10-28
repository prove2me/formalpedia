-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_grid_binomial_complete_pattern_mass_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:43:27.781258+00:00
-- url     : https://prove2.me/submissions/84d77a8b-25dc-4dfb-9c71-5e3bf752a4d8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_uniform_grid_pattern_real_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_binary_patterns_pairwise_disjoint_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_binomial_pattern_sum_ws01b

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n k : ℕ) (h : ℝ)
    (hgap : ∀ i : ℕ, i < n →
      (((t (i + 1) - t i : ℝ≥0) : ℝ)) = h) :
    P.real {ω : Ω | ∃ S ∈ Finset.powersetCard k (Finset.range n),
      ∀ i : ℕ, i < n →
        X.X (t (i + 1)) ω - X.X (t i) ω ∈
          (if i ∈ S then
            Iio (X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))
          else
            {X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))})} =
      (Nat.choose n k : ℝ) *
        (1 - Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal))) ^ k *
        (Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal))) ^ (n - k) := by
  have hP : IsProbabilityMeasure P := X.isProbability
  set A : ℕ → Set Ω := fun i => {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈
    Iio (X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))}
  set B : ℕ → Set Ω := fun i => {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈
    ({X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))} : Set ℝ)}
  set E : Finset ℕ → Set Ω := fun S => {ω : Ω | ∀ i : ℕ, i < n →
    if i ∈ S then ω ∈ A i else ω ∈ B i}
  have hE : ∀ S, E S = {ω : Ω | ∀ i : ℕ, i < n →
      X.X (t (i + 1)) ω - X.X (t i) ω ∈
        (if i ∈ S then
          Iio (X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))
        else
          {X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))})} := by
    intro S; ext ω
    simp only [E, A, B, Set.mem_ofPred_eq]
    refine forall₂_congr fun i _ => ?_
    split_ifs <;> rfl
  have hset : {ω : Ω | ∃ S ∈ Finset.powersetCard k (Finset.range n),
      ∀ i : ℕ, i < n →
        X.X (t (i + 1)) ω - X.X (t i) ω ∈
          (if i ∈ S then
            Iio (X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))
          else
            {X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))})} =
      ⋃ S ∈ Finset.powersetCard k (Finset.range n), E S := by
    ext ω; simp only [hE, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  have hmX : ∀ s, Measurable (X.X s) := fun s =>
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hinc : ∀ i, Measurable fun ω => X.X (t (i + 1)) ω - X.X (t i) ω := fun i =>
    (hmX _).sub (hmX _)
  have hmeas : ∀ S, MeasurableSet (E S) := by
    intro S
    have : E S = ⋂ i ∈ Finset.range n, (if i ∈ S then A i else B i) := by
      ext ω; simp only [E, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
      refine forall₂_congr fun i _ => ?_
      split_ifs <;> rfl
    rw [this]
    refine Finset.measurableSet_biInter _ fun i _ => ?_
    split_ifs
    · exact hinc i measurableSet_Iio
    · exact hinc i (measurableSet_singleton _)
  have hdisj := AvramDividend.Classical.bv_binary_patterns_pairwise_disjoint_ws01b A B n k
    (fun i _ ω hA hB => by
      simp only [A, B, Set.mem_ofPred_eq, Set.mem_Iio, Set.mem_singleton_iff] at hA hB
      rw [hB] at hA; exact lt_irrefl _ hA)
  rw [hset, measureReal_biUnion_finset hdisj (fun S _ => hmeas S)]
  rw [← AvramDividend.Classical.bv_binomial_pattern_sum_ws01b]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [show {ω | ∀ i < n, if i ∈ S then ω ∈ A i else ω ∈ B i} = E S from rfl, hE]
  exact AvramDividend.Classical.bv_actual_uniform_grid_pattern_real_ws01b X hBV hFinite t ht n S h hgap
