-- Prove2me | solution 1 for ConsistentSubmodular.HardInstance.realization_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:26.273199+00:00
-- url     : https://prove2.me/submissions/dfe696b0-19c2-4be7-aafe-cee58e3f0d2c

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardInstance
import Theorems.Thm_ConsistentSubmodular_HardInstance_tinyCount_sum_le
import Theorems.Thm_ConsistentSubmodular_HardInstance_value_le_before
import Theorems.Thm_ConsistentSubmodular_HardInstance_value_le_middle
import Theorems.Thm_ConsistentSubmodular_HardInstance_value_le_after

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.HardInstance

/-- A tiny set of `T'` is a tiny set of `T` or an insertion of `T' \ T`. -/
theorem tinyCount_le_add {k : ℕ} (T T' : Finset (Fin (3 * k + 2))) (g : Fin 3) :
    tinyCount k g T' ≤ tinyCount k g T + tinyCount k g (T' \ T) := by
  unfold tinyCount
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro e he
  obtain ⟨heT', hp⟩ := mem_filter.mp he
  by_cases heT : e ∈ T
  · exact mem_union_left _ (mem_filter.mpr ⟨heT, hp⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨heT', heT⟩, hp⟩)

/-- The insertions number at most the recourse. -/
theorem card_sdiff_le_recourse {n : ℕ} (T T' : Finset (Fin n)) : (T' \ T).card ≤ recourse T' T :=
  card_le_card subset_union_left

/-- The insertions of tiny sets of groups `1` and `2` number at most the recourse. -/
theorem tinyCount_sdiff_le {k : ℕ} (T T' : Finset (Fin (3 * k + 2))) :
    tinyCount k 1 (T' \ T) + tinyCount k 2 (T' \ T) ≤ recourse T' T := by
  refine le_trans ?_ (card_sdiff_le_recourse T T')
  unfold tinyCount
  rw [← card_union_of_disjoint]
  · exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  · rw [disjoint_filter]
    intro e _ h1 h2
    exact absurd (h1.2.symm.trans h2.2) (by decide)

end ConsistentSubmodular.HardInstance

end

end

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance

theorem solution {k C : ℕ} {u : Fin 3 → ℝ} (hu : ∀ g, 0 ≤ u g)
    (hu21 : u 2 ≤ u 1) {S : Fin (3 * k + 2 + 1) → Finset (Fin (3 * k + 2))}
    (hS : FeasibleTrajectory k C S) :
    weightedValue k u (S (timeBefore k)) ≤
        u 0 * tinyCount k 0 (S (timeBefore k)) + u 1 * tinyCount k 1 (S (timeBefore k)) +
          u 2 * tinyCount k 2 (S (timeBefore k)) ∧
      weightedValue k u (S (timeMiddle k)) ≤
        u 0 * k + u 1 * C + u 1 * tinyCount k 1 (S (timeBefore k)) +
          u 2 * tinyCount k 2 (S (timeBefore k)) ∧
      weightedValue k u (S (timeAfter k)) ≤
        u 0 * k + u 1 * k + 2 * u 2 * C + u 2 * tinyCount k 2 (S (timeBefore k)) ∧
      (tinyCount k 0 (S (timeBefore k)) : ℝ) + tinyCount k 1 (S (timeBefore k)) +
        tinyCount k 2 (S (timeBefore k)) ≤ k := by
  obtain ⟨-, hsets, hrec⟩ := hS
  have hrec₁ : recourse (S (timeMiddle k)) (S (timeBefore k)) ≤ C := hrec ⟨3 * k, by omega⟩
  have hrec₂ : recourse (S (timeAfter k)) (S (timeMiddle k)) ≤ C := hrec ⟨3 * k + 1, by omega⟩
  have hbefore : ∀ e ∈ S (timeBefore k), e.val < 3 * k := fun e he =>
    (mem_filter.mp ((hsets (timeBefore k)).1 he)).2
  have hmiddle : ∀ e ∈ S (timeMiddle k), e.val < 3 * k + 1 := fun e he =>
    (mem_filter.mp ((hsets (timeMiddle k)).1 he)).2
  -- Counts of the insertions at the two updates.
  have a₁ := tinyCount_le_add (S (timeBefore k)) (S (timeMiddle k)) 1
  have a₂ := tinyCount_le_add (S (timeBefore k)) (S (timeMiddle k)) 2
  have a₁₂ := (tinyCount_sdiff_le (S (timeBefore k)) (S (timeMiddle k))).trans hrec₁
  have b₂ := tinyCount_le_add (S (timeMiddle k)) (S (timeAfter k)) 2
  have b₁₂ := (tinyCount_sdiff_le (S (timeMiddle k)) (S (timeAfter k))).trans hrec₂
  have hcard := (tinyCount_sum_le (S (timeBefore k))).trans (hsets (timeBefore k)).2
  have hw1R : 0 ≤ u 1 := hu 1
  have hw2R : 0 ≤ u 2 := hu 2
  refine ⟨value_le_before hu _ hbefore, ?_, ?_, by exact_mod_cast hcard⟩
  · have hcov := value_le_middle hu _ hmiddle
    have ha₁ : (tinyCount k 1 (S (timeMiddle k)) : ℝ) ≤ tinyCount k 1 (S (timeBefore k)) +
        tinyCount k 1 (S (timeMiddle k) \ S (timeBefore k)) := by exact_mod_cast a₁
    have ha₂ : (tinyCount k 2 (S (timeMiddle k)) : ℝ) ≤ tinyCount k 2 (S (timeBefore k)) +
        tinyCount k 2 (S (timeMiddle k) \ S (timeBefore k)) := by exact_mod_cast a₂
    have ha₁₂ : (tinyCount k 1 (S (timeMiddle k) \ S (timeBefore k)) : ℝ) +
        tinyCount k 2 (S (timeMiddle k) \ S (timeBefore k)) ≤ C := by exact_mod_cast a₁₂
    have h1 := mul_le_mul_of_nonneg_left ha₁ hw1R
    have h2 := mul_le_mul_of_nonneg_left ha₂ hw2R
    have h3 := mul_le_mul_of_nonneg_right hu21
      (Nat.cast_nonneg (tinyCount k 2 (S (timeMiddle k) \ S (timeBefore k))) : (0 : ℝ) ≤ _)
    have h4 := mul_le_mul_of_nonneg_left ha₁₂ hw1R
    linarith
  · have hcov := value_le_after hu (S (timeAfter k))
    have ha₂ : (tinyCount k 2 (S (timeMiddle k)) : ℝ) ≤ tinyCount k 2 (S (timeBefore k)) +
        tinyCount k 2 (S (timeMiddle k) \ S (timeBefore k)) := by exact_mod_cast a₂
    have ha₁₂ : (tinyCount k 1 (S (timeMiddle k) \ S (timeBefore k)) : ℝ) +
        tinyCount k 2 (S (timeMiddle k) \ S (timeBefore k)) ≤ C := by exact_mod_cast a₁₂
    have hb₂ : (tinyCount k 2 (S (timeAfter k)) : ℝ) ≤ tinyCount k 2 (S (timeMiddle k)) +
        tinyCount k 2 (S (timeAfter k) \ S (timeMiddle k)) := by exact_mod_cast b₂
    have hb₁₂ : (tinyCount k 1 (S (timeAfter k) \ S (timeMiddle k)) : ℝ) +
        tinyCount k 2 (S (timeAfter k) \ S (timeMiddle k)) ≤ C := by exact_mod_cast b₁₂
    have hc₁ : (0 : ℝ) ≤ tinyCount k 1 (S (timeMiddle k) \ S (timeBefore k)) :=
      Nat.cast_nonneg _
    have hc₁' : (0 : ℝ) ≤ tinyCount k 1 (S (timeAfter k) \ S (timeMiddle k)) :=
      Nat.cast_nonneg _
    have htwo : (tinyCount k 2 (S (timeAfter k)) : ℝ) ≤
        tinyCount k 2 (S (timeBefore k)) + 2 * C := by linarith
    have h := mul_le_mul_of_nonneg_left htwo hw2R
    linarith

end
