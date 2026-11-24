-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.bracket
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:26.393833+00:00
-- url     : https://prove2.me/submissions/a4342111-338d-46c6-9f18-f3d7b11af998

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_sum_drop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
theorem _root_.solution (h31 : LogBinomialProperties) (h34 : LogBinomialDeficit) (k' K : ℕ) (la : ℕ → ℤ) (lst : List ℕ) (hk : 1 ≤ k')
    (h1 : ∀ l, l < lst.length → k' ≤ lst.getD l 0)
    (h2 : ∀ l, l + 1 < lst.length → 4 * lst.getD (l + 1) 0 ≤ lst.getD l 0)
    (h3 : ∀ u, tailPos K la u ≤ ((lst.drop u).sum : ℕ)) :
    (∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ)) -
      (∑ l ∈ range lst.length, fT k' ((lst.getD l 0 : ℕ) : ℝ)) ≤ 0 ∧
    ∀ (u₀ : ℕ) (X : ℝ), 0 < X → ((tailPos K la u₀ : ℤ) : ℝ) ≤ (((lst.drop u₀).sum : ℕ) : ℝ) - X →
      u₀ < lst.length ∧
      (∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ)) -
        (∑ l ∈ range lst.length, fT k' ((lst.getD l 0 : ℕ) : ℝ)) ≤
          -(X * k' / (4 * ((lst.getD u₀ 0 : ℕ) : ℝ))) := by
  classical
  have F0 : fT k' 0 = 0 := (h31 k').1
  have hnn : ∀ m, (0 : ℝ) ≤ ((max (la m) 0 : ℤ) : ℝ) := fun m => by exact_mod_cast le_max_right (la m) 0

  have hbeyond : ∀ m, m < K → lst.length ≤ m → max (la m) 0 = 0 := by
    intro m hmK hmL
    have h := h3 lst.length
    rw [List.drop_length] at h
    have h0 : tailPos K la lst.length ≤ 0 := by simpa using h
    have hsub : max (la m) 0 ≤ tailPos K la lst.length := by
      unfold tailPos
      exact Finset.single_le_sum (f := fun m => max (la m) 0) (fun i _ => le_max_right _ _)
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmK, hmL⟩)
    exact le_antisymm (le_trans hsub h0) (le_max_right _ _)
  let al : ℕ → ℝ := fun l => if l < K then ((max (la l) 0 : ℤ) : ℝ) else 0
  let Bs : ℕ → ℝ := fun l => ((lst.getD l 0 : ℕ) : ℝ)
  have hal : ∀ l, al l = if l < K then ((max (la l) 0 : ℤ) : ℝ) else 0 := fun l => rfl
  have hBs : ∀ l, Bs l = ((lst.getD l 0 : ℕ) : ℝ) := fun l => rfl
  have hal0 : ∀ l, 0 ≤ al l := by
    intro l
    rw [hal]
    split_ifs
    · exact hnn l
    · exact le_refl 0
  have halK : ∀ l, K ≤ l → al l = 0 := by
    intro l hl
    rw [hal, if_neg (by omega)]
  have halL : ∀ l, lst.length ≤ l → al l = 0 := by
    intro l hl
    rw [hal]
    split_ifs with h
    · rw [hbeyond l h hl]
      simp
    · rfl
  have hA : ∀ u, ((tailPos K la u : ℤ) : ℝ) = ∑ l ∈ Ico u lst.length, al l := by
    intro u
    unfold tailPos
    rw [Int.cast_sum]
    have e1 : ∑ m ∈ (range K).filter (fun m => u ≤ m), ((max (la m) 0 : ℤ) : ℝ) =
        ∑ m ∈ (range K).filter (fun m => u ≤ m), al m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_filter, Finset.mem_range] at hm
      rw [hal, if_pos hm.1]
    have e2 : ∑ m ∈ (range K).filter (fun m => u ≤ m), al m = ∑ m ∈ Ico u (K + lst.length), al m := by
      apply Finset.sum_subset
      · intro m hm
        rw [Finset.mem_filter, Finset.mem_range] at hm
        rw [Finset.mem_Ico]
        exact ⟨hm.2, by omega⟩
      · intro m hm hnm
        rw [Finset.mem_Ico] at hm
        apply halK
        by_contra hc
        exact hnm (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hm.1⟩)
    have e3 : ∑ m ∈ Ico u lst.length, al m = ∑ m ∈ Ico u (K + lst.length), al m := by
      apply Finset.sum_subset
      · intro m hm
        rw [Finset.mem_Ico] at hm ⊢
        exact ⟨hm.1, by omega⟩
      · intro m hm hnm
        rw [Finset.mem_Ico] at hm
        apply halL
        by_contra hc
        exact hnm (Finset.mem_Ico.mpr ⟨hm.1, by omega⟩)
    rw [e1, e2, e3]
  have hB : ∀ u, (((lst.drop u).sum : ℕ) : ℝ) = ∑ l ∈ Ico u lst.length, Bs l := by
    intro u
    rw [sum_drop lst u, Nat.cast_sum]
  have hC : ∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ) = ∑ l ∈ range lst.length, fT k' (al l) := by
    have c1 : ∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ) = ∑ m ∈ range K, fT k' (al m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_range] at hm
      rw [hal, if_pos hm]
    have c2 : ∑ m ∈ range K, fT k' (al m) = ∑ m ∈ range (K + lst.length), fT k' (al m) := by
      apply Finset.sum_subset
      · intro m hm
        rw [Finset.mem_range] at hm ⊢
        omega
      · intro m _ hnm
        rw [Finset.mem_range] at hnm
        rw [halK m (by omega), F0]
    have c3 : ∑ m ∈ range lst.length, fT k' (al m) = ∑ m ∈ range (K + lst.length), fT k' (al m) := by
      apply Finset.sum_subset
      · intro m hm
        rw [Finset.mem_range] at hm ⊢
        omega
      · intro m _ hnm
        rw [Finset.mem_range] at hnm
        rw [halL m (by omega), F0]
    rw [c1, c2, c3]
  obtain ⟨-, P2, P3, P4⟩ := h34 k' lst.length al Bs hk hal0
    (fun l hl => by rw [hBs]; exact_mod_cast h1 l hl)
    (fun l hl => by rw [hBs, hBs]; exact_mod_cast h2 l hl)
    (fun u _ => by
      have h' : ((tailPos K la u : ℤ) : ℝ) ≤ (((lst.drop u).sum : ℕ) : ℝ) := by
        have h3u := h3 u
        generalize (lst.drop u).sum = s at h3u ⊢
        exact_mod_cast h3u
      rw [hA u, hB u] at h'
      linarith)
  refine ⟨?_, ?_⟩
  · rw [hC]
    exact le_trans P2 P3
  · intro u₀ X hX hT
    rw [hA u₀, hB u₀] at hT
    have hu : u₀ < lst.length := by
      by_contra hc
      simp only [Finset.Ico_eq_empty_of_le (show lst.length ≤ u₀ by omega), Finset.sum_empty] at hT
      linarith
    refine ⟨hu, ?_⟩
    obtain ⟨Q1, Q2⟩ := P4 u₀ X hu hX.le (by linarith)
    rw [hC]
    exact le_trans Q1 Q2
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
