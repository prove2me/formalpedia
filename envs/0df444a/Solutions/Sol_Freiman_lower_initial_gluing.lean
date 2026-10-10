-- Prove2me | solution 1 for Freiman.lower_initial_gluing
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-09-12T13:06:18.830575+00:00
-- url     : https://prove2.me/submissions/92b6fad4-a9e2-4990-9d28-844f17fe0e0d

import Definitions.Def_Freiman_lowerInitialStage
import Theorems.Thm_Freiman_lower_initial_stage_preconnected
import Theorems.Thm_Freiman_lower_initial_stage_overlap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman
open Set Filter

lemma stage_decomposition :
    lowerInitialSet =
      {cF} ∪ ({t : ℝ | ∃ p ∈ lowerFixedRoots, t ∈ lowerCover p} ∪
        (⋃ n : ℕ, lowerInitialStage n)) := by
  ext t
  simp only [lowerInitialSet, Set.mem_ofPred_eq, Set.mem_union,
    Set.mem_singleton_iff, Set.mem_iUnion]
  constructor
  · intro ht
    rcases ht with hexpl | hrest
    · rw [lowerExplicitValue] at hexpl
      rcases hexpl with hc | ⟨f,n,k,hf,hval⟩
      · exact Or.inl hc
      · right; right; refine ⟨n, ?_⟩
        change t = lowerFamilyLimitValue .A n 0 ∨
          t = lowerFamilyLimitValue .B n 0 ∨
          (∃ j, t = lowerFamilyLimitValue .C n j) ∨
          (∃ j, t ∈ lowerFamilyH .A n j 0) ∨
          (∃ j, t ∈ lowerFamilyH .B n j 0) ∨
          (∃ j p, t ∈ lowerFamilyH .C n j p) ∨
          t ∈ lowerFamilyH .auxB n 0 0
        cases f with
        | A => left; simpa [lowerFamilyLimitValue, lowerFamilyLimitPair] using hval
        | B => right; left; simpa [lowerFamilyLimitValue, lowerFamilyLimitPair] using hval
        | C => right; right; left; exact ⟨k,hval⟩
        | auxB => exact (hf rfl).elim
    · rcases hrest with hfixed | hfam
      · exact Or.inr (Or.inl hfixed)
      · rcases hfam with ⟨f,n,k,p,h⟩
        right; right; refine ⟨n, ?_⟩
        change t = lowerFamilyLimitValue .A n 0 ∨
          t = lowerFamilyLimitValue .B n 0 ∨
          (∃ j, t = lowerFamilyLimitValue .C n j) ∨
          (∃ j, t ∈ lowerFamilyH .A n j 0) ∨
          (∃ j, t ∈ lowerFamilyH .B n j 0) ∨
          (∃ j p, t ∈ lowerFamilyH .C n j p) ∨
          t ∈ lowerFamilyH .auxB n 0 0
        cases f with
        | A => right; right; right; left; exact ⟨k, by simpa [lowerFamilyH, lowerFamilyPair] using h⟩
        | B => right; right; right; right; left; exact ⟨k, by simpa [lowerFamilyH, lowerFamilyPair] using h⟩
        | C => right; right; right; right; right; left; exact ⟨k,p,h⟩
        | auxB => right; right; right; right; right; right; simpa [lowerFamilyH, lowerFamilyPair] using h
  · intro ht
    rcases ht with hc | hrest
    · exact Or.inl (Or.inl hc)
    · rcases hrest with hfixed | hs
      · exact Or.inr (Or.inl hfixed)
      · rcases hs with ⟨n,hs⟩
        change t = lowerFamilyLimitValue .A n 0 ∨
          t = lowerFamilyLimitValue .B n 0 ∨
          (∃ j, t = lowerFamilyLimitValue .C n j) ∨
          (∃ j, t ∈ lowerFamilyH .A n j 0) ∨
          (∃ j, t ∈ lowerFamilyH .B n j 0) ∨
          (∃ j p, t ∈ lowerFamilyH .C n j p) ∨
          t ∈ lowerFamilyH .auxB n 0 0 at hs
        rcases hs with hA | hB | hClim | hAH | hBH | hCH | hX
        · exact Or.inl (Or.inr ⟨.A,n,0, by simp, hA⟩)
        · exact Or.inl (Or.inr ⟨.B,n,0, by simp, hB⟩)
        · rcases hClim with ⟨k,hk⟩
          exact Or.inl (Or.inr ⟨.C,n,k, by simp, hk⟩)
        · rcases hAH with ⟨k,hk⟩
          exact Or.inr (Or.inr ⟨.A,n,k,0,hk⟩)
        · rcases hBH with ⟨k,hk⟩
          exact Or.inr (Or.inr ⟨.B,n,k,0,hk⟩)
        · rcases hCH with ⟨k,p,hkp⟩
          exact Or.inr (Or.inr ⟨.C,n,k,p,hkp⟩)
        · exact Or.inr (Or.inr ⟨.auxB,n,0,0,hX⟩)

theorem solution (hseams : lowerInitialSeams) (hlimits : lowerInitialLimits)
    (hfixed : IsPreconnected {t : ℝ | ∃ p ∈ lowerFixedRoots, t ∈ lowerCover p})
    (hoverlap : (lowerCover ([3,2,1,1,3],[4,3,2,2]) ∩ lowerFamilyH .A 0 1 0).Nonempty) :
    IsPreconnected lowerInitialSet := by
  let F : Set ℝ := {t : ℝ | ∃ p ∈ lowerFixedRoots, t ∈ lowerCover p}
  let S : Set ℝ := ⋃ n : ℕ, lowerInitialStage n
  have hS : IsPreconnected S := by
    dsimp [S]
    apply IsPreconnected.iUnion_of_chain
    · intro n
      exact lower_initial_stage_preconnected hseams hlimits n
    · intro n
      simpa [Nat.succ_eq_add_one] using lower_initial_stage_overlap hseams n
  have hFS : (F ∩ S).Nonempty := by
    rcases hoverlap with ⟨x, hxcover, hxA⟩
    refine ⟨x, ?_, ?_⟩
    · change ∃ p ∈ lowerFixedRoots, x ∈ lowerCover p
      exact ⟨([3,2,1,1,3],[4,3,2,2]), by simp [lowerFixedRoots], hxcover⟩
    · change x ∈ ⋃ n : ℕ, lowerInitialStage n
      refine Set.mem_iUnion.2 ⟨0, ?_⟩
      change x = lowerFamilyLimitValue .A 0 0 ∨
        x = lowerFamilyLimitValue .B 0 0 ∨
        (∃ k, x = lowerFamilyLimitValue .C 0 k) ∨
        (∃ k, x ∈ lowerFamilyH .A 0 k 0) ∨
        (∃ k, x ∈ lowerFamilyH .B 0 k 0) ∨
        (∃ k p, x ∈ lowerFamilyH .C 0 k p) ∨
        x ∈ lowerFamilyH .auxB 0 0 0
      right; right; right; left
      exact ⟨1, hxA⟩
  have hbase : IsPreconnected (F ∪ S) := by
    exact hfixed.union' hFS hS
  have hsinf_mem : ∀ n : ℕ, sInf (lowerFamilyH .A n 1 0) ∈ lowerInitialStage n := by
    intro n
    change sInf (lowerFamilyH .A n 1 0) = lowerFamilyLimitValue .A n 0 ∨
      sInf (lowerFamilyH .A n 1 0) = lowerFamilyLimitValue .B n 0 ∨
      (∃ k, sInf (lowerFamilyH .A n 1 0) = lowerFamilyLimitValue .C n k) ∨
      (∃ k, sInf (lowerFamilyH .A n 1 0) ∈ lowerFamilyH .A n k 0) ∨
      (∃ k, sInf (lowerFamilyH .A n 1 0) ∈ lowerFamilyH .B n k 0) ∨
      (∃ k p, sInf (lowerFamilyH .A n 1 0) ∈ lowerFamilyH .C n k p) ∨
      sInf (lowerFamilyH .A n 1 0) ∈ lowerFamilyH .auxB n 0 0
    right; right; right; left
    refine ⟨1, ?_⟩
    simp [lowerFamilyH]
  have hcF_S : cF ∈ closure S := by
    apply mem_closure_of_tendsto hlimits.2.2.2.1
    filter_upwards [] with n
    change sInf (lowerFamilyH .A n 1 0) ∈ S
    exact Set.mem_iUnion.2 ⟨n, hsinf_mem n⟩
  have hcF_base : cF ∈ closure (F ∪ S) := by
    exact closure_mono (Set.subset_union_right) hcF_S
  have hwith : IsPreconnected (insert cF (F ∪ S)) := by
    apply hbase.subset_closure
    · exact Set.subset_insert cF (F ∪ S)
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hcF_base
      · exact subset_closure hx
  rw [stage_decomposition]
  change IsPreconnected (insert cF
    ({t : ℝ | ∃ p ∈ lowerFixedRoots, t ∈ lowerCover p} ∪
      (⋃ n : ℕ, lowerInitialStage n))) at hwith
  simpa only [Set.insert_eq] using hwith
