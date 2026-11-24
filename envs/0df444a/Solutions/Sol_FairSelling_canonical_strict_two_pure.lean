-- Prove2me | solution 1 for FairSelling.canonical_strict_two_pure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:02:30.635711+00:00
-- url     : https://prove2.me/submissions/b3d88b81-f180-4199-bec7-2b36f44f9ec4

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_CanonicalStrict
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_greedy_two_bags
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_vbarSum_sdiff
import Theorems.Thm_FairSelling_vbarSum_union
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {τ : ℝ} (hτ : 0 < τ) (F : G)
    (hsmall : ∀ g ∈ (Finset.univ \ ({F} : Finset G)), vbar w p g < (2 / 3) * τ)
    (htot3 : 3 * τ ≤ vbarSum w p (Finset.univ \ {F}))
    (htotall : 4 * τ ≤ vbarSum w p Finset.univ) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p τ kept sold money leftover := by
  classical
  obtain ⟨B1, B2, -, -, hdisj, hge1, hge2, hle⟩ :=
    greedy_two_bags (vbar w p) (fun g => le_trans (hp g) (le_max_left _ _)) τ hτ
      (Finset.univ \ {F}) hsmall htot3
  have hkept2 : vbarSum w p (Finset.univ \ (B1 ∪ B2))
      = vbarSum w p Finset.univ - vbarSum w p B1 - vbarSum w p B2 := by
    rw [vbarSum_sdiff w p (Finset.subset_univ _), vbarSum_union w p hdisj]
    ring
  have hB1 : vbarSum w p B1 = ∑ g ∈ B1, vbar w p g := rfl
  have hB2 : vbarSum w p B2 = ∑ g ∈ B2, vbar w p g := rfl
  set X : Fin 3 → Finset G :=
    fun k => if k = 0 then B1 else if k = 1 then B2 else Finset.univ \ (B1 ∪ B2) with hX
  have hX0 : X 0 = B1 := by simp [hX]
  have hX1 : X 1 = B2 := by simp [hX]
  have hX2 : X 2 = Finset.univ \ (B1 ∪ B2) := by simp [hX]
  have hd1 : Disjoint B1 (Finset.univ \ (B1 ∪ B2)) := by
    rw [Finset.disjoint_right]
    intro x hx hxB
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ hxB)
  have hd2 : Disjoint B2 (Finset.univ \ (B1 ∪ B2)) := by
    rw [Finset.disjoint_right]
    intro x hx hxB
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_right _ hxB)
  have d01 : Disjoint (X 0) (X 1) := by rw [hX0, hX1]; exact hdisj
  have d02 : Disjoint (X 0) (X 2) := by rw [hX0, hX2]; exact hd1
  have d12 : Disjoint (X 1) (X 2) := by rw [hX1, hX2]; exact hd2
  have hval0 : τ ≤ vbarSum w p (X 0) + (0 : ℝ) := by rw [hX0, add_zero, hB1]; exact hge1
  have hval1 : τ ≤ vbarSum w p (X 1) + (0 : ℝ) := by rw [hX1, add_zero, hB2]; exact hge2
  have hval2 : τ ≤ vbarSum w p (X 2) + (0 : ℝ) := by
    rw [hX2, add_zero, hkept2, hB1, hB2]; linarith
  refine ⟨X, ∅, fun _ => 0, 2, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j k hjk
    fin_cases j <;> fin_cases k
    · exact absurd rfl hjk
    · exact d01
    · exact d02
    · exact d01.symm
    · exact absurd rfl hjk
    · exact d12
    · exact d02.symm
    · exact d12.symm
    · exact absurd rfl hjk
  · intro k; simp
  · intro k; exact le_rfl
  · simp
  · intro k
    fin_cases k
    · exact hval0
    · exact hval1
    · exact hval2
  · intro k _; exact Or.inl rfl
  · simp
  · intro k _; exact Or.inl rfl
end FairSelling
