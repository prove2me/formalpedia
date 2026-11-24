-- Prove2me | solution 1 for FairSelling.canonical_strict_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:01:35.039887+00:00
-- url     : https://prove2.me/submissions/9a69a0bf-0c53-400b-8e62-85f5cf587b2b

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_CanonicalStrict
import Theorems.Thm_FairSelling_bagfill
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_vbarSum_sdiff
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
theorem _root_.solution (w p : G → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hsmall : ∀ g, vbar w p g < τ) (F e : G) (heF : e ≠ F)
    (hpF : τ / 3 ≤ p F)
    (htop : τ ≤ vbar w p e + p F)
    (htot : 4 * τ ≤ vbarSum w p (Finset.univ \ {F}) + p F) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p τ kept sold money leftover := by
  classical
  have hpFlt : p F < τ := lt_of_le_of_lt (le_max_left _ _) (hsmall F)
  have hue : vbar w p e < τ := hsmall e
  -- the goods available for the pure bundle
  set S : Finset G := (Finset.univ \ ({F} : Finset G)) \ {e} with hS
  have heU : ({e} : Finset G) ⊆ Finset.univ \ ({F} : Finset G) := by
    simp [Finset.subset_iff, heF]
  have hSsum : vbarSum w p S = vbarSum w p (Finset.univ \ {F}) - vbar w p e := by
    rw [hS, vbarSum_sdiff w p heU]
    simp [vbarSum]
  obtain ⟨B, hBS, hB1, hB2⟩ :=
    bagfill (vbar w p) τ (2 * τ) hτ.le (by linarith) S
      (fun g _ => by have := hsmall g; linarith)
      (by
        have hEq : ∑ g ∈ S, vbar w p g = vbarSum w p S := rfl
        rw [hEq, hSsum]; linarith)
  have hBsum : vbarSum w p B = ∑ g ∈ B, vbar w p g := rfl
  have hFS : F ∉ S := by simp [hS]
  have heS : e ∉ S := by simp [hS]
  have hFB : F ∉ B := fun h => hFS (hBS h)
  have heB : e ∉ B := fun h => heS (hBS h)
  set C : Finset G := insert F (insert e B) with hC
  have hCsum : vbarSum w p C = vbar w p F + vbar w p e + vbarSum w p B := by
    rw [hC, vbarSum, Finset.sum_insert (by simp [Ne.symm heF, hFB]), Finset.sum_insert heB]
    simp [vbarSum]
    ring
  have hkept2 : vbarSum w p (Finset.univ \ C)
      = vbarSum w p (Finset.univ \ {F}) - vbar w p e - vbarSum w p B := by
    rw [vbarSum_sdiff w p (Finset.subset_univ C), hCsum,
      vbarSum_sdiff w p (Finset.subset_univ ({F} : Finset G))]
    simp [vbarSum]
    ring
  -- the three bundles
  set X : Fin 3 → Finset G :=
    fun k => if k = 0 then {e} else if k = 1 then B else Finset.univ \ C with hX
  set m : Fin 3 → ℝ :=
    fun k => if k = 0 then τ - vbar w p e else if k = 1 then 0 else p F - (τ - vbar w p e)
    with hm
  have hX0 : X 0 = {e} := by simp [hX]
  have hX1 : X 1 = B := by simp [hX]
  have hX2 : X 2 = Finset.univ \ C := by simp [hX]
  have hm0' : m 0 = τ - vbar w p e := by simp [hm]
  have hm1' : m 1 = 0 := by simp [hm]
  have hm2' : m 2 = p F - (τ - vbar w p e) := by simp [hm]
  have hdeB : Disjoint ({e} : Finset G) B := by simpa using heB
  have hdeC : Disjoint ({e} : Finset G) (Finset.univ \ C) := by
    rw [Finset.disjoint_left]
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    simp [hC]
  have hdBC : Disjoint B (Finset.univ \ C) := by
    rw [Finset.disjoint_right]
    intro x hx hxB
    exact (Finset.mem_sdiff.mp hx).2 (by simp [hC, hxB])
  -- the six conditions, checked bundle by bundle
  have d01 : Disjoint (X 0) (X 1) := by rw [hX0, hX1]; exact hdeB
  have d02 : Disjoint (X 0) (X 2) := by rw [hX0, hX2]; exact hdeC
  have d12 : Disjoint (X 1) (X 2) := by rw [hX1, hX2]; exact hdBC
  have hs0 : Disjoint ({F} : Finset G) (X 0) := by
    rw [hX0]; simpa [Finset.disjoint_singleton] using Ne.symm heF
  have hs1 : Disjoint ({F} : Finset G) (X 1) := by
    rw [hX1]; simpa [Finset.disjoint_singleton_left] using hFB
  have hs2 : Disjoint ({F} : Finset G) (X 2) := by
    rw [hX2, Finset.disjoint_left]
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    simp [hC]
  have hcard0 : (X 0).card = 1 := by rw [hX0]; simp
  have hmn0 : 0 ≤ m 0 := by rw [hm0']; linarith
  have hmn1 : 0 ≤ m 1 := by rw [hm1']
  have hmn2 : 0 ≤ m 2 := by rw [hm2']; linarith
  have hmle : m 0 ≤ p F := by rw [hm0']; linarith
  have hval0 : τ ≤ vbarSum w p (X 0) + m 0 := by
    rw [hX0, hm0', show vbarSum w p ({e} : Finset G) = vbar w p e from by simp [vbarSum]]
    linarith
  have hval1 : τ ≤ vbarSum w p (X 1) + m 1 := by
    rw [hX1, hm1', add_zero, hBsum]; exact hB1
  have hval2 : τ ≤ vbarSum w p (X 2) + m 2 := by
    rw [hX2, hm2', hkept2]
    linarith
  refine ⟨X, {F}, m, 2, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
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
  · intro k
    fin_cases k
    · exact hs0
    · exact hs1
    · exact hs2
  · intro k
    fin_cases k
    · exact hmn0
    · exact hmn1
    · exact hmn2
  · rw [Fin.sum_univ_three, hm0', hm1', hm2']
    simp
  · intro k
    fin_cases k
    · exact hval0
    · exact hval1
    · exact hval2
  · intro k hk
    fin_cases k
    · exact Or.inr hcard0
    · exact Or.inl hm1'
    · exact absurd rfl hk
  · simp
  · intro k hk
    fin_cases k
    · exact Or.inr ⟨hcard0, F, Finset.mem_singleton_self F, hmle, hpF⟩
    · exact Or.inl hm1'
    · exact absurd rfl hk
end FairSelling
