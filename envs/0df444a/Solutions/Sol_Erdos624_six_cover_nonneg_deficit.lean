-- Prove2me | solution 1 for Erdos624.six_cover_nonneg_deficit
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T10:25:48.947517+00:00
-- url     : https://prove2.me/submissions/94f5e6a9-4b33-483e-95e9-703195c6402d

import Mathlib
open Finset

namespace E624R19D
open Finset

lemma sum_card_eq_sum_mem {U : Type*} [DecidableEq U]
    (Z : Finset U) (S : Finset (Finset U))
    (hsub : ∀ A ∈ S, A ⊆ Z) :
    ∑ A ∈ S, #A = ∑ z ∈ Z, #{A ∈ S | z ∈ A} := by
  classical
  have hA : ∀ A ∈ S, #A = ∑ z ∈ Z, if z ∈ A then 1 else 0 := by
    intro A hA
    have heq : Z.filter (fun z => z ∈ A) = A := by
      ext z
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun hz => ⟨hsub A hA hz, hz⟩⟩
    rw [← sum_filter (p := fun z => z ∈ A), heq, card_eq_sum_ones]
  calc
    ∑ A ∈ S, #A = ∑ A ∈ S, ∑ z ∈ Z, if z ∈ A then 1 else 0 :=
      sum_congr rfl hA
    _ = ∑ z ∈ Z, ∑ A ∈ S, if z ∈ A then 1 else 0 := sum_comm
    _ = ∑ z ∈ Z, #{A ∈ S | z ∈ A} := by
        refine sum_congr rfl fun z _ => ?_
        rw [← sum_filter (p := fun A => z ∈ A), card_eq_sum_ones]

lemma card_erase_erase {U : Type*} [DecidableEq U]
    (Z : Finset U) {z t : U} (hz : z ∈ Z) (ht : t ∈ Z) (hne : t ≠ z) :
    #((Z.erase z).erase t) = #Z - 2 := by
  have ht' : t ∈ Z.erase z := mem_erase.2 ⟨hne, ht⟩
  rw [card_erase_of_mem ht', card_erase_of_mem hz]
  exact Nat.sub_sub _ _ _

lemma exists_cover_avoiding {U : Type*} [DecidableEq U]
    (Z : Finset U) (S : Finset (Finset U)) (z t : U)
    (hz : z ∈ Z) (ht : t ∈ Z) (hne : t ≠ z)
    (hcov : ∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ S, A ⊆ Y) :
    ∃ A ∈ S, z ∉ A ∧ t ∉ A ∧ A ⊆ Z := by
  let Y := (Z.erase z).erase t
  have hYsub : Y ⊆ Z := (erase_subset t (Z.erase z)).trans (erase_subset z Z)
  have hYcard : #Y = #Z - 2 := card_erase_erase Z hz ht hne
  obtain ⟨A, hAS, hAY⟩ := hcov Y hYsub hYcard
  refine ⟨A, hAS, ?_, ?_, hAY.trans hYsub⟩
  · exact fun hzA => (mem_erase.1 ((erase_subset t (Z.erase z)) (hAY hzA))).1 rfl
  · exact fun htA => (mem_erase.1 (hAY htA)).1 rfl

/-- On a selected intersecting six-cover of the $k$-faces of a $(k+2)$-set,
every point lies in at most three of the six rows, the total size sum is at
most $3|Z|$, and equality holds if and only if every degree is exactly three. -/
theorem six_cover_nonneg_deficit {U : Type*} [DecidableEq U]
    (Z : Finset U) (S : Finset (Finset U))
    (hZ : 2 ≤ #Z)
    (hS : #S = 6)
    (hsub : ∀ A ∈ S, A ⊆ Z)
    (hne : ∀ A ∈ S, A.Nonempty)
    (hnd : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ¬ Disjoint A B)
    (hcov : ∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ S, A ⊆ Y) :
    (∀ z ∈ Z, #{A ∈ S | z ∈ A} ≤ 3) ∧
    ∑ A ∈ S, #A ≤ 3 * #Z ∧
    (∑ A ∈ S, #A = 3 * #Z ↔ ∀ z ∈ Z, #{A ∈ S | z ∈ A} = 3) := by
  classical
  have hdeg : ∀ z ∈ Z, #{A ∈ S | z ∈ A} ≤ 3 := by
    intro z hz
    set Av := S.filter (fun A => z ∉ A) with hAv
    have hsplit : #S = #{A ∈ S | z ∈ A} + #Av := by
      rw [hAv, ← card_filter_add_card_filter_not (fun A => z ∈ A), add_comm]
    have hAvcard : #Av = 6 - #{A ∈ S | z ∈ A} := by
      omega
    have hAv3 : 3 ≤ #Av := by
      by_contra hlt
      have hle : #Av ≤ 2 := by omega
      have hzAv : ∀ A ∈ Av, z ∉ A := fun A hA => (mem_filter.1 hA).2
      have hAvS : ∀ A ∈ Av, A ∈ S := fun A hA => (mem_filter.1 hA).1
      rcases (show #Av = 0 ∨ #Av = 1 ∨ #Av = 2 by omega) with hAv0 | hAv1 | hAv2
      · obtain ⟨t, ht, htz⟩ : ∃ t ∈ Z, t ≠ z := by
          by_contra hnone
          have : Z ⊆ {z} := by
            intro u hu
            refine mem_singleton.2 ?_
            by_contra hne
            exact hnone ⟨u, hu, hne⟩
          have : #Z ≤ 1 := (card_le_card this).trans_eq (card_singleton _)
          omega
        obtain ⟨A, hAS, hzA, _, _⟩ := exists_cover_avoiding Z S z t hz ht htz hcov
        have : A ∈ Av := mem_filter.2 ⟨hAS, hzA⟩
        simp [card_eq_zero.mp hAv0] at this
      · obtain ⟨A, hAuniq⟩ := card_eq_one.mp hAv1
        have hAAv : A ∈ Av := by simp [hAuniq]
        have hAS : A ∈ S := hAvS A hAAv
        obtain ⟨t, htA⟩ := hne A hAS
        have htZ : t ∈ Z := hsub A hAS htA
        have htz : t ≠ z := fun e => hzAv A hAAv (e ▸ htA)
        obtain ⟨B, hBS, hzB, htB, _⟩ := exists_cover_avoiding Z S z t hz htZ htz hcov
        have hBAv : B ∈ Av := mem_filter.2 ⟨hBS, hzB⟩
        have hBA : B = A := by
          have : B ∈ ({A} : Finset _) := by simpa [hAuniq] using hBAv
          simpa using this
        exact htB (hBA.symm ▸ htA)
      · obtain ⟨A, B, hAB, hAvAB⟩ := card_eq_two.mp hAv2
        have hAAv : A ∈ Av := by simp [hAvAB]
        have hBAv : B ∈ Av := by simp [hAvAB]
        have hAS : A ∈ S := hAvS A hAAv
        have hBS : B ∈ S := hAvS B hBAv
        have hndAB : ¬ Disjoint A B := hnd A hAS B hBS hAB
        obtain ⟨t, htA, htB'⟩ := not_disjoint_iff.mp hndAB
        have htZ : t ∈ Z := hsub A hAS htA
        have htz : t ≠ z := fun e => hzAv A hAAv (e ▸ htA)
        obtain ⟨C, hCS, hzC, htC, _⟩ := exists_cover_avoiding Z S z t hz htZ htz hcov
        have hCAv : C ∈ Av := mem_filter.2 ⟨hCS, hzC⟩
        have hCmem : C = A ∨ C = B := by
          have : C ∈ ({A, B} : Finset _) := by simpa [hAvAB] using hCAv
          simpa using this
        rcases hCmem with hCA | hCB
        · exact htC (hCA.symm ▸ htA)
        · exact htC (hCB.symm ▸ htB')
    have : #{A ∈ S | z ∈ A} ≤ 3 := by
      have := hAv3
      omega
    exact this
  have hsum : ∑ A ∈ S, #A = ∑ z ∈ Z, #{A ∈ S | z ∈ A} :=
    sum_card_eq_sum_mem Z S hsub
  have hle : ∑ A ∈ S, #A ≤ 3 * #Z := by
    rw [hsum]
    calc
      ∑ z ∈ Z, #{A ∈ S | z ∈ A} ≤ ∑ _z ∈ Z, 3 := sum_le_sum fun z hz => hdeg z hz
      _ = 3 * #Z := by simp [sum_const, smul_eq_mul, mul_comm]
  refine ⟨hdeg, hle, ?_⟩
  constructor
  · intro heq z hz
    have hpt : ∑ z ∈ Z, #{A ∈ S | z ∈ A} = ∑ z ∈ Z, 3 := by
      rw [← hsum, heq]
      simp [sum_const, smul_eq_mul, mul_comm]
    exact (sum_eq_sum_iff_of_le (fun z hz => hdeg z hz)).1 hpt z hz
  · intro hall
    rw [hsum, sum_congr rfl (fun z hz => hall z hz)]
    simp [sum_const, smul_eq_mul, mul_comm]

end E624R19D

namespace Erdos624

theorem six_cover_nonneg_deficit {U : Type*} [DecidableEq U]
    (Z : Finset U) (S : Finset (Finset U))
    (hZ : 2 ≤ #Z)
    (hS : #S = 6)
    (hsub : ∀ A ∈ S, A ⊆ Z)
    (hne : ∀ A ∈ S, A.Nonempty)
    (hnd : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ¬ Disjoint A B)
    (hcov : ∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ S, A ⊆ Y) :
    (∀ z ∈ Z, #{A ∈ S | z ∈ A} ≤ 3) ∧
    ∑ A ∈ S, #A ≤ 3 * #Z ∧
    (∑ A ∈ S, #A = 3 * #Z ↔ ∀ z ∈ Z, #{A ∈ S | z ∈ A} = 3) :=
  E624R19D.six_cover_nonneg_deficit Z S hZ hS hsub hne hnd hcov

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U]
    (Z : Finset U) (S : Finset (Finset U))
    (hZ : 2 ≤ #Z)
    (hS : #S = 6)
    (hsub : ∀ A ∈ S, A ⊆ Z)
    (hne : ∀ A ∈ S, A.Nonempty)
    (hnd : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ¬ Disjoint A B)
    (hcov : ∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ S, A ⊆ Y) :
    (∀ z ∈ Z, #{A ∈ S | z ∈ A} ≤ 3) ∧
    ∑ A ∈ S, #A ≤ 3 * #Z ∧
    (∑ A ∈ S, #A = 3 * #Z ↔ ∀ z ∈ Z, #{A ∈ S | z ∈ A} = 3) :=
  Erdos624.six_cover_nonneg_deficit Z S hZ hS hsub hne hnd hcov
