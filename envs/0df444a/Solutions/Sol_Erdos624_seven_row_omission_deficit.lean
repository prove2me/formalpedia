-- Prove2me | solution 1 for Erdos624.seven_row_omission_deficit
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-19T15:08:45.840717+00:00
-- url     : https://prove2.me/submissions/87b4e7aa-af4f-42a4-8551-ba7c80d598a7

import Mathlib
open Finset

namespace E624R20D
open Finset

variable {U : Type*} [DecidableEq U]

set_option linter.unusedVariables false

lemma sum_card_eq_sum_mem
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

lemma card_erase_erase
    (Z : Finset U) {z t : U} (hz : z ∈ Z) (ht : t ∈ Z) (hne : t ≠ z) :
    #((Z.erase z).erase t) = #Z - 2 := by
  have ht' : t ∈ Z.erase z := mem_erase.2 ⟨hne, ht⟩
  rw [card_erase_of_mem ht', card_erase_of_mem hz]
  exact Nat.sub_sub _ _ _

lemma exists_cover_avoiding
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

lemma six_cover_degree_le_three
    (Z : Finset U) (S : Finset (Finset U))
    (hZ : 2 ≤ #Z)
    (hS : #S = 6)
    (hsub : ∀ A ∈ S, A ⊆ Z)
    (hne : ∀ A ∈ S, A.Nonempty)
    (hnd : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ¬ Disjoint A B)
    (hcov : ∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ S, A ⊆ Y) :
    ∀ z ∈ Z, #{A ∈ S | z ∈ A} ≤ 3 := by
  classical
  intro z hz
  set Av := S.filter (fun A => z ∉ A) with hAv
  have hsplit : #S = #{A ∈ S | z ∈ A} + #Av := by
    rw [hAv, ← card_filter_add_card_filter_not (fun A => z ∈ A), add_comm]
  have hAvcard : #Av = 6 - #{A ∈ S | z ∈ A} := by omega
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
          by_contra hne'
          exact hnone ⟨u, hu, hne'⟩
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
  omega

lemma deg_erase {T : Finset (Finset U)} {R : Finset U} {z : U}
    (hR : R ∈ T) :
    #{A ∈ T.erase R | z ∈ A} =
      #{A ∈ T | z ∈ A} - (if z ∈ R then 1 else 0) := by
  classical
  by_cases hz : z ∈ R
  · have hRmem : R ∈ T.filter (fun A => z ∈ A) := mem_filter.2 ⟨hR, hz⟩
    have hfilt :
        (T.filter (fun A => z ∈ A)).erase R = (T.erase R).filter (fun A => z ∈ A) := by
      ext A
      simp only [mem_filter, mem_erase]
      tauto
    have hcard : #((T.filter (fun A => z ∈ A)).erase R) = #{A ∈ T | z ∈ A} - 1 :=
      card_erase_of_mem hRmem
    rw [hfilt] at hcard
    have hsplit : #{A ∈ T.erase R | z ∈ A} = #{A ∈ T | z ∈ A} - 1 := hcard
    simp [hz, hsplit]
  · have hEq : T.filter (fun A => z ∈ A) = (T.erase R).filter (fun A => z ∈ A) := by
      ext A
      simp [mem_filter, mem_erase]
      intro hzA hAT
      exact fun hAR => hz (hAR ▸ hzA)
    simp [hz, hEq]

lemma seven_row_omission_deficit
    (Z : Finset U) (T : Finset (Finset U)) (R : Finset U)
    (hZ : 2 ≤ #Z)
    (hT : #T = 7)
    (hR : R ∈ T)
    (hsub : ∀ A ∈ T, A ⊆ Z)
    (hne : ∀ A ∈ T, A.Nonempty)
    (hnd : ∀ A ∈ T, ∀ B ∈ T, A ≠ B → ¬ Disjoint A B)
    (hcov : ∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ T.erase R, A ⊆ Y) :
    (∀ z ∈ Z, #{A ∈ T | z ∈ A} ≤ 4) ∧
      (Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) ⊆ R) ∧
      (3 * #Z - ∑ A ∈ T.erase R, #A =
        (∑ z ∈ Z.filter (fun z => #{A ∈ T | z ∈ A} ≤ 2),
            (3 - #{A ∈ T | z ∈ A})) +
          #(R \ Z.filter (fun z => #{A ∈ T | z ∈ A} = 4))) := by
  classical
  set S6 := T.erase R with hS6
  have hS6card : #S6 = 6 := by
    rw [hS6, card_erase_of_mem hR, hT]
  have hsub6 : ∀ A ∈ S6, A ⊆ Z := fun A hA => hsub A (mem_of_mem_erase hA)
  have hne6 : ∀ A ∈ S6, A.Nonempty := fun A hA => hne A (mem_of_mem_erase hA)
  have hnd6 : ∀ A ∈ S6, ∀ B ∈ S6, A ≠ B → ¬ Disjoint A B :=
    fun A hA B hB hneAB => hnd A (mem_of_mem_erase hA) B (mem_of_mem_erase hB) hneAB
  have hdeg6 : ∀ z ∈ Z, #{A ∈ S6 | z ∈ A} ≤ 3 :=
    six_cover_degree_le_three Z S6 hZ hS6card hsub6 hne6 hnd6 (by simpa [hS6] using hcov)
  have hdegS6 : ∀ z, #{A ∈ S6 | z ∈ A} =
      #{A ∈ T | z ∈ A} - (if z ∈ R then 1 else 0) := by
    intro z
    simpa [hS6] using (deg_erase (T := T) (R := R) (z := z) hR)
  have hDpos : ∀ z, z ∈ R → 1 ≤ #{A ∈ T | z ∈ A} := by
    intro z hzR
    have : R ∈ T.filter (fun A => z ∈ A) := mem_filter.2 ⟨hR, hzR⟩
    exact Nat.succ_le_iff.2 (card_pos.mpr ⟨R, this⟩)
  have hD4 : ∀ z ∈ Z, #{A ∈ T | z ∈ A} ≤ 4 := by
    intro z hz
    have hd6 := hdegS6 z
    have hle3 : #{A ∈ S6 | z ∈ A} ≤ 3 := hdeg6 z hz
    by_cases hzR : z ∈ R
    · have := hDpos z hzR
      rw [if_pos hzR] at hd6
      omega
    · rw [if_neg hzR] at hd6
      omega
  have hSsub : Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) ⊆ R := by
    intro z hz
    have hzZ : z ∈ Z := (mem_filter.1 hz).1
    have h4 : #{A ∈ T | z ∈ A} = 4 := (mem_filter.1 hz).2
    have hd6 := hdegS6 z
    have hle3 : #{A ∈ S6 | z ∈ A} ≤ 3 := hdeg6 z hzZ
    by_cases hzR : z ∈ R
    · exact hzR
    · rw [if_neg hzR] at hd6
      omega
  have hsum : ∑ A ∈ S6, #A = ∑ z ∈ Z, #{A ∈ S6 | z ∈ A} :=
    sum_card_eq_sum_mem Z S6 hsub6
  have hle : ∑ A ∈ S6, #A ≤ 3 * #Z := by
    rw [hsum]
    calc
      ∑ z ∈ Z, #{A ∈ S6 | z ∈ A} ≤ ∑ _z ∈ Z, 3 := sum_le_sum fun z hz => hdeg6 z hz
      _ = 3 * #Z := by simp [sum_const, smul_eq_mul, mul_comm]
  have hsub' : 3 * #Z - ∑ A ∈ S6, #A = ∑ z ∈ Z, (3 - #{A ∈ S6 | z ∈ A}) := by
    have hpt : ∑ z ∈ Z, #{A ∈ S6 | z ∈ A} + ∑ z ∈ Z, (3 - #{A ∈ S6 | z ∈ A}) =
        ∑ z ∈ Z, 3 := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun z hz => Nat.add_sub_of_le (hdeg6 z hz)
    have hright : ∑ z ∈ Z, 3 = 3 * #Z := by simp [sum_const, smul_eq_mul, mul_comm]
    rw [hsum, ← hright, ← hpt, Nat.add_sub_cancel_left]
  set D : U → ℕ := fun z => #{A ∈ T | z ∈ A} with hDdef
  set S : Finset U := Z.filter (fun z => D z = 4) with hSdef
  have hS_eq : S = Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) := by
    simp [hSdef, hDdef]
  have hpoint : ∀ z ∈ Z, 3 - #{A ∈ S6 | z ∈ A} =
      (if D z ≤ 2 then 3 - D z else 0) + (if z ∈ R ∧ D z ≠ 4 then 1 else 0) := by
    intro z hz
    have hd6 : #{A ∈ S6 | z ∈ A} = D z - (if z ∈ R then 1 else 0) := by
      simpa [hDdef] using hdegS6 z
    have hDle : D z ≤ 4 := by simpa [hDdef] using hD4 z hz
    by_cases hzR : z ∈ R
    · have hpos : 1 ≤ D z := by simpa [hDdef] using hDpos z hzR
      have hd6' : #{A ∈ S6 | z ∈ A} = D z - 1 := by simp [hd6, hzR]
      by_cases hle2 : D z ≤ 2
      · have hne4 : D z ≠ 4 := by omega
        have harith : 3 - (D z - 1) = (3 - D z) + 1 := by omega
        simp [hd6', hle2, hzR, hne4]
        exact harith
      · have hcases : D z = 3 ∨ D z = 4 := by omega
        rcases hcases with h3 | h4
        · simp [hd6', hle2, hzR, h3]
        · simp [hd6', hle2, hzR, h4]
    · have hd6' : #{A ∈ S6 | z ∈ A} = D z := by simp [hd6, hzR]
      have hne4 : D z ≠ 4 := by
        intro h4
        have hzS : z ∈ S := by
          rw [hSdef]
          exact mem_filter.2 ⟨hz, h4⟩
        exact hzR (hSsub (hS_eq ▸ hzS))
      simp [hd6', hzR, hne4]
      by_cases hle2 : D z ≤ 2
      · simp [hle2]
      · have : D z = 3 := by omega
        simp [hle2, this]
  have hsum_split :
      ∑ z ∈ Z, (3 - #{A ∈ S6 | z ∈ A}) =
        (∑ z ∈ Z.filter (fun z => D z ≤ 2), (3 - D z)) +
          #(R \ S) := by
    have hpt := sum_congr rfl fun z hz => hpoint z hz
    have hsum' :
        ∑ z ∈ Z, (3 - #{A ∈ S6 | z ∈ A}) =
          (∑ z ∈ Z, if D z ≤ 2 then 3 - D z else 0) +
            (∑ z ∈ Z, if z ∈ R ∧ D z ≠ 4 then 1 else 0) := by
      rw [hpt, sum_add_distrib]
    have hfirst :
        (∑ z ∈ Z, if D z ≤ 2 then 3 - D z else 0) =
          ∑ z ∈ Z.filter (fun z => D z ≤ 2), (3 - D z) :=
      (sum_filter (p := fun z => D z ≤ 2) (f := fun z => 3 - D z) (s := Z)).symm
    have hRsub : R ⊆ Z := hsub R hR
    have hsecond :
        (∑ z ∈ Z, if z ∈ R ∧ D z ≠ 4 then 1 else 0) = #(R \ S) := by
      have hpred : ∀ z, (z ∈ R ∧ D z ≠ 4) ↔ z ∈ R \ S := by
        intro z
        constructor
        · intro ⟨hzR, hne4⟩
          have hzS : z ∉ S := by
            intro hzS
            have hz' : z ∈ Z.filter (fun w => D w = 4) := by
              simpa [hSdef] using hzS
            exact hne4 (mem_filter.1 hz').2
          exact mem_sdiff.2 ⟨hzR, hzS⟩
        · intro hzRS
          have hzR : z ∈ R := (mem_sdiff.1 hzRS).1
          have hzS : z ∉ S := (mem_sdiff.1 hzRS).2
          have hzZ : z ∈ Z := hRsub hzR
          have hne4 : D z ≠ 4 := by
            intro h4
            have : z ∈ S := by
              rw [hSdef]
              exact mem_filter.2 ⟨hzZ, h4⟩
            exact hzS this
          exact ⟨hzR, hne4⟩
      have : Z.filter (fun z => z ∈ R ∧ D z ≠ 4) = R \ S := by
        ext z
        simp only [mem_filter]
        constructor
        · intro ⟨_, hp⟩
          exact (hpred z).1 hp
        · intro hzRS
          exact ⟨hRsub (mem_sdiff.1 hzRS).1, (hpred z).2 hzRS⟩
      rw [← sum_filter (p := fun z => z ∈ R ∧ D z ≠ 4), this, card_eq_sum_ones]
    rw [hsum', hfirst, hsecond]
  refine ⟨hD4, ?_, ?_⟩
  · simpa [hDdef, hSdef] using hSsub
  · -- rewrite both sides in D/S notation
    have : 3 * #Z - ∑ A ∈ T.erase R, #A =
        (∑ z ∈ Z.filter (fun z => D z ≤ 2), (3 - D z)) + #(R \ S) := by
      simpa [hS6] using (hsub'.trans hsum_split)
    simpa [hS6, hDdef, hSdef] using this

end E624R20D

namespace Erdos624

theorem seven_row_omission_deficit {U : Type*} [DecidableEq U]
    (Z : Finset U) (T : Finset (Finset U)) (R : Finset U)
    (hZ : 2 ≤ #Z)
    (hT : #T = 7)
    (hR : R ∈ T)
    (hsub : ∀ A ∈ T, A ⊆ Z)
    (hne : ∀ A ∈ T, A.Nonempty)
    (hnd : ∀ A ∈ T, ∀ B ∈ T, A ≠ B → ¬ Disjoint A B)
    (hcov : ∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ T.erase R, A ⊆ Y) :
    (∀ z ∈ Z, #{A ∈ T | z ∈ A} ≤ 4) ∧
      (Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) ⊆ R) ∧
      (3 * #Z - ∑ A ∈ T.erase R, #A =
        (∑ z ∈ Z.filter (fun z => #{A ∈ T | z ∈ A} ≤ 2),
            (3 - #{A ∈ T | z ∈ A})) +
          #(R \ Z.filter (fun z => #{A ∈ T | z ∈ A} = 4))) :=
  E624R20D.seven_row_omission_deficit Z T R hZ hT hR hsub hne hnd hcov

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U]
    (Z : Finset U) (T : Finset (Finset U)) (R : Finset U)
    (hZ : 2 ≤ #Z)
    (hT : #T = 7)
    (hR : R ∈ T)
    (hsub : ∀ A ∈ T, A ⊆ Z)
    (hne : ∀ A ∈ T, A.Nonempty)
    (hnd : ∀ A ∈ T, ∀ B ∈ T, A ≠ B → ¬ Disjoint A B)
    (hcov : ∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ T.erase R, A ⊆ Y) :
    (∀ z ∈ Z, #{A ∈ T | z ∈ A} ≤ 4) ∧
      (Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) ⊆ R) ∧
      (3 * #Z - ∑ A ∈ T.erase R, #A =
        (∑ z ∈ Z.filter (fun z => #{A ∈ T | z ∈ A} ≤ 2),
            (3 - #{A ∈ T | z ∈ A})) +
          #(R \ Z.filter (fun z => #{A ∈ T | z ∈ A} = 4))) :=
  Erdos624.seven_row_omission_deficit Z T R hZ hT hR hsub hne hnd hcov

