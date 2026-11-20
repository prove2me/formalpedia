-- Prove2me | solution 1 for Erdos624.seven_row_omission_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-19T15:08:45.213678+00:00
-- url     : https://prove2.me/submissions/d7817e18-68b7-4c12-8efe-f8a4de6ee105

import Mathlib
open Finset

namespace E624R20I
open Finset

set_option linter.unusedVariables false

variable {U : Type*} [DecidableEq U]

lemma deg_erase {T : Finset (Finset U)} {R : Finset U} {z : U}
    (hR : R ∈ T) :
    #{A ∈ T.erase R | z ∈ A} = #{A ∈ T | z ∈ A} - (if z ∈ R then 1 else 0) := by
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

lemma deg_erase_eq_three_of {T : Finset (Finset U)} {R : Finset U} {z : U}
    (hR : R ∈ T)
    (h : #{A ∈ T.erase R | z ∈ A} = 3) :
    (#{A ∈ T | z ∈ A} = 3 ∨ #{A ∈ T | z ∈ A} = 4) ∧
      (z ∈ R ↔ #{A ∈ T | z ∈ A} = 4) := by
  classical
  have hde := deg_erase (T := T) (R := R) (z := z) hR
  by_cases hz : z ∈ R
  · have : #{A ∈ T | z ∈ A} = 4 := by
      have h' : #{A ∈ T.erase R | z ∈ A} = #{A ∈ T | z ∈ A} - 1 := by simp [hde, hz]
      omega
    exact ⟨Or.inr this, ⟨fun _ => this, fun _ => hz⟩⟩
  · have : #{A ∈ T | z ∈ A} = 3 := by
      have h' : #{A ∈ T.erase R | z ∈ A} = #{A ∈ T | z ∈ A} := by simp [hde, hz]
      omega
    exact ⟨Or.inl this, ⟨fun hzin => (hz hzin).elim, fun h4 => by omega⟩⟩

lemma S_eq_R_of_deg_three {Z : Finset U} {T : Finset (Finset U)} {R : Finset U}
    (hR : R ∈ T) (hsub : ∀ A ∈ T, A ⊆ Z)
    (hdeg : ∀ z ∈ Z, #{A ∈ T.erase R | z ∈ A} = 3) :
    Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) = R := by
  classical
  ext z
  constructor
  · intro hz
    have hzZ : z ∈ Z := (mem_filter.1 hz).1
    have h4 : #{A ∈ T | z ∈ A} = 4 := (mem_filter.1 hz).2
    exact (deg_erase_eq_three_of hR (hdeg z hzZ)).2.2 h4
  · intro hzR
    have hzZ : z ∈ Z := hsub R hR hzR
    have hiff := (deg_erase_eq_three_of hR (hdeg z hzZ)).2
    exact mem_filter.2 ⟨hzZ, hiff.1 hzR⟩

/-- On a seven-row window, a covering three-regular omission exists if and only if
every degree is 3 or 4, the degree-4 set is itself a raw row, and omitting that
row leaves a cover of every two-point deletion. -/
theorem seven_row_omission_iff
    (Z : Finset U) (T : Finset (Finset U))
    (hZ : 2 ≤ #Z)
    (hT : #T = 7)
    (hsub : ∀ A ∈ T, A ⊆ Z) :
    (∃ R ∈ T,
        (∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ T.erase R, A ⊆ Y) ∧
        (∀ z ∈ Z, #{A ∈ T.erase R | z ∈ A} = 3)) ↔
      ((∀ z ∈ Z, #{A ∈ T | z ∈ A} = 3 ∨ #{A ∈ T | z ∈ A} = 4) ∧
        (Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) ∈ T) ∧
        (∀ Y ⊆ Z, #Y = #Z - 2 →
          ∃ A ∈ T.erase (Z.filter (fun z => #{A ∈ T | z ∈ A} = 4)), A ⊆ Y)) := by
  classical
  constructor
  · rintro ⟨R, hR, hcov, hdeg⟩
    have hSR : Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) = R :=
      S_eq_R_of_deg_three hR hsub hdeg
    refine ⟨?_, by simpa [hSR] using hR, by simpa [hSR] using hcov⟩
    intro z hz
    exact (deg_erase_eq_three_of hR (hdeg z hz)).1
  · rintro ⟨hD, hSmem, hcov⟩
    set S := Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) with hSdef
    refine ⟨S, hSmem, hcov, ?_⟩
    intro z hz
    have hde := deg_erase (T := T) (R := S) (z := z) hSmem
    rcases hD z hz with h3 | h4
    · have hzS : z ∉ S := by
        intro hzS
        have hz' : z ∈ Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) := by
          simpa [hSdef] using hzS
        have : #{A ∈ T | z ∈ A} = 4 := (mem_filter.1 hz').2
        omega
      have : #{A ∈ T.erase S | z ∈ A} = #{A ∈ T | z ∈ A} := by simp [hde, hzS]
      omega
    · have hzS : z ∈ S := by
        rw [hSdef]
        exact mem_filter.2 ⟨hz, h4⟩
      have : #{A ∈ T.erase S | z ∈ A} = #{A ∈ T | z ∈ A} - 1 := by simp [hde, hzS]
      omega

end E624R20I

namespace Erdos624

theorem seven_row_omission_iff {U : Type*} [DecidableEq U]
    (Z : Finset U) (T : Finset (Finset U))
    (hZ : 2 ≤ #Z)
    (hT : #T = 7)
    (hsub : ∀ A ∈ T, A ⊆ Z) :
    (∃ R ∈ T,
        (∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ T.erase R, A ⊆ Y) ∧
        (∀ z ∈ Z, #{A ∈ T.erase R | z ∈ A} = 3)) ↔
      ((∀ z ∈ Z, #{A ∈ T | z ∈ A} = 3 ∨ #{A ∈ T | z ∈ A} = 4) ∧
        (Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) ∈ T) ∧
        (∀ Y ⊆ Z, #Y = #Z - 2 →
          ∃ A ∈ T.erase (Z.filter (fun z => #{A ∈ T | z ∈ A} = 4)), A ⊆ Y)) :=
  E624R20I.seven_row_omission_iff Z T hZ hT hsub

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U]
    (Z : Finset U) (T : Finset (Finset U))
    (hZ : 2 ≤ #Z)
    (hT : #T = 7)
    (hsub : ∀ A ∈ T, A ⊆ Z) :
    (∃ R ∈ T,
        (∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ T.erase R, A ⊆ Y) ∧
        (∀ z ∈ Z, #{A ∈ T.erase R | z ∈ A} = 3)) ↔
      ((∀ z ∈ Z, #{A ∈ T | z ∈ A} = 3 ∨ #{A ∈ T | z ∈ A} = 4) ∧
        (Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) ∈ T) ∧
        (∀ Y ⊆ Z, #Y = #Z - 2 →
          ∃ A ∈ T.erase (Z.filter (fun z => #{A ∈ T | z ∈ A} = 4)), A ⊆ Y)) :=
  Erdos624.seven_row_omission_iff Z T hZ hT hsub

