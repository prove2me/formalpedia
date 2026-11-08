-- Prove2me | solution 1 for DRSubmodHull.observation_5_7_valid_candidates_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:56:11.866873+00:00
-- url     : https://prove2.me/submissions/b48d0cac-f612-487d-a7b8-4cf63f4fb0df

import Mathlib
import Definitions.Def_DRSubmodHull_IsPermFinderOutput

set_option autoImplicit false

open DRSubmodHull in
theorem solution {V : Type*} [Fintype V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u)
    (L : List V) (hL : IsValidPartialPerm A N u L) (hlen : L.length < Fintype.card V) :
    (validCandidates A N u L).Nonempty := by
  obtain ⟨δ, ⟨hv1, hv2, hv3⟩, hLeq⟩ := hL
  have key : ∀ x, x ∈ (List.ofFn δ).take L.length ↔ (δ.symm x).val < L.length := by
    intro x
    rw [List.mem_take_iff_getElem]
    simp only [List.length_ofFn, List.getElem_ofFn]
    constructor
    · rintro ⟨j, hj, rfl⟩
      simp only [Equiv.symm_apply_apply]
      exact lt_of_lt_of_le hj (min_le_left _ _)
    · intro h
      exact ⟨(δ.symm x).val, lt_min h (δ.symm x).isLt, by simp⟩
  have memL : ∀ x, x ∈ L ↔ (δ.symm x).val < L.length := by
    intro x
    constructor
    · intro hx
      rw [hLeq] at hx
      exact (key x).1 hx
    · intro h
      rw [hLeq]
      exact (key x).2 h
  have hi : (δ.symm (δ ⟨L.length, hlen⟩)).val = L.length := by simp
  refine ⟨δ ⟨L.length, hlen⟩, ?_, ?_, ?_, ?_⟩
  · rw [memL, hi]; exact lt_irrefl _
  · rintro ⟨j, hij, hne, hjL, hu⟩
    have h1 := hv1 _ j (Ne.symm hne) hij hu.symm
    rw [Fin.lt_iff_val_lt_val, hi] at h1
    exact hjL ((memL j).2 h1)
  · rintro ⟨hpsi, hlt, hc⟩
    have hpos := hstd.2.2.1 (δ ⟨L.length, hlen⟩)
    have hfl : Int.floor (u (δ ⟨L.length, hlen⟩)) = 0 := by
      rw [Int.floor_eq_zero_iff]; exact ⟨hpos.le, hlt⟩
    have h1 := hv2 _ hpsi hfl
    rw [Fin.lt_iff_val_lt_val, hi] at h1
    exact hc ((memL _).2 h1)
  · rintro ⟨hpsi, ⟨j, hji, hjL, hu⟩, hc⟩
    have h1 := hv3 _ hpsi j hji hu
    obtain ⟨ρ, hρ, _, _⟩ := hP42 _ hpsi
    have hex : ∃ j, A (δ ⟨L.length, hlen⟩) j := ⟨ρ, (hρ ρ).2 rfl⟩
    have hch : child A (δ ⟨L.length, hlen⟩) = hex.choose := by
      unfold child; rw [dif_pos hex]
    have hA : A (δ ⟨L.length, hlen⟩) (child A (δ ⟨L.length, hlen⟩)) := by
      rw [hch]; exact hex.choose_spec
    have hne : child A (δ ⟨L.length, hlen⟩) ≠ δ ⟨L.length, hlen⟩ := by
      intro heq
      rw [heq] at hA
      exact hstd.1.2 _ (Relation.TransGen.single hA)
    have hne' : (δ.symm (child A (δ ⟨L.length, hlen⟩))).val ≠ L.length := by
      intro hv
      apply hne
      have : δ.symm (child A (δ ⟨L.length, hlen⟩)) = ⟨L.length, hlen⟩ := Fin.ext hv
      have h2 := congrArg δ this
      rwa [Equiv.apply_symm_apply] at h2
    have hcL : ¬ (δ.symm (child A (δ ⟨L.length, hlen⟩))).val < L.length :=
      fun h => hc ((memL _).2 h)
    apply h1
    rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, hi]
    exact ⟨(memL j).1 hjL, by omega⟩
