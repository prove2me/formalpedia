-- Prove2me | solution 1 for FairGuarantees.DivideChoose.divider_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:54:09.777597+00:00
-- url     : https://prove2.me/submissions/c3e24f68-a027-4041-9406-48f25a838179

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting

open FairGuarantees.DivideChoose

theorem solution {d n : ℕ} (hn : 0 < n) {Ω : Set (E d)} (hΩ : IsManna Ω)
    {u : Set (E d) → ℝ} (hu : IsUtility Ω u) {Q : Fin n → Set (E d)} (hQ : IsPartition Ω Ω n Q)
    (Old : Finset (Fin n)) (hfresh : ∃ j, j ∉ Old)
    (hOld : ∀ j ∈ Old, u (Q j) < minMax Ω u n)
    (hequi : ∀ j ∉ Old, ∀ k ∉ Old, u (Q j) = u (Q k)) :
    ∀ j ∉ Old, minMax Ω u n ≤ u (Q j) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨C, hC⟩ := hu.2.1
  have hle : minMax Ω u n ≤ ⨆ j, u (Q j) := by
    apply csInf_le
    · refine ⟨-C, ?_⟩
      rintro x ⟨P, hP, rfl⟩
      have h0 := hC (P ⟨0, hn⟩) (hP.1 ⟨0, hn⟩).1
      have : u (P ⟨0, hn⟩) ≤ ⨆ i, u (P i) :=
        le_ciSup (f := fun i => u (P i)) (Set.finite_range _).bddAbove _
      linarith [(abs_le.mp h0).1]
    · exact ⟨Q, hQ, rfl⟩
  obtain ⟨j0, hj0⟩ := exists_eq_ciSup_of_finite (f := fun j => u (Q j))
  have hj0o : j0 ∉ Old := by
    intro hjo
    have := hOld j0 hjo
    rw [hj0] at this
    linarith
  intro j hj
  rw [hequi j hj j0 hj0o, hj0]
  exact hle
