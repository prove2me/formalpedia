-- Prove2me | solution 1 for FairGuarantees.DivideChoose.chooser_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:53:41.032558+00:00
-- url     : https://prove2.me/submissions/e65a7b9d-90de-4126-93af-d9979b1e8cb5

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting

open FairGuarantees.DivideChoose

theorem solution {d n : ℕ} (hn : 0 < n) {Ω : Set (E d)} (hΩ : IsManna Ω)
    {u : Set (E d) → ℝ} (hu : IsUtility Ω u) {Q : Fin n → Set (E d)} (hQ : IsPartition Ω Ω n Q)
    (Old : Finset (Fin n)) (hOld : ∀ j ∈ Old, u (Q j) < minMax Ω u n) :
    ∃ j ∉ Old, minMax Ω u n ≤ u (Q j) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨C, hC⟩ := hu.2.1
  have hle : minMax Ω u n ≤ ⨆ j, u (Q j) := by
    apply csInf_le
    · refine ⟨-C, ?_⟩
      rintro x ⟨P, hP, rfl⟩
      have h0 := hC (P ⟨0, hn⟩) (hP.1 ⟨0, hn⟩).1
      have : u (P ⟨0, hn⟩) ≤ ⨆ i, u (P i) := le_ciSup (f := fun i => u (P i)) (Set.finite_range _).bddAbove _
      linarith [(abs_le.mp h0).1]
    · exact ⟨Q, hQ, rfl⟩
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j => u (Q j))
  refine ⟨j, fun hjo => ?_, by rw [hj]; exact hle⟩
  have := hOld j hjo
  rw [hj] at this
  linarith
