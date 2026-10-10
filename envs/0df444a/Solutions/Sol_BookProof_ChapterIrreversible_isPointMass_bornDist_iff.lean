-- Prove2me | solution 1 for BookProof.ChapterIrreversible.isPointMass_bornDist_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:15:47.160695+00:00
-- url     : https://prove2.me/submissions/27bb8a28-624c-4914-83d9-5ac8353e0876

-- Generated from ChapterIrreversible.lean — solution of BookProof.ChapterIrreversible.isPointMass_bornDist_iff
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) :
    IsPointMass (bornDist v) ↔ IsDeterministicColumn v := by

  constructor <;> intro h;
  · obtain ⟨ a, ha₁, ha₂ ⟩ := h;
    exact ⟨ a, by contrapose! ha₁; simp_all [ bornDist ],
      fun b hb => by specialize ha₂ b hb; simp_all [ bornDist ] ⟩;
  · obtain ⟨ a, ha₁, ha₂ ⟩ := h; use a; simp_all  ;
    simp_all [ Finset.sum_eq_single a, bornDist ]
