-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.conj_mul_hFun
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:46.591526+00:00
-- url     : https://prove2.me/submissions/f5523840-fa93-4ea2-9d33-e4d0e8b73fb5

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.conj_mul_hFun
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

set_option maxHeartbeats 1000000 in
theorem solution (κ : ℝ) (X Y : ℕ → ℂ) (m : ℕ) :
    (starRingEnd ℂ) (X m) * hFun κ Y m
      = -Complex.I * crossA κ X Y m + Complex.I * shift2 (crossB κ X Y) m := by

  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;>
      simp [hFun, crossA, shift2, Complex.ext_iff] <;>
      constructor <;> ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    simp only [hFun, crossA, crossB, shift2_add_two]
    ring
