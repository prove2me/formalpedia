-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.mem_ibd
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T18:45:58.882733+00:00
-- url     : https://prove2.me/submissions/1a3690ba-bf8d-4ad2-a315-815d95184714

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.mem_ibd
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Theorems.Thm_BookProof_HermiteCarleman_mem_cube_inc
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanGeneralHop




open Finset
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {N : ℕ} {m b : Fin d →₀ ℕ} :
    b ∈ ibd d N m ↔ (∀ k, b k ≤ N + 1) ∧ (∀ k, m k ≤ b k) ∧ ¬ (∀ k, b k ≤ N) := by

  classical
  rw [ibd, Finset.mem_filter, mem_cube_inc]
