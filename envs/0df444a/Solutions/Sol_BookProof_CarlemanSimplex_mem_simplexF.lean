-- Prove2me | solution 1 for BookProof.CarlemanSimplex.mem_simplexF
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T18:57:40.513105+00:00
-- url     : https://prove2.me/submissions/683d1047-9760-4ae6-8eb2-79fa876d69e3

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.mem_simplexF
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_apply_le_deg
import Theorems.Thm_BookProof_HermiteCarleman_mem_cube_inc
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}


set_option maxHeartbeats 1000000 in
theorem solution {d N : ℕ} {a : Fin d →₀ ℕ} : a ∈ simplexF d N ↔ deg a ≤ N := by

  classical
  rw [simplexF, Finset.mem_filter, mem_cube_inc]
  exact ⟨fun h => h.2, fun h => ⟨fun i => le_trans (apply_le_deg a i) h, h⟩⟩
