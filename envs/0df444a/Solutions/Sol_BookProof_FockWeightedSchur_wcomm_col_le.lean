-- Prove2me | solution 1 for BookProof.FockWeightedSchur.wcomm_col_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T09:54:59.990374+00:00
-- url     : https://prove2.me/submissions/0a20573c-bd68-4b78-bca7-925d105b025a

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.wcomm_col_le
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_wcomm_row_le
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.FockSecondQuantization

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hB : WCommBound w col B)
    (j : ℕ) (L : Finset ℕ) :
    ∑ k ∈ L, ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j) ≤ B := by

  classical
  have hterm : ∀ k, ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j)
      = ‖(col j) k‖ * |w k ^ 2 - w j ^ 2| / (w j * w k) := by
    intro k
    have h1 : ‖(col k) j‖ = ‖(col j) k‖ := by rw [hherm j k]; simp
    rw [h1, abs_sub_comm, mul_comm (w k) (w j)]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  exact wcomm_row_le hw hB j L
