-- Prove2me | solution 1 for BookProof.FockWeightedSchur.wcol_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T09:54:15.589464+00:00
-- url     : https://prove2.me/submissions/f81f8f32-1ff1-4430-9f90-fc5351e0239b

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.wcol_le
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_sum_le_of_vanishing
import Theorems.Thm_BookProof_FockWeightedSchur_w_pos
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
theorem solution (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hK : WColBound w col K) (j : ℕ)
    (L : Finset ℕ) : ∑ k ∈ L, ‖(col k) j‖ / w k ≤ K := by

  classical
  have hswap : ∀ k, ‖(col k) j‖ = ‖(col j) k‖ := by
    intro k
    rw [hherm j k]
    simp
  rw [Finset.sum_congr rfl fun k _ => by rw [hswap k]]
  refine le_trans (sum_le_of_vanishing (S := (col j).support)
    (fun k => div_nonneg (norm_nonneg _) (w_pos hw k).le) ?_) (hK j)
  intro k hk
  rw [Finsupp.notMem_support_iff.mp hk]
  simp
