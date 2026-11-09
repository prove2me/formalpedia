-- Prove2me | solution 1 for BookProof.FockWeightedSchur.oscCol_entries_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T10:19:43.1703+00:00
-- url     : https://prove2.me/submissions/12e8c497-3d51-4cba-8453-8a8cc6d0fd62

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.oscCol_entries_unbounded
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_norm_oscCol_apply
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (C : ℝ) : ∃ k : ℕ, C ≤ ‖(oscCol k) (k + 1)‖ := by

  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ 2)
  refine ⟨n, ?_⟩
  rw [norm_oscCol_apply, if_pos rfl]
  by_cases hC : C ≤ 0
  · exact le_trans hC (Real.sqrt_nonneg _)
  · have hC : 0 < C := lt_of_not_ge hC
    have h1 : C ^ 2 < (n : ℝ) + 1 := by linarith
    have h2 : Real.sqrt (C ^ 2) < Real.sqrt ((n : ℝ) + 1) := by
      exact Real.sqrt_lt_sqrt (sq_nonneg C) h1
    rw [Real.sqrt_sq hC.le] at h2
    exact h2.le
