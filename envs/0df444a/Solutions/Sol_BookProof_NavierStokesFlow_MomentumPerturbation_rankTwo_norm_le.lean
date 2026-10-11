-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:41:23.641028+00:00
-- url     : https://prove2.me/submissions/22576bb8-60bf-489b-bcb9-222f3a4790bd

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — solution of BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_norm_le
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation





open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (u w x : L2I ι) : ‖rankTwo u w x‖ ≤ 2 * (‖u‖ * ‖w‖) * ‖x‖ := by

  refine le_trans (norm_add_le _ _) ?_
  rw [norm_smul, norm_smul]
  have h1 : ‖(inner ℂ u x : ℂ)‖ ≤ ‖u‖ * ‖x‖ := norm_inner_le_norm u x
  have h2 : ‖(inner ℂ w x : ℂ)‖ ≤ ‖w‖ * ‖x‖ := norm_inner_le_norm w x
  nlinarith [norm_nonneg u, norm_nonneg w, norm_nonneg x,
    mul_nonneg (norm_nonneg u) (norm_nonneg x), mul_nonneg (norm_nonneg w) (norm_nonneg x)]
