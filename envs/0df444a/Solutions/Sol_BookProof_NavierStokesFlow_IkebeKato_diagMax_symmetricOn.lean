-- Prove2me | solution 1 for BookProof.NavierStokesFlow.IkebeKato.diagMax_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T13:16:49.068749+00:00
-- url     : https://prove2.me/submissions/628f1e46-3b83-493a-b12f-71b343098332

-- Generated from ChapterNavierStokesIkebeKato.lean — solution of BookProof.NavierStokesFlow.IkebeKato.diagMax_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato



open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (c : ι → ℝ) : SymmetricOn (maxDom c) (diagMax c) := by

  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  simp only [RCLike.inner_apply, diagMax_coe, map_mul, Complex.conj_ofReal]
  ring
