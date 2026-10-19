-- Prove2me | solution 1 for BookProof.NavierStokesFlow.BilinearEsa.embFun_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:23:48.147174+00:00
-- url     : https://prove2.me/submissions/666ffba5-35dc-4409-b4dd-0ecf631d0c5b

-- Generated from ChapterNavierStokesBilinearEsa.lean — solution of BookProof.NavierStokesFlow.BilinearEsa.embFun_of_ne
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {j j' : J} (a : ℕ → ℂ) (n : ℕ) (h : j' ≠ j) : embFun j a (n, j') = 0 := by

  simp [embFun, h]
