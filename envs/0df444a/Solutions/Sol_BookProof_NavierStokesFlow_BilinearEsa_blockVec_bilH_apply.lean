-- Prove2me | solution 1 for BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:23:50.749628+00:00
-- url     : https://prove2.me/submissions/3ddc3252-186d-4d9b-bb63-311020a39fe6

-- Generated from ChapterNavierStokesBilinearEsa.lean — solution of BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (κ : J → ℝ) (x : lpFiniteModes (ℕ × J)) (j : J) (n : ℕ) :
    ((bilH κ x : L2I (ℕ × J)) : ℕ × J → ℂ) (n, j)
      = hFun (κ j) (fun m => ((x : L2I (ℕ × J)) : ℕ × J → ℂ) (m, j)) n := rfl
