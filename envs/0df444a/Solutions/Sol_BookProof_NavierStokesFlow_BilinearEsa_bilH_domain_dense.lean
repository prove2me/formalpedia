-- Prove2me | solution 1 for BookProof.NavierStokesFlow.BilinearEsa.bilH_domain_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:23:59.092242+00:00
-- url     : https://prove2.me/submissions/110df88f-0cf9-4f2c-8df7-ea3bd92b83ce

-- Generated from ChapterNavierStokesBilinearEsa.lean — solution of BookProof.NavierStokesFlow.BilinearEsa.bilH_domain_dense
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution :
    Dense ((lpFiniteModes (ℕ × J) : Submodule ℂ (L2I (ℕ × J))) : Set (L2I (ℕ × J))) := lpFiniteModes_dense
