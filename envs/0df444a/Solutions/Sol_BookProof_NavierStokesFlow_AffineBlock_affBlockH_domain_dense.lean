-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineBlock.affBlockH_domain_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:23:45.663556+00:00
-- url     : https://prove2.me/submissions/3e737370-cae3-43cd-aebc-4d7a83d696cf

-- Generated from ChapterNavierStokesAffineBlockEsa.lean — solution of BookProof.NavierStokesFlow.AffineBlock.affBlockH_domain_dense
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineBlock



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution :
    Dense ((lpFiniteModes (ℕ × J) : Submodule ℂ (L2I (ℕ × J))) : Set (L2I (ℕ × J))) := lpFiniteModes_dense
