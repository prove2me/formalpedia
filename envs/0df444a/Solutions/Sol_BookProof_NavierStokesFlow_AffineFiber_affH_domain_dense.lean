-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineFiber.affH_domain_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T15:05:52.545686+00:00
-- url     : https://prove2.me/submissions/62497a5d-56dd-4e0a-82ec-aea5ef0b28aa

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — solution of BookProof.NavierStokesFlow.AffineFiber.affH_domain_dense
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

variable {ι : Type*}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (P : PairShift ι)

set_option maxHeartbeats 1000000 in
theorem solution :
    Dense ((lpFiniteModes ℕ : Submodule ℂ (L2I ℕ)) : Set (L2I ℕ)) := lpFiniteModes_dense
