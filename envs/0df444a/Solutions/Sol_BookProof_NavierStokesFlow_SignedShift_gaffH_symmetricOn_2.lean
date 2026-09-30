-- Prove2me | solution 2 for BookProof.NavierStokesFlow.SignedShift.gaffH_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T22:00:34.957292+00:00
-- url     : https://prove2.me/submissions/3c9a992c-0b66-4466-9cc6-70860a70f502

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.gaffH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_symmetricOn
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber

variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)


































variable {sym : ι → ℝ}














open BookProof.NavierStokesFlow.HermiteFarisLavine

variable (kap cst : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution : SymmetricOn (maxDom (gsym kap cst)) (gaffH kap cst) := listH_symmetricOn _
