-- Prove2me | solution 2 for BookProof.NavierStokesFlow.SignedShift.gaffH_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T22:10:14.720108+00:00
-- url     : https://prove2.me/submissions/15ac2027-d8e7-47d0-8046-82be63652f96

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.gaffH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_essentiallySelfAdjointOn_core
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
theorem solution :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((gaffH kap cst).comp (Submodule.inclusion (finiteModes_le_maxDom (gsym kap cst)))) := listH_essentiallySelfAdjointOn_core _ (gsym_ge_one kap cst)
