-- Prove2me | solution 2 for BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T21:46:46.908542+00:00
-- url     : https://prove2.me/submissions/1f2cab96-e25e-4895-8bd0-705b87c8006c

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hasSum_inner_hopH_left
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hasSum_inner_hopH_right
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber

variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

set_option maxHeartbeats 1000000 in
theorem solution : SymmetricOn (maxDom sym) (hopH S) := by

  intro x y
  exact (hasSum_inner_hopH_left S x (y : L2I ι)).unique (hasSum_inner_hopH_right S x y)
