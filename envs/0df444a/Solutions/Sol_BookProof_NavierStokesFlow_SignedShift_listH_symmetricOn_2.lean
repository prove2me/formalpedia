-- Prove2me | solution 2 for BookProof.NavierStokesFlow.SignedShift.listH_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T21:54:44.114563+00:00
-- url     : https://prove2.me/submissions/12f17334-c64e-42df-830a-8edd94df621a

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.listH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hopH_symmetricOn
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_cons
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesIkebeKato
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

set_option maxHeartbeats 1000000 in
theorem solution (L : List (SignedHop ι sym)) : SymmetricOn (maxDom sym) (listH L) := by

  induction L with
  | nil =>
      intro x y
      simp [listH]
  | cons S L ih =>
      intro x y
      have h₁ := SignedHop.hopH_symmetricOn S x y
      have h₂ := ih x y
      change (inner ℂ (listH (S :: L) x : L2I ι) (y : L2I ι) : ℂ)
        = inner ℂ (x : L2I ι) (listH (S :: L) y : L2I ι)
      simp only [listH_cons, LinearMap.add_apply, inner_add_left, inner_add_right]
      linear_combination h₁ + h₂
