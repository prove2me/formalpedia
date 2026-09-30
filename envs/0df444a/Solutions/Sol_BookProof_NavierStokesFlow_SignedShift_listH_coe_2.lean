-- Prove2me | solution 2 for BookProof.NavierStokesFlow.SignedShift.listH_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T21:10:01.922415+00:00
-- url     : https://prove2.me/submissions/cae32df3-826b-4d6b-bbe6-2b2832b588c8

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.listH_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_cons
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hopH_coe
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
theorem solution {sym : ι → ℝ} (L : List (SignedHop ι sym)) (x : maxDom sym) (γ : ι) :
    ((listH L x : L2I ι) : ι → ℂ) γ
      = (L.map (fun S => S.hFun ((x : L2I ι) : ι → ℂ) γ)).sum := by

  induction L with
  | nil => simp [listH]
  | cons S L ih =>
      rw [listH_cons]
      simp only [LinearMap.add_apply, lp.coeFn_add, Pi.add_apply, List.map_cons,
        List.sum_cons, SignedHop.hopH_coe, ih]
