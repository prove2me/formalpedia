-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ThreeComponent.velH_coe_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:30:53.625331+00:00
-- url     : https://prove2.me/submissions/7c01dfa1-0ab0-4e81-b113-54e68cb55d82

-- Generated from ChapterNavierStokesThreeComponent.lean — solution of BookProof.NavierStokesFlow.ThreeComponent.velH_coe_single
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
import Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velState_coe
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hFun_single
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_coe
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift





































variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (β γ : Vel) :
    ((velH A c (velState A c β) : L2I Vel) : Vel → ℂ) γ
      = ((hopList A c).map (fun S => Complex.I *
          ((if γ = S.shift β then (S.amp β : ℂ) else 0)
            - (if S.shift γ = β then (S.amp γ : ℂ) else 0)))).sum := by

  rw [velH, SignedShift.listH_coe]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro S _
  exact S.hFun_single (velState_coe A c β) γ
