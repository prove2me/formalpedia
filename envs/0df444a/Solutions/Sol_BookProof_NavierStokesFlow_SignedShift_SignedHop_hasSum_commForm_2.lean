-- Prove2me | solution 2 for BookProof.NavierStokesFlow.SignedShift.SignedHop.hasSum_commForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T21:33:29.258313+00:00
-- url     : https://prove2.me/submissions/1cef98a8-1e40-4f2e-be24-9e465c2c8a91

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.SignedHop.hasSum_commForm
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hasSum_inner_hopH_left
import Theorems.Thm_BookProof_FarisLavine_commForm_eq
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
theorem solution (x : maxDom sym) :
    HasSum (fun β => 2 * S.step * (S.amp β
        * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β)
            * ((x : L2I ι) : ι → ℂ) (S.shift β)).re))
      (commForm (hopH S) (diagMax sym) x) := by

  have hL := hasSum_inner_hopH_left S x (diagMax sym x : L2I ι)
  have hIm := Complex.hasSum_im hL
  have hpt : ∀ β, (-Complex.I * S.crossA ((x : L2I ι) : ι → ℂ)
        (((diagMax sym x : L2I ι) : ι → ℂ)) β
      + Complex.I * S.crossB ((x : L2I ι) : ι → ℂ)
        (((diagMax sym x : L2I ι) : ι → ℂ)) β).im
      = -S.step * (S.amp β * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β)
        * ((x : L2I ι) : ι → ℂ) (S.shift β)).re) := by
    intro β
    simp only [crossA, crossB, diagMax_coe, S.sym_step]
    simp [Complex.add_im, Complex.mul_im, Complex.mul_re]
    ring
  have hIm' : HasSum (fun β => -S.step * (S.amp β
      * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β)
        * ((x : L2I ι) : ι → ℂ) (S.shift β)).re))
      (inner ℂ (hopH S x : L2I ι) (diagMax sym x : L2I ι) : ℂ).im := by
    refine hIm.congr_fun ?_
    intro β
    exact (hpt β).symm
  have hres := hIm'.mul_left (-2)
  rw [commForm_eq]
  refine hres.congr_fun ?_
  intro β
  ring
