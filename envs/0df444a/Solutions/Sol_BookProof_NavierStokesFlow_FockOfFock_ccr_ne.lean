-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.ccr_ne
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:44:06.389588+00:00
-- url     : https://prove2.me/submissions/ecc1eda9-8526-49c3-b629-1197c42c30f6

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

variable {M : Type*}

private theorem annih_coe (m : M) (f : FockDom M) (n : Conf M) :
    (((annih m f : FockDom M) : FockL2 M) : Conf M → ℂ) n
      = (Real.sqrt (n m + 1) : ℂ) * ((f : FockL2 M) : Conf M → ℂ) (n + Finsupp.single m 1) := rfl

private theorem creat_coe (m : M) (f : FockDom M) (n : Conf M) :
    (((creat m f : FockDom M) : FockL2 M) : Conf M → ℂ) n
      = (Real.sqrt (n m) : ℂ) * ((f : FockL2 M) : Conf M → ℂ) (n - Finsupp.single m 1) := rfl

theorem solution [DecidableEq M] {m m' : M} (h : m ≠ m') :
    (annih m).comp (creat m') - (creat m').comp (annih m) = 0 := by
  ext f n
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    Submodule.coe_sub, Pi.sub_apply, annih_coe, creat_coe, lp.coeFn_sub, Submodule.coe_zero,
    lp.coeFn_zero, Pi.zero_apply]
  have hm' : ((n + Finsupp.single m 1 : Conf M) m' : ℝ) = (n m' : ℝ) := by
    simp [Ne.symm h]
  have hm : ((n - Finsupp.single m' 1 : Conf M) m : ℝ) + 1 = (n m : ℝ) + 1 := by
    simp [h]
  have harg : (n + Finsupp.single m 1 : Conf M) - Finsupp.single m' 1
      = (n - Finsupp.single m' 1 : Conf M) + Finsupp.single m 1 := by
    ext j
    rcases eq_or_ne j m with rfl | hj
    · simp [Ne.symm h]
    · rcases eq_or_ne j m' with rfl | hj'
      · simp [hj]
      · simp [Ne.symm hj, Ne.symm hj']
  rw [hm', hm, harg]
  ring


#print axioms solution
