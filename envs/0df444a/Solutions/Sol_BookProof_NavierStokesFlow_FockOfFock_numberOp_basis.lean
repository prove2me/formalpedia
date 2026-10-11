-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.numberOp_basis
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:25:31.883462+00:00
-- url     : https://prove2.me/submissions/3f116633-7fe4-4b24-a53b-da9f636d543b

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.numberOp_basis
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_annih_basis
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_creat_basis
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]

set_option maxHeartbeats 1000000 in
theorem solution (m : M) (n : Conf M) :
    numberOp m (fockBasis n) = ((n m : ℝ) : ℂ) • fockBasis n := by

  rcases Nat.eq_zero_or_pos (n m) with h | h
  · simp [numberOp, annih_basis, h]
  · have h1 : ((n - Finsupp.single m 1 : Conf M) m : ℝ) + 1 = (n m : ℝ) := by
      have hval : (n - Finsupp.single m 1 : Conf M) m = n m - 1 := by simp
      rw [hval, Nat.cast_sub h]
      ring
    have h2 : (n - Finsupp.single m 1 : Conf M) + Finsupp.single m 1 = n :=
      sub_single_add_single h
    have hsq : Real.sqrt (n m : ℝ) * Real.sqrt (n m : ℝ) = (n m : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    simp only [numberOp, LinearMap.comp_apply, annih_basis, map_smul, creat_basis, h1, h2,
      smul_smul, ← Complex.ofReal_mul, hsq]
