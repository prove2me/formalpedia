-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.momFock_no_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:09:02.34001+00:00
-- url     : https://prove2.me/submissions/c9f1267a-3644-49cc-b852-8bb8631d0319

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.momFock_no_eigenvector
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_fockR_total_level
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian



open MeasureTheory



open FullEsa FockContinuum
open BookProof.NavierStokesFlow.ThreeComponent

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution {lam : ℂ} (hlam : lam ≠ 0) (v : momFock.core)
    (hv : ((momFock.data.hFull v : momFock.core) : Lp ℂ 2 fockR)
      = lam • ((v : Lp ℂ 2 fockR))) :
    ((v : Lp ℂ 2 fockR)) = 0 := by

  refine momFock.hFull_eq_zero_of_eigen ?_ v hv
  by_cases him : lam.im = 0
  · have hre : lam.re ≠ 0 := fun h =>
      hlam (Complex.ext (by simpa using h) (by simpa using him))
    have hset : {x : ParcelConf ℝ | (momFock.total x : ℂ) = lam}
        = {x : ParcelConf ℝ | momFock.total x = lam.re} := by
      ext x
      constructor
      · intro h; simpa using congrArg Complex.re h
      · intro h
        simp only [Set.mem_setOf_eq] at h
        exact Complex.ext (by simpa using h) (by simpa using him.symm)
    rw [hset]
    exact fockR_total_level hre
  · have hempty : {x : ParcelConf ℝ | (momFock.total x : ℂ) = lam} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
      have h2 := congrArg Complex.im hx
      simp only [Complex.ofReal_im] at h2
      exact him h2.symm
    rw [hempty, measure_empty]
