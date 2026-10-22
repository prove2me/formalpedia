-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.cubeA_coord
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T11:51:57.145514+00:00
-- url     : https://prove2.me/submissions/45a7e48e-b574-406f-b038-8d52c6c51e58

-- Generated from ChapterFockCubicUnbounded.lean — solution of BookProof.FockCubicUnbounded.cubeA_coord
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Theorems.Thm_BookProof_FockCubicUnbounded_cubeA_apply
import Theorems.Thm_BookProof_FockSecondQuantization_annA_apply
import Theorems.Thm_BookProof_FockSecondQuantization_creA_apply
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockCubicUnbounded



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockSecondQuantization

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (x : FockAlg) (γ : Conf) :
    cubeA k x γ
      = ((Real.sqrt (γ k) : ℝ) : ℂ) * ((Real.sqrt ((dn k γ) k) : ℝ) : ℂ)
          * ((Real.sqrt ((dn k (dn k γ)) k) : ℝ) : ℂ) * x (dn k (dn k (dn k γ)))
        + ((Real.sqrt ((γ k : ℝ) + 1) : ℝ) : ℂ)
            * ((Real.sqrt (((up k γ) k : ℝ) + 1) : ℝ) : ℂ)
            * ((Real.sqrt (((up k (up k γ)) k : ℝ) + 1) : ℝ) : ℂ)
            * x (up k (up k (up k γ))) := by

  rw [cubeA_apply, Finsupp.add_apply, creA_apply, creA_apply, creA_apply,
    annA_apply, annA_apply, annA_apply]
  ring
