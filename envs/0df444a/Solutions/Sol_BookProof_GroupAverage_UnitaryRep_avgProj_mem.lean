-- Prove2me | solution 1 for BookProof.GroupAverage.UnitaryRep.avgProj_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T15:06:03.427984+00:00
-- url     : https://prove2.me/submissions/64e8e4d5-6a10-46c2-9e9a-5e29c47e4fb5

-- Generated from ChapterGroupAverageEsa.lean — solution of BookProof.GroupAverage.UnitaryRep.avgProj_mem
import Mathlib
import Definitions.Def_ChapterGroupAverageEsa
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_apply
open BookProof.GroupAverage
open BookProof.GroupAverage.UnitaryRep




open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]
variable (rep : UnitaryRep G F)
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (hD : ∀ (g : G) (x : F), x ∈ D → rep.act g x ∈ D) :
    ∀ x ∈ D, rep.avgProj x ∈ D := by

  intro x hx
  rw [avgProj_apply]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun g _ => hD g x hx))
