-- Prove2me | solution 1 for BookProof.GroupAverage.UnitaryRep.act_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:29:53.260454+00:00
-- url     : https://prove2.me/submissions/bcf11664-2d94-478b-9ba4-43f230d9e30c

-- Generated from ChapterGroupAverageEsa.lean — solution of BookProof.GroupAverage.UnitaryRep.act_sum
import Mathlib
import Definitions.Def_ChapterGroupAverageEsa
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_mul
open BookProof.GroupAverage
open BookProof.GroupAverage.UnitaryRep




open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]
variable (rep : UnitaryRep G F)
variable (G) in

set_option maxHeartbeats 1000000 in
theorem solution (h : G) (x : F) :
    rep.act h (∑ g : G, rep.act g x) = ∑ g : G, rep.act g x := by

  rw [map_sum]
  have : ∀ g : G, rep.act h (rep.act g x) = rep.act (h * g) x := by
    intro g; rw [rep.act_mul]
  simp only [this]
  exact Fintype.sum_bijective (fun g => h * g) (Group.mulLeft_bijective h) _ _ (fun g => rfl)
