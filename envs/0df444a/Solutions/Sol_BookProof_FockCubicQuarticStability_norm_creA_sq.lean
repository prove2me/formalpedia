-- Prove2me | solution 1 for BookProof.FockCubicQuarticStability.norm_creA_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:10:12.00206+00:00
-- url     : https://prove2.me/submissions/885fa074-4f12-40d6-85d3-20da442d3039

-- Generated from ChapterFockCubicQuarticStability.lean — solution of BookProof.FockCubicQuarticStability.norm_creA_sq
import Mathlib
import Definitions.Def_ChapterFockCubicQuarticStability
import Theorems.Thm_BookProof_FockSecondQuantization_ccr_annA_creA
import Theorems.Thm_BookProof_FockSecondQuantization_inner_creA_left
import Theorems.Thm_BookProof_FockSecondQuantization_inner_creA_right
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockCubicQuarticStability



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicUnbounded
open BookProof.FockSecondQuantization

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (v : FockAlg) :
    ‖toLp (creA k v)‖ ^ 2 = ‖toLp (annA k v)‖ ^ 2 + ‖toLp v‖ ^ 2 := by

  have hadd : ∀ a b : FockAlg, toLp (a + b) = toLp a + toLp b := fun a b => map_add toLpL a b
  have hccr : annA k (creA k v) = creA k (annA k v) + v := by
    have h := ccr_annA_creA k v
    have := sub_eq_iff_eq_add.mp h
    simpa [add_comm] using this
  have key : (inner ℂ (toLp (creA k v)) (toLp (creA k v)) : ℂ)
      = inner ℂ (toLp (annA k v)) (toLp (annA k v)) + inner ℂ (toLp v) (toLp v) := by
    rw [inner_creA_left, hccr, hadd, inner_add_right, inner_creA_right]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at key
  exact_mod_cast key
