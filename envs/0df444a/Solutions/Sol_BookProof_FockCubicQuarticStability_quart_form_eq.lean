-- Prove2me | solution 1 for BookProof.FockCubicQuarticStability.quart_form_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:10:07.902172+00:00
-- url     : https://prove2.me/submissions/599438ed-63ae-49cb-ad78-49c4114d96bd

-- Generated from ChapterFockCubicQuarticStability.lean — solution of BookProof.FockCubicQuarticStability.quart_form_eq
import Mathlib
import Definitions.Def_ChapterFockCubicQuarticStability
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
theorem solution (k : ℕ) (u : FockAlg) :
    (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re = ‖toLp (annA k (annA k u))‖ ^ 2 := by

  have hq : quartA k u = creA k (creA k (annA k (annA k u))) := rfl
  have h : (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ)
      = inner ℂ (toLp (annA k (annA k u))) (toLp (annA k (annA k u))) := by
    rw [hq, inner_creA_right, inner_creA_right]
  rw [h, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]
