-- Prove2me | solution 1 for BookProof.FockCubicQuarticStability.cubic_form_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:10:10.723533+00:00
-- url     : https://prove2.me/submissions/ee7110e8-7944-437d-9d68-8376f603731a

-- Generated from ChapterFockCubicQuarticStability.lean — solution of BookProof.FockCubicQuarticStability.cubic_form_eq
import Mathlib
import Definitions.Def_ChapterFockCubicQuarticStability
import Theorems.Thm_BookProof_FockCubicUnbounded_cubeA_apply
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
    (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
      = 2 * (inner ℂ (toLp (annA k (annA k u))) (toLp (creA k u)) : ℂ).re := by

  have hadd : ∀ a b : FockAlg, toLp (a + b) = toLp a + toLp b := fun a b => map_add toLpL a b
  have hcre : (inner ℂ (toLp u) (toLp (creA k (creA k (creA k u)))) : ℂ)
      = inner ℂ (toLp (annA k (annA k u))) (toLp (creA k u)) := by
    rw [inner_creA_right, inner_creA_right]
  have hann : (inner ℂ (toLp (annA k (annA k u))) (toLp (creA k u)) : ℂ)
      = inner ℂ (toLp (annA k (annA k (annA k u)))) (toLp u) := by
    rw [inner_creA_right]
  have hann' : (inner ℂ (toLp u) (toLp (annA k (annA k (annA k u)))) : ℂ)
      = (starRingEnd ℂ) (inner ℂ (toLp (annA k (annA k u))) (toLp (creA k u))) := by
    rw [hann, inner_conj_symm]
  rw [cubeA_apply, hadd, inner_add_right, Complex.add_re, hcre, hann', Complex.conj_re]
  ring
