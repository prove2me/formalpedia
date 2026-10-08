-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornQuotient.continuous_bornMapSphere
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:27:54.54899+00:00
-- url     : https://prove2.me/submissions/fd97e246-6b1e-42eb-a1f5-56d80105914e

-- Generated from ChapterFreeFieldBornQuotient.lean — theorem BookProof.ChapterFreeFieldBornQuotient.continuous_bornMapSphere
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Mathlib
import Definitions.Def_ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornQuotient

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont

theorem solution : Continuous (bornMapSphere n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  exact ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) k).comp continuous_subtype_val).pow 2

#print axioms solution
