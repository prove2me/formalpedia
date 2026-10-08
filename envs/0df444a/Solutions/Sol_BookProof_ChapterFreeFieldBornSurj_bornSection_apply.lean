-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSurj.bornSection_apply
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:59:45.513831+00:00
-- url     : https://prove2.me/submissions/5d07c726-c05f-45bc-acc3-1e9d6a3d09fd

-- Generated from ChapterFreeFieldBornSurj.lean — theorem BookProof.ChapterFreeFieldBornSurj.bornSection_apply
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornSurj

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn

theorem solution (p : Fin n → ℝ) (k : Fin n) :
    bornSection p k = Real.sqrt (p k) := by   rfl


#print axioms solution
