-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBorn.measurable_bornMap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:34:19.041657+00:00
-- url     : https://prove2.me/submissions/6ec62859-608b-44a3-a1f9-98c322724f56

import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn

set_option autoImplicit false

open BookProof.ChapterFreeFieldBorn MeasureTheory BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport in
theorem solution {n : ℕ} : Measurable (bornMap : EuclideanSpace ℝ (Fin n) → _) := by
  have hc : Continuous (bornMap : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) := by
    unfold bornMap
    refine continuous_pi fun k => ?_
    exact ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) k)).pow 2
  exact hc.measurable
