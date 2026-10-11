-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.invMap_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:34:51.449605+00:00
-- url     : https://prove2.me/submissions/bf781eec-94de-4d6c-b024-546e46895af0

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.invMap_ne_zero
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal
open BookProof.OdeUnitaryFlow

theorem solution{x : ℝ} (hx : x ≠ 0) : invMap x ≠ 0 := by
  unfold invMap
  exact div_ne_zero (by norm_num) hx
