-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.hasDerivAt_invMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:59:02.725133+00:00
-- url     : https://prove2.me/submissions/d46d93d6-7008-4870-a1a7-c9808fc939b6

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.hasDerivAt_invMap
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution {x : ℝ} (hx : x ≠ 0) : HasDerivAt invMap ((x ^ 2)⁻¹) x := by

  have h := (hasDerivAt_const x (-1 : ℝ)).div (hasDerivAt_id x) hx
  have heq : (0 * x - (-1 : ℝ) * 1) / x ^ 2 = (x ^ 2)⁻¹ := by
    field_simp
    ring
  simp only [invMap, Pi.div_def, id_eq, heq] at h
  exact h
