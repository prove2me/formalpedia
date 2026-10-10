-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.volume_compl_flowDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:59.126949+00:00
-- url     : https://prove2.me/submissions/34c5953c-9a1b-4568-b859-ce79a472608d

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.volume_compl_flowDom
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) : volume (flowDom t)ᶜ = 0 := by

  rcases eq_or_ne t 0 with rfl | ht
  · have h : (flowDom (0 : ℝ))ᶜ = (∅ : Set ℝ) := by
      ext x; simp [flowDom]
    simp [h]
  · have h : (flowDom t)ᶜ ⊆ {(-1 / t : ℝ)} := by
      intro x hx
      have hx' : 1 + t * x = 0 := by
        simpa [flowDom, not_not] using hx
      have : x = -1 / t := by field_simp; linarith
      simp [this]
    exact measure_mono_null h (by simp)
