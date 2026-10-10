-- Prove2me | solution 1 for BookProof.HalfLineLimitCircle.deficiencyVec_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:40:44.76888+00:00
-- url     : https://prove2.me/submissions/b036368d-bc44-4c00-9f6e-3b00eb0f772e

-- Generated from ChapterHalfLineLimitCircle.lean — solution of BookProof.HalfLineLimitCircle.deficiencyVec_ne_zero
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
import Theorems.Thm_BookProof_HalfLineLimitCircle_deficiencyVec_coeFn
import Definitions.Def_ChapterFarisLavine
open BookProof.HalfLineLimitCircle




open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

set_option maxHeartbeats 1000000 in
theorem solution : deficiencyVec ≠ 0 := by

  intro h
  have hae : deficiencyFun =ᵐ[hlMeasure] (fun _ => (0:ℂ)) := by
    have h0 := deficiencyVec_coeFn
    rw [h] at h0
    filter_upwards [h0, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := hlMeasure)] with x h1 h2
    rw [← h1, h2]
    rfl
  have heq : EqOn deficiencyFun (fun _ => (0:ℂ)) (Ioi (0:ℝ)) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioi
      deficiencyFun_contDiff.continuous.continuousOn continuousOn_const
  have := heq (mem_Ioi.mpr one_pos)
  exact Complex.exp_ne_zero _ this
