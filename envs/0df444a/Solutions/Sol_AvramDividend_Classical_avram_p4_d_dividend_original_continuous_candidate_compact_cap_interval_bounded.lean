-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_continuous_candidate_compact_cap_interval_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:32:01.686568+00:00
-- url     : https://prove2.me/submissions/e9e529fc-1eef-4a3b-92ab-11d8f138cd50

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original candidate's one-sided continuity bounds its entire finite
dividend cap interval, including the cap and lower boundary contact. -/
theorem solution
    (C : ℝ≥0∞)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ))) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ Icc (0 : ℝ) C.toReal, ‖w z‖ ≤ M := by
  have hcap : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hnonempty : (Icc (0 : ℝ) C.toReal).Nonempty := by
    exact ⟨0, ⟨le_refl _, hcap⟩⟩
  have hwIcc : ContinuousOn w (Icc (0 : ℝ) C.toReal) :=
    hw_cont.mono (by intro z hz; exact hz.1)
  have hnorm : ContinuousOn (fun z : ℝ => ‖w z‖)
      (Icc (0 : ℝ) C.toReal) :=
    continuous_norm.comp_continuousOn hwIcc
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) C.toReal)).exists_isMaxOn
      hnonempty hnorm
  refine ⟨‖w z‖, norm_nonneg _, ?_⟩
  intro y hy
  exact hmax hy
