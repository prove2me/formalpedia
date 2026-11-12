-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:02:37.42933+00:00
-- url     : https://prove2.me/submissions/35e90491-73cd-4287-9648-ecb02998e696

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys130_compact_reserve_negative_mark_value_increment_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
noncomputable section

/-- Compact payoff domination converted to the original finite
extended-nonnegative-real closed dividend cap. -/
theorem solution
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ b z : ℝ, 0 ≤ b → ENNReal.ofReal b ≤ C → z < 0 →
        |w (b + z) - w b| ≤ 2 * M := by
  have hcompact : ContinuousOn w (Icc (0 : ℝ) C.toReal) :=
    hw_cont.mono (by intro b hb; exact hb.1)
  obtain ⟨M, hM, hbound⟩ :=
    AvramDividend.Classical.avram_bvb_phys130_compact_reserve_negative_mark_value_increment_uniform_bound
      C.toReal w hcompact hw_neg
  refine ⟨M, hM, ?_⟩
  intro b z hb hbC hz
  have hbreal : b ≤ C.toReal := by
    have h := ENNReal.toReal_mono hFinite hbC
    simpa only [ENNReal.toReal_ofReal hb] using h
  exact hbound b z hb hbreal hz
