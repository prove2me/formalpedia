-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_leftjump_cap_splice_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:57:09.87218+00:00
-- url     : https://prove2.me/submissions/449075f6-a60e-4e16-b6ca-68fded31c61c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_frozen_source_cap_splice_step

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- On an actual positive-time negative Lévy source jump, the cap-spliced
and original C1 candidates have the same source-jump increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ v : ℝ, V v = w v)
    (hVfinite : C ≠ ⊤ → ∀ v : ℝ,
      V v = if v ≤ C.toReal then w v
        else w C.toReal + (v - C.toReal))
    (z : ℝ) (hz : C = ⊤ ∨ z ≤ C.toReal) :
    V (z + (X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)) - V z =
      w (z + (X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)) - w z := by
  have hJump :
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≤ 0 := by
    have h :=
      (avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
        X ω t ht).1
    linarith only [h]
  have hzd :
      C = ⊤ ∨
        z + (X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) ≤
          C.toReal := by
    rcases hz with htop | hfin
    · exact Or.inl htop
    · exact Or.inr (by linarith only [hfin, hJump])
  exact avram_p3_bv_frozen_source_cap_splice_step
    C w V hVtop hVfinite z
      (X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)
      hz hzd
