-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_before_first_negative_jump_source_increments_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:31:15.205206+00:00
-- url     : https://prove2.me/submissions/74195332-98b2-47f7-bce6-2427464c4bd8

import Mathlib
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All source jumps strictly before the first actual negative mark are zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hBefore : (t : WithTop ℝ≥0) <
      (⨅ u : ℝ≥0,
        if 0 < u ∧
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
        then (u : WithTop ℝ≥0) else ⊤)) :
    X.X t ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t = 0 := by
  classical
  have hNonPos :
      X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≤ 0 :=
    avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω t ht
  by_contra hNe
  have hNeg :
      X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t < 0 :=
    lt_of_le_of_ne hNonPos hNe
  have hLe : (⨅ u : ℝ≥0,
      if 0 < u ∧
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
      then (u : WithTop ℝ≥0) else ⊤) ≤
      (t : WithTop ℝ≥0) := by
    calc
      (⨅ u : ℝ≥0,
        if 0 < u ∧
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
        then (u : WithTop ℝ≥0) else ⊤) ≤
        (if 0 < t ∧
            X.X t ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) t < 0
         then (t : WithTop ℝ≥0) else ⊤) := iInf_le _ t
      _ = (t : WithTop ℝ≥0) := if_pos ⟨ht, hNeg⟩
  exact (not_lt_of_ge hLe) hBefore
