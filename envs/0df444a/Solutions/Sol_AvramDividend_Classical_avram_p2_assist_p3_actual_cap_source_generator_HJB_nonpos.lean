-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_assist_p3_actual_cap_source_generator_HJB_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:00:48.670661+00:00
-- url     : https://prove2.me/submissions/5e07816a-754f-45e0-9e7b-ba0dd0b2ccfa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generator_eq_interior
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Genuine original Lévy generator HJB sign survives cap continuation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (q : ℝ)
    (hw_gen : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      X.generator w z - q * w z ≤ 0) :
    ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      X.generator V z - q * V z ≤ 0 := by
  intro z hz0 hzC
  have hzw := hw_gen z hz0 hzC
  by_cases hC : C = ⊤
  · have hEq : V = w := funext (hVtop hC)
    simpa only [hEq] using hzw
  · have hznonneg : 0 ≤ z := le_of_lt hz0
    have hne : ENNReal.ofReal z ≠ ⊤ := ENNReal.ofReal_ne_top
    have hlt : (ENNReal.ofReal z).toReal < C.toReal :=
      (ENNReal.toReal_lt_toReal hne hC).2 hzC
    rw [ENNReal.toReal_ofReal hznonneg] at hlt
    have hval : V z = w z := by
      rw [hVfinite hC z, if_pos (le_of_lt hlt)]
    have hgen : X.generator V z = X.generator w z := by
      calc
        X.generator V z =
            X.generator (fun y => if y ≤ C.toReal then w y
              else w C.toReal + (y - C.toReal)) z := by
                congr 1
                funext y
                exact hVfinite hC y
        _ = X.generator w z :=
          avram_wave4_04_cap_linear_extension_source_generator_eq_interior
            X w C.toReal z hlt
    rw [hgen, hval]
    exact hzw
