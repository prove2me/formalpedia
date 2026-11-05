-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_assist_p3_actual_cap_source_generatorIntegrable_HJB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:01:21.426064+00:00
-- url     : https://prove2.me/submissions/8fbdcd7d-dba0-4296-98bb-c841f99d5e57

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_interior_cap_generator_hjb
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original source cap continuation retains generator integrability and its HJB sign. -/
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
      X.GeneratorIntegrable w z ∧
      X.generator w z - q * w z ≤ 0) :
    ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      X.GeneratorIntegrable V z ∧
      X.generator V z - q * V z ≤ 0 := by
  intro z hz0 hzC
  have hsource := hw_gen z hz0 hzC
  by_cases hC : C = ⊤
  · have hEq : V = w := funext (hVtop hC)
    simpa only [hEq] using hsource
  · have hznonneg : 0 ≤ z := le_of_lt hz0
    have hne : ENNReal.ofReal z ≠ ⊤ := ENNReal.ofReal_ne_top
    have hlt : (ENNReal.ofReal z).toReal < C.toReal :=
      (ENNReal.toReal_lt_toReal hne hC).2 hzC
    rw [ENNReal.toReal_ofReal hznonneg] at hlt
    have hEq : V = (fun y : ℝ => if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal)) := funext (hVfinite hC)
    rw [hEq]
    exact avram_p3_bv_original_interior_cap_generator_hjb
      X w C.toReal z q hlt hsource
