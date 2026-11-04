-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_random_measure_monotone_compensator_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:57:36.253709+00:00
-- url     : https://prove2.me/submissions/66293aea-b480-492f-8c4f-cf85b6e0aec3

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_random_measure_double_monotone_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal

/-- An exact countable monotone extension of an independently proved
finite-stage random-measure compensator, requiring real stage data. -/
theorem solution
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (M : Ω → Measure α) (K : Measure α)
    (F : ℕ → Ω → α → ℝ≥0∞)
    (hF : ∀ ω n, Measurable (F n ω))
    (hOuterM : ∀ n,
      Measurable (fun ω => (∫⁻ x, F n ω x ∂M ω)))
    (hOuterK : ∀ n,
      Measurable (fun ω => (∫⁻ x, F n ω x ∂K)))
    (hMono : ∀ ω, Monotone (fun n => F n ω))
    (hEach : ∀ n,
      (∫⁻ ω, (∫⁻ x, F n ω x ∂M ω) ∂P) =
      (∫⁻ ω, (∫⁻ x, F n ω x ∂K) ∂P)) :
    (∫⁻ ω, (∫⁻ x, ⨆ n, F n ω x ∂M ω) ∂P) =
    (∫⁻ ω, (∫⁻ x, ⨆ n, F n ω x ∂K) ∂P) := by
  calc
    (∫⁻ ω, (∫⁻ x, ⨆ n, F n ω x ∂M ω) ∂P) =
        ⨆ n, (∫⁻ ω, (∫⁻ x, F n ω x ∂M ω) ∂P) :=
      avram_p2_f_weighted_random_measure_double_monotone_lintegral
        P M F hF hOuterM hMono
    _ = ⨆ n, (∫⁻ ω, (∫⁻ x, F n ω x ∂K) ∂P) := by
          congr 1
          funext n
          exact hEach n
    _ = (∫⁻ ω, (∫⁻ x, ⨆ n, F n ω x ∂K) ∂P) := by
          symm
          exact avram_p2_f_weighted_random_measure_double_monotone_lintegral
            P (fun _ => K) F hF hOuterK hMono
