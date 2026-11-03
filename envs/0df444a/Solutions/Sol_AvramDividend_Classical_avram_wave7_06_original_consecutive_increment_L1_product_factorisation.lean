-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_consecutive_increment_L1_product_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:55:12.904541+00:00
-- url     : https://prove2.me/submissions/e763267d-9be9-4459-9088-e3b24e4bec2f

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_successive_future_increments_indepFun

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Factorisation of the source consecutive-increment cross moment under integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u v : ℝ≥0)
    (hFirst : Integrable
      (fun ω => X.X (s + u) ω - X.X s ω) P)
    (hSecond : Integrable
      (fun ω => X.X (s + u + v) ω - X.X (s + u) ω) P) :
    (∫ ω, (X.X (s + u) ω - X.X s ω) *
      (X.X (s + u + v) ω - X.X (s + u) ω) ∂P) =
      (∫ ω, X.X (s + u) ω - X.X s ω ∂P) *
      (∫ ω, X.X (s + u + v) ω - X.X (s + u) ω ∂P) := by
  have hIndep :
      IndepFun
        (fun ω => X.X (s + u) ω - X.X s ω)
        (fun ω => X.X (s + u + v) ω - X.X (s + u) ω)
        P :=
    avram_wave7_06_original_successive_future_increments_indepFun X s u v
  exact hIndep.integral_mul_eq_mul_integral
    hFirst.aestronglyMeasurable hSecond.aestronglyMeasurable
