-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_bi_new_levy_inverse_esscher_measure_equality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:40:06.473996+00:00
-- url     : https://prove2.me/submissions/b1699d02-8b6a-4fff-a2b3-214563d7cc15

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_inverse_clock_measure_equality

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p : ℝ) (hq : 0 ≤ q)
    (hroot : X.ψ φ = q) (hp : 0 < p) :
    ENNReal.ofReal (p + q) •
      (((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ)))).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (-φ * X.X (Real.toNNReal z.2) z.1)))) =
    ENNReal.ofReal p • (P.prod (expMeasure (p + q))) := by
  have hF : Measurable (fun z : Ω × ℝ => X.X (Real.toNNReal z.2) z.1) :=
    (AvramDividend.Classical.chat04_levy_joint_time_state_measurable X).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have h := AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_measure_equality P p q φ hp hq
    (fun z : Ω × ℝ => X.X (Real.toNNReal z.2) z.1) hF
  rw [hroot]
  exact h
