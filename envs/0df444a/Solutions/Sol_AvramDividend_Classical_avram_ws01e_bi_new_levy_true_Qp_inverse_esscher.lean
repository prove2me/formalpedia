-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_levy_true_Qp_inverse_esscher
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:30:39.697188+00:00
-- url     : https://prove2.me/submissions/701f39ae-a2b3-43b6-9c3e-1315d93091bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_inverse_clock_cast_corrected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The genuine random-terminal Esscher law converts to the original larger-rate clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p : ℝ) (hq : 0 ≤ q)
    (hroot : X.ψ φ = q) (hp : 0 < p)
    (W : Ω × ℝ → ℝ≥0∞) (hW : Measurable W) :
    ENNReal.ofReal (p + q) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp (-φ * X.X (Real.toNNReal z.2) z.1)) * W z
        ∂((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) =
    ENNReal.ofReal p *
      (∫⁻ z : Ω × ℝ, W z ∂(P.prod (expMeasure (p + q)))) := by
  have hTime : Measurable (fun z : Ω × ℝ =>
      (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hF : Measurable (fun z : Ω × ℝ =>
      X.X (Real.toNNReal z.2) z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp hTime
  simpa only [hroot] using
    (avram_ws01e_bi_new_inverse_clock_cast_corrected
      P p q φ hp hq
      (fun z : Ω × ℝ => X.X (Real.toNNReal z.2) z.1)
      hF W hW)
