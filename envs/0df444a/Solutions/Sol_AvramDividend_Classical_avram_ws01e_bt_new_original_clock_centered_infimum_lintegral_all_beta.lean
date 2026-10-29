-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_clock_centered_infimum_lintegral_all_beta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:35:28.029338+00:00
-- url     : https://prove2.me/submissions/b67c3e16-3538-4c8b-9174-a9f765869f6b

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_lintegral_all_beta
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_drawdown_infimum_all_borel_reward

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The genuine original-clock centred running infimum has the
complete descending transform, including the removable root. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p) :
    ∃ m : ℝ, 0 < m ∧ HasDerivAt X.ψ m lam ∧
      ∀ β : ℝ, 0 < β →
        (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp
          (-β * (X.X 0 z.1 +
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ z.2.toNNReal ∧ y = X.X s z.1})))
          ∂(P.prod (expMeasure p))) =
        ENNReal.ofReal
          (if β = lam then p / (lam * m)
          else (p / lam) * ((lam - β) / (p - X.ψ β))) := by
  rcases avram_ws01e_bt_new_original_clock_descending_lintegral_all_beta
    X p hp lam hlam hroot with ⟨m, hm, hmDeriv, hAll⟩
  refine ⟨m, hm, hmDeriv, ?_⟩
  intro β hβ
  have hf : Measurable (fun y : ℝ =>
      ENNReal.ofReal (Real.exp (-β * y))) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_const.mul measurable_id).exp)
  have hReward :=
    avram_ws01e_bt_new_original_clock_drawdown_infimum_all_borel_reward
      X p hp (fun y : ℝ => ENNReal.ofReal (Real.exp (-β * y))) hf
  calc
    (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp
        (-β * (X.X 0 z.1 +
          -sInf {y : ℝ | ∃ s : ℝ≥0,
            s ≤ z.2.toNNReal ∧ y = X.X s z.1})))
        ∂(P.prod (expMeasure p))) =
      (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp
        (-β * (runningSup X z.2.toNNReal z.1 -
          X.X z.2.toNNReal z.1)))
        ∂(P.prod (expMeasure p))) := hReward.symm
    _ = _ := hAll β hβ
