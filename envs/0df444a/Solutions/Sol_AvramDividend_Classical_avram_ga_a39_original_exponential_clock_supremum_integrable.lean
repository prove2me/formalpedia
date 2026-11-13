-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a39_original_exponential_clock_supremum_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:47:15.646918+00:00
-- url     : https://prove2.me/submissions/bbd3288e-87eb-444a-8ffb-a67199ceab22

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_supremum_lintegral_rate_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p lam β : ℝ) (hp : 0 < p) (hlam : 0 < lam)
    (hroot : X.ψ lam = p) (hβ : β < lam) :
    (∫⁻ z : Ω×ℝ,
      ENNReal.ofReal (Real.exp
        (β * runningSup X (Real.toNNReal z.2) z.1))
        ∂ (P.prod (expMeasure p))) < ⊤ := by
  have hEq :=
    avram_ws01e_bt_new_original_clock_supremum_lintegral_rate_gap
      X p hp lam hlam hroot β hβ
  have hCoeff : ENNReal.ofReal (lam - β) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hβ))
  by_contra hNot
  have hInf : (∫⁻ z : Ω×ℝ,
      ENNReal.ofReal (Real.exp
        (β * runningSup X (Real.toNNReal z.2) z.1))
        ∂ (P.prod (expMeasure p))) = ⊤ :=
    top_unique (le_of_not_gt hNot)
  rw [hInf] at hEq
  simp [ENNReal.mul_top, hCoeff] at hEq
