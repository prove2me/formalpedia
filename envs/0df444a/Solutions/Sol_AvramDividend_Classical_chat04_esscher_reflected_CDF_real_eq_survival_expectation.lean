-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_reflected_CDF_real_eq_survival_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:50:17.789895+00:00
-- url     : https://prove2.me/submissions/d22298fc-35e8-4602-9f90-97f0df2a176a

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_reflected_law_Iic_eq_killed_lintegral
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_real_to_lintegral
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ x : ℝ) (hθ : 0 ≤ θ) :
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))).map (fun ω : Ω => -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})).real (Iic x) =
    (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) := by
  have hpush :=
    chat04_esscher_reflected_law_Iic_eq_killed_lintegral X t θ x
  have hbridge :=
    chat04_esscher_killed_survival_real_to_lintegral X x t θ hθ
  have hn := (esscher_weighted_lower_survival_mass_unit_interval
    X θ hθ x t).1
  rw [Measure.real_def, hpush, hbridge, ENNReal.toReal_ofReal hn]
