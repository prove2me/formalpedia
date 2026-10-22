-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scale_weighted_deriv_adjacent_unit_intervals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:44:08.363426+00:00
-- url     : https://prove2.me/submissions/1a5a7202-ef74-41a2-a7ef-4f423b029a77

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_interval_mass_bound
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_value_interval_lower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! A unit interval of weighted scale derivative is controlled by the
scale Laplace mass on the subsequent unit interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ a : ℝ) (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hWa : 0 ≤ W a) :
    (∫ x in a..(a + 1), Real.exp (-(θ * x)) * deriv W x) ≤
      Real.exp (2 * θ) *
        (∫ x in (a + 1)..(a + 2), Real.exp (-(θ * x)) * W x) := by
  have hmono := scaleFunction_monotone X q W hW
  have ha1 : 0 ≤ a + 1 := by linarith
  have hab1 : a ≤ a + 1 := by linarith
  have hab2 : a + 1 ≤ a + 2 := by linarith
  have hWa1 : 0 ≤ W (a + 1) := le_trans hWa (hmono hab1)
  have hleft :=
    (chat07_scale_weighted_deriv_interval_mass_bound
      X q W hW θ a (a + 1) hθ ha hab1).2
  have hright :=
    (chat07_scale_weighted_value_interval_lower
      X q W hW θ (a + 1) (a + 2) hθ hab2 hWa1).2
  have hright' :
      Real.exp (-(θ * (a + 2))) * W (a + 1) ≤
        (∫ x in (a + 1)..(a + 2), Real.exp (-(θ * x)) * W x) := by
    simpa [show (a + 2) - (a + 1) = (1 : ℝ) by ring] using hright
  have hdelta : W (a + 1) - W a ≤ W (a + 1) := by linarith
  have hexp : Real.exp (-(θ * a)) =
      Real.exp (2 * θ) * Real.exp (-(θ * (a + 2))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (∫ x in a..(a + 1), Real.exp (-(θ * x)) * deriv W x)
        ≤ Real.exp (-(θ * a)) * (W (a + 1) - W a) := hleft
    _ ≤ Real.exp (-(θ * a)) * W (a + 1) :=
      mul_le_mul_of_nonneg_left hdelta (Real.exp_pos _).le
    _ = Real.exp (2 * θ) *
        (Real.exp (-(θ * (a + 2))) * W (a + 1)) := by
      rw [hexp]
      ring
    _ ≤ Real.exp (2 * θ) *
        (∫ x in (a + 1)..(a + 2), Real.exp (-(θ * x)) * W x) :=
      mul_le_mul_of_nonneg_left hright' (Real.exp_pos _).le
