-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scale_deriv_interval_integrable_and_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:13:06.816206+00:00
-- url     : https://prove2.me/submissions/3acb29c2-3773-49ee-9707-1523c7fd36ca

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Monotonicity controls the integral mass of the scale derivative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a b : ℝ) :
    IntervalIntegrable (deriv W) volume a b ∧
      (∫ x in a..b, deriv W x) ∈ uIcc 0 (W b - W a) := by
  have hmono : MonotoneOn W (uIcc a b) :=
    (scaleFunction_monotone X q W hW).monotoneOn _
  exact ⟨hmono.intervalIntegrable_deriv,
    hmono.intervalIntegral_deriv_mem_uIcc⟩
