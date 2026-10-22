-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_atom_esscher_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:58:29.363233+00:00
-- url     : https://prove2.me/submissions/012ae8eb-b5ea-444c-bac4-e848f32e7026

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Insert the Esscher jump weight into the ENNReal double-tail atom integral. -/
theorem solution
    (φ θ z : ℝ) (hφ : 0 < φ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    (∫⁻ t in Ioo (0 : ℝ) z,
      ENNReal.ofReal (θ ^ 2) *
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
        ENNReal.ofReal (Real.exp (-φ * z)) ∂volume) =
      ENNReal.ofReal
        (Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) := by
  let G : ℝ → ENNReal := fun t =>
    ENNReal.ofReal (θ ^ 2 * ((z - t) * Real.exp (-θ * t)))
  have hmeas : Measurable G := by
    dsimp [G]
    fun_prop
  have hpoint : ∀ t : ℝ,
      ENNReal.ofReal (θ ^ 2) *
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
        ENNReal.ofReal (Real.exp (-φ * z)) =
      ENNReal.ofReal (Real.exp (-φ * z)) * G t := by
    intro t
    dsimp [G]
    rw [← ENNReal.ofReal_mul (sq_nonneg θ)]
    ac_rfl
  simp_rw [hpoint]
  rw [lintegral_const_mul (ENNReal.ofReal (Real.exp (-φ * z))) hmeas]
  have hatom :
      (∫⁻ t in Ioo (0 : ℝ) z, G t ∂volume) =
      ENNReal.ofReal (Real.exp (-θ * z) - 1 + θ * z) := by
    simpa only [G, restrict_Ioo_eq_restrict_Ioc] using
      AvramDividend.Classical.gaussian_double_tail_atom_lintegral θ z hθ hz
  rw [hatom]
  rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
