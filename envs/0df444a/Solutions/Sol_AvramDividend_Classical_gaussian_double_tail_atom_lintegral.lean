-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_atom_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:51:43.818877+00:00
-- url     : https://prove2.me/submissions/a9c58e19-5cb6-43c0-a5a8-bdd5b3f8b0cc

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Convert the positive single-jump Volterra atom integral to an ENNReal integral. -/
theorem solution
    (θ z : ℝ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    (∫⁻ t in Ioc (0 : ℝ) z,
      ENNReal.ofReal (θ ^ 2 * ((z - t) * Real.exp (-θ * t))) ∂volume) =
      ENNReal.ofReal (Real.exp (-θ * z) - 1 + θ * z) := by
  let f : ℝ → ℝ := fun t => θ ^ 2 * ((z - t) * Real.exp (-θ * t))
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hint : IntegrableOn f (Ioc (0 : ℝ) z) volume :=
    hcont.integrableOn_Ioc
  have hmem : ∀ᵐ t : ℝ ∂volume.restrict (Ioc (0 : ℝ) z),
      t ∈ Ioc (0 : ℝ) z :=
    ae_restrict_mem (μ := volume) measurableSet_Ioc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) z)] f := by
    filter_upwards [hmem] with t ht
    dsimp [f]
    exact mul_nonneg (sq_nonneg θ)
      (mul_nonneg (sub_nonneg.mpr ht.2) (le_of_lt (Real.exp_pos _)))
  have hbridge :
      ENNReal.ofReal (∫ t in Ioc (0 : ℝ) z, f t ∂volume) =
        (∫⁻ t in Ioc (0 : ℝ) z, ENNReal.ofReal (f t) ∂volume) :=
    ofReal_integral_eq_lintegral_ofReal hint hnonneg
  have hatom :
      (∫ t in (0 : ℝ)..z, f t) =
        Real.exp (-θ * z) - 1 + θ * z := by
    simpa only [f] using
      AvramDividend.Classical.gaussian_double_tail_atom_integral θ z
  calc
    (∫⁻ t in Ioc (0 : ℝ) z, ENNReal.ofReal (f t) ∂volume) =
        ENNReal.ofReal (∫ t in Ioc (0 : ℝ) z, f t ∂volume) := hbridge.symm
    _ = ENNReal.ofReal (∫ t in (0 : ℝ)..z, f t) := by
      rw [intervalIntegral.integral_of_le hz]
    _ = ENNReal.ofReal (Real.exp (-θ * z) - 1 + θ * z) :=
      congrArg ENNReal.ofReal hatom
