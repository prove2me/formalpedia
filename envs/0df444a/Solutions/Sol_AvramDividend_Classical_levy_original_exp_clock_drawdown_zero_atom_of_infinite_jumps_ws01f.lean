-- Prove2me | solution 1 for AvramDividend.Classical.levy_original_exp_clock_drawdown_zero_atom_of_infinite_jumps_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:40:58.911994+00:00
-- url     : https://prove2.me/submissions/327052bd-0e2e-4838-8a56-8b24b1932181

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_tilted_clock_drawdown_zero_atom_of_infinite_jumps_ws01f

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (q φ p lam m : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    (P.prod (expMeasure p))
      {z : Ω × ℝ | runningSup X z.2.toNNReal z.1 -
        X.X z.2.toNNReal z.1 = 0} = 0 := by
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure p)
  let f : Ω × ℝ → ENNReal := fun z =>
    ENNReal.ofReal (Real.exp
      (φ * X.X z.2.toNNReal z.1 - (z.2.toNNReal : ℝ) * X.ψ φ))
  let D : Ω × ℝ → ℝ := fun z =>
    runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1
  have hQzero : (μ.withDensity f) {z | D z = 0} = 0 :=
    levy_tilted_clock_drawdown_zero_atom_of_infinite_jumps_ws01f
      X hjump q φ p lam m hq hφ hroot hp hlam hlamroot hm hmderiv hJoint
  have hQa : ∀ᵐ z ∂(μ.withDensity f), D z ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp hQzero
  have hOrigConditional : ∀ᵐ z ∂μ, f z ≠ 0 → D z ≠ 0 :=
    (ae_withDensity_iff hJoint).mp hQa
  have hfpos (z : Ω × ℝ) : f z ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hOrig : ∀ᵐ z ∂μ, D z ≠ 0 := by
    filter_upwards [hOrigConditional] with z hz
    exact hz (hfpos z)
  exact measure_eq_zero_iff_ae_notMem.mpr hOrig
