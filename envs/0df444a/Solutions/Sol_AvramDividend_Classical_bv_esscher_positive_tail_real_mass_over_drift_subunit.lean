-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_positive_tail_real_mass_over_drift_subunit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:14:37.048741+00:00
-- url     : https://prove2.me/submissions/031e71a6-afe7-4c1b-b7ca-3ffefb986436

import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_total_mass_of_root
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Field.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The real Esscher positive-tail mass divided by BV drift is subunit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    0 ≤
      (∫ t in Ioi (0 : ℝ),
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) / X.drift ∧
      (∫ t in Ioi (0 : ℝ),
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) / X.drift < 1 := by
  let μ : Measure ℝ≥0 := X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  have hpos : 0 ≤
      ∫ z : ℝ≥0, (z : ℝ) * Real.exp (-(φ * (z : ℝ))) ∂μ := by
    apply integral_nonneg
    intro z
    exact mul_nonneg (NNReal.coe_nonneg z) (Real.exp_pos _).le
  have hsub :
      (∫ z : ℝ≥0, (z : ℝ) * Real.exp (-(φ * (z : ℝ))) ∂μ) <
        X.drift :=
    (bv_esscher_root_subcritical_kernel_mass X hbv q hq φ hφ hroot).2
  have hdrift : 0 < X.drift := lt_of_le_of_lt hpos hsub
  rw [bv_esscher_positive_tail_real_total_mass_of_root
    X hbv q hq φ hφ hroot]
  exact ⟨div_nonneg hpos hdrift.le, (div_lt_one hdrift).mpr hsub⟩
