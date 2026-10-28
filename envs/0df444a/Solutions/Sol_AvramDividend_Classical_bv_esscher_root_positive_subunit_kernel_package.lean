-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_root_positive_subunit_kernel_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:43:49.71099+00:00
-- url     : https://prove2.me/submissions/c6ad450f-8a50-4578-9829-64889001ea20

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_normalised_causal_kernel_shape
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_normalised_kernel_mass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The canonical BV Esscher renewal kernel has strictly positive, subunit mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (κ : ℝ → ℝ) (ρ : ℝ),
      (∀ t : ℝ, κ t =
        if 0 < t then
          ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ := by
  obtain ⟨κ, hκ, hcont, hanti, hzero, hnonneg, hint, hlt⟩ :=
    bv_esscher_root_normalised_causal_kernel_shape X hX hbv q hq φ hφ hroot
  have hmass :
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) =
      (∫ t in Ioi (0 : ℝ),
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) / X.drift := by
    calc
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) =
          ∫ t in Ioi (0 : ℝ),
            ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
              (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
              {z : ℝ≥0 | t < (z : ℝ)}) / X.drift ∂volume :=
        setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
          rw [hκ t, if_pos (Set.mem_Ioi.mp ht)])
      _ = _ := by rw [integral_div]
  have hpositive : 0 < ∫ t in Ioi (0 : ℝ), κ t ∂volume := by
    rw [hmass]
    exact (bv_esscher_root_positive_normalised_kernel_mass
      X hX hbv q hq φ hφ hroot).1
  exact ⟨κ, ∫ t in Ioi (0 : ℝ), κ t ∂volume,
    hκ, hpositive, hlt, hcont, hanti, hzero, hnonneg, hint, rfl⟩