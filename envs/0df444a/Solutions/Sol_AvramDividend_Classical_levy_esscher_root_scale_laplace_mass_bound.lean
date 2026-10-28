-- Prove2me | solution 1 for AvramDividend.Classical.levy_esscher_root_scale_laplace_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:20:14.481664+00:00
-- url     : https://prove2.me/submissions/cda4c9ab-acca-4f41-afba-a94dc77a208d

import Mathlib.Algebra.Order.Field.Basic
import Theorems.Thm_AvramDividend_Classical_levy_esscher_root_scale_tilted_laplace
import Theorems.Thm_AvramDividend_Classical_levy_esscher_root_resolvent_ratio_pos_le
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ β : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hβ : 0 < β)
    (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 < β * (∫ y in Ioi (0 : ℝ),
      Real.exp (-(β * y)) * (Real.exp (-(φ * y)) * W y) ∂volume) ∧
    β * (∫ y in Ioi (0 : ℝ),
      Real.exp (-(β * y)) * (Real.exp (-(φ * y)) * W y) ∂volume) ≤
      φ / q := by
  have hscale := (levy_esscher_root_scale_tilted_laplace
    X q φ β hq hφ hβ hroot W hW).2
  have hratio := levy_esscher_root_resolvent_ratio_pos_le
    X q φ β hq hφ hβ hroot
  rw [hscale]
  simpa only [div_eq_mul_inv] using hratio
