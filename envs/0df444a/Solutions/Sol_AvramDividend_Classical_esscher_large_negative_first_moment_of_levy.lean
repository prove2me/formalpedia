-- Prove2me | solution 1 for AvramDividend.Classical.esscher_large_negative_first_moment_of_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T05:31:02.937892+00:00
-- url     : https://prove2.me/submissions/eb927085-284c-4606-a9a5-9830c938b778

import Mathlib.Order.BoundedOrder.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_large_negative_jump_mass
import Theorems.Thm_AvramDividend_Classical_esscher_large_negative_first_moment_integrable
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
    (φ : ℝ) (hφ : 0 < φ) :
    IntegrableOn (fun y : ℝ => (-y) * Real.exp (φ * y))
      (Iic (-1 : ℝ)) X.ν := by
  have hfinite : X.ν (Iic (-1 : ℝ)) < ⊤ :=
    lt_top_iff_ne_top.mpr
      (finite_large_negative_jump_mass X.ν X.ν_integrable)
  exact esscher_large_negative_first_moment_integrable X.ν φ hφ hfinite
