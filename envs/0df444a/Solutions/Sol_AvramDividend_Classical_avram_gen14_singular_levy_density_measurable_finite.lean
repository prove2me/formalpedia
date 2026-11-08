-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen14_singular_levy_density_measurable_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:32:31.382211+00:00
-- url     : https://prove2.me/submissions/8f3751a4-07d1-4a43-8054-1ff5dcbfca82

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- The proposed spectrally negative jump density is Borel and pointwise finite. -/
theorem solution :
    Measurable (fun z : ℝ => if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0) ∧
    (∀ z : ℝ, (if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0) < ⊤) := by
  have hpow : Measurable (fun z : ℝ => |z| ^ (-(3 / 2 : ℝ))) :=
    (measurable_abs).pow_const (-(3 / 2 : ℝ))
  constructor
  · exact Measurable.ite measurableSet_Ioo hpow.ennreal_ofReal measurable_const
  · intro z
    split_ifs <;> simp [ENNReal.ofReal_lt_top]
