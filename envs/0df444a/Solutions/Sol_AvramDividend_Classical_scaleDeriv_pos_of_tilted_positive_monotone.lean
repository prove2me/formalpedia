-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_pos_of_tilted_positive_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T13:12:49.9989+00:00
-- url     : https://prove2.me/submissions/a4c2a006-d0f2-45d9-85c4-f7c7598adf9e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  intro x hx
  obtain ⟨φ, hφ, hmono⟩ := htilt
  have hbound : φ * W x ≤ deriv W x :=
    normalized_derivative_lower_bound φ x hmono hx (hdiff x hx)
  exact lt_of_lt_of_le (mul_pos hφ (hpos x hx)) hbound
