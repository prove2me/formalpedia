-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_disjoint_negative_void_intervals_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:26:06.701689+00:00
-- url     : https://prove2.me/submissions/a153bb04-75bf-4ded-8842-c301a7855cc8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_disjoint_nojump_intervals_independent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Literal original-X marked jump-count voids in disjoint intervals are independent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    P ({ω : Ω |
      ((Measure.count.restrict {r : ℝ≥0 |
        0 < r ∧ X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ≠ 0}).map
        (fun r : ℝ≥0 => (r,
          X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) = 0} ∩
       {ω : Ω |
        ((Measure.count.restrict {r : ℝ≥0 |
          0 < r ∧ X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ≠ 0}).map
          (fun r : ℝ≥0 => (r,
            X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r)))
          (Ioc u v ×ˢ Iio (0 : ℝ)) = 0}) =
      P {ω : Ω |
        ((Measure.count.restrict {r : ℝ≥0 |
          0 < r ∧ X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ≠ 0}).map
          (fun r : ℝ≥0 => (r,
            X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r)))
          (Ioc s t ×ˢ Iio (0 : ℝ)) = 0} *
      P {ω : Ω |
        ((Measure.count.restrict {r : ℝ≥0 |
          0 < r ∧ X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ≠ 0}).map
          (fun r : ℝ≥0 => (r,
            X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r)))
          (Ioc u v ×ˢ Iio (0 : ℝ)) = 0} := by
  let N₁ : Set Ω := {ω : Ω |
    ((Measure.count.restrict {r : ℝ≥0 |
      0 < r ∧ X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ≠ 0}).map
      (fun r : ℝ≥0 => (r,
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) = 0}
  let N₂ : Set Ω := {ω : Ω |
    ((Measure.count.restrict {r : ℝ≥0 |
      0 < r ∧ X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ≠ 0}).map
      (fun r : ℝ≥0 => (r,
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r)))
      (Ioc u v ×ˢ Iio (0 : ℝ)) = 0}
  let J₁ : Set Ω := {ω : Ω | ∀ r : ℝ≥0, r ∈ Ioc s t →
    X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r = 0}
  let J₂ : Set Ω := {ω : Ω | ∀ r : ℝ≥0, r ∈ Ioc u v →
    X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r = 0}
  have hE₁ : N₁ = J₁ := by
    ext ω
    exact avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
      X ω s t
  have hE₂ : N₂ = J₂ := by
    ext ω
    exact avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
      X ω u v
  change P (N₁ ∩ N₂) = P N₁ * P N₂
  rw [hE₁, hE₂]
  exact avram_wave4_04a_bv_actual_disjoint_nojump_intervals_independent
    X hBV hFinite s t u v hst htu huv
