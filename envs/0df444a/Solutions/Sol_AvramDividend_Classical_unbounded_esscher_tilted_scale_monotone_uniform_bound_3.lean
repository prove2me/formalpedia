-- Prove2me | solution 3 for AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:25:45.193864+00:00
-- url     : https://prove2.me/submissions/3649dc3f-1482-4db9-b9da-9cd4dac8b297

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_first_passage_scale_decay
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_uniform_bound_of_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    MonotoneOn V (Ioi (0 : ℝ)) ∧
      ∃ C : ℝ, ∀ x : ℝ, 0 < x → V x ≤ C := by
  have hscale :=
    unbounded_esscher_root_first_passage_scale_decay
      X q hq W hW hnbv φ hφ hroot
  have hmono : MonotoneOn V (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    change 0 < x at hx
    change 0 < y at hy
    rw [hV x hx, hV y hy]
    have hbound := hscale x y hx hxy
    calc
      Real.exp (-(φ * x)) * W x ≤
          Real.exp (-(φ * x)) *
          (Real.exp (-(φ * (y - x))) * W y) :=
        mul_le_mul_of_nonneg_left hbound (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-(φ * x) + -(φ * (y - x))) * W y := by
        rw [Real.exp_add]
        ring
      _ = Real.exp (-(φ * y)) * W y := by
        congr 1
        ring
  have hub := esscher_tilted_uniform_bound_of_monotone
    X q hq W hW φ hφ hroot V hV hmono
  exact ⟨hmono, ⟨Real.exp 2 * (φ / q), hub⟩⟩
