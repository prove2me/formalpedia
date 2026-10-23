-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_esscher_ratio_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:37:56.903643+00:00
-- url     : https://prove2.me/submissions/f7bd3e90-e8f5-42e6-a3a4-85700a9fcaaa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound

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
    (hnbv : ¬ X.BoundedVariation) :
    ∃ (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q),
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x / W y ≤ Real.exp (-(φ * (y - x))) := by
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hnbv q hq
  have hmono : MonotoneOn
      (fun t : ℝ => Real.exp (-(φ * t)) * W t) (Ioi (0 : ℝ)) := by
    exact (unbounded_esscher_tilted_scale_monotone_uniform_bound
      X q hq W hW hnbv φ hφ hroot
      (fun t : ℝ => Real.exp (-(φ * t)) * W t)
      (by intro t ht; rfl)).1
  refine ⟨φ, hφ, hroot, ?_⟩
  intro x y hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hWy : 0 < W y :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv y hy
  have htilt : Real.exp (-(φ * x)) * W x ≤
      Real.exp (-(φ * y)) * W y :=
    hmono hx hy hxy
  have hex : Real.exp (φ * x) * Real.exp (-(φ * x)) = 1 := by
    rw [← Real.exp_add]
    have : φ * x + -(φ * x) = 0 := by ring
    rw [this, Real.exp_zero]
  have hey : Real.exp (φ * x) * Real.exp (-(φ * y)) =
      Real.exp (-(φ * (y - x))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (div_le_iff₀ hWy).2
  calc
    W x = Real.exp (φ * x) * (Real.exp (-(φ * x)) * W x) := by
      rw [← mul_assoc, hex, one_mul]
    _ ≤ Real.exp (φ * x) * (Real.exp (-(φ * y)) * W y) :=
      mul_le_mul_of_nonneg_left htilt (Real.exp_nonneg _)
    _ = Real.exp (-(φ * (y - x))) * W y := by
      rw [← mul_assoc, hey]
