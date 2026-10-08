-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_unbounded
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:10:34.306767+00:00
-- url     : https://prove2.me/submissions/209db332-2835-4755-b0c5-1b02009c6b0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_cumulative_laplace_representation
import Theorems.Thm_AvramDividend_Classical_positive_tilted_of_laplace_cumulative_identification_full_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : ¬ X.BoundedVariation) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  obtain ⟨β, φ, b, hφ, hfin, hmass, hlap⟩ :=
    unbounded_tilted_cumulative_laplace_representation
      X hX q hq W hW hbv
  have hcontW : ContinuousOn W (Ioi 0) :=
    hW.2.2.1.mono Set.Ioi_subset_Ici_self
  have hcontExp :
      ContinuousOn (fun x : ℝ => Real.exp (-φ * x)) (Ioi 0) := by
    fun_prop
  have hcont :
      ContinuousOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) :=
    hcontExp.mul hcontW
  have hnonneg :
      ∀ x : ℝ, 0 < x → 0 ≤ Real.exp (-φ * x) * W x := by
    intro x hx
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (hW.2.1 x (le_of_lt hx))
  obtain ⟨hpositive, hmonotone⟩ :=
    positive_tilted_of_laplace_cumulative_identification_full_support
      β φ b hφ hfin hmass W hcont hnonneg hlap
  exact ⟨hpositive, φ, hφ, hmonotone⟩
