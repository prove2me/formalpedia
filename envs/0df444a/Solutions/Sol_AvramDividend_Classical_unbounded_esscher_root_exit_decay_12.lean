-- Prove2me | solution 12 for AvramDividend.Classical.unbounded_esscher_root_exit_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T21:58:18.301973+00:00
-- url     : https://prove2.me/submissions/ea1e8ab6-38ba-4449-a4a5-4da124f180f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-φ * (y - x)) * W y := by
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact AvramDividend.Classical.unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  have hBase := AvramDividend.Classical.unbounded_fixedroot_decay_of_corrected_exit_identity
    X q hq W hW hnbv φ hφ hroot hExit
  intro x y hx hxy
  have h := hBase x y hx hxy
  have hArg : -φ * (y - x) = -(φ * (y - x)) := by ring
  rw [hArg]
  exact h
