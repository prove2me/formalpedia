-- Prove2me | solution 8 for AvramDividend.Classical.unbounded_esscher_root_first_passage_scale_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:57:02.092693+00:00
-- url     : https://prove2.me/submissions/5b93115d-3559-4c31-b5d1-8d5f426ddd43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_scale_decay_of_corrected_exit_estimates

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
      W x ≤ Real.exp (-(φ * (y - x))) * W y := by
  -- Positivity (Proved e50526dc, needs only hW + hnbv, both available).
  have hpos : ∀ y : ℝ, 0 < y → 0 < W y :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded_variation
      X q W hW hnbv
  -- Corrected exit identity (Open 6d3911f8, hnbv-native, no Standing needed).
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := fun a x ha hx hxa =>
    AvramDividend.Classical.unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  -- Corrected exit discount bound at the positive Esscher root
  -- (Proved a6c37169, needs hq hφ hroot).
  have hBound : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x ≤
        ENNReal.ofReal (Real.exp (-(φ * (a - x)))) := fun a x ha hx hxa =>
    AvramDividend.Classical.corrected_exit_exp_bound_at_positive_root
      X q hq φ hφ hroot a x ha hx hxa
  -- Fixed-root decay composition (Proved 6c3feafc): exit identity + bound
  -- give the tilted-scale monotonicity, i.e. exactly the goal.
  exact AvramDividend.Classical.unbounded_fixedroot_scale_decay_of_corrected_exit_estimates
    X q W hpos φ hExit hBound
