-- Prove2me | solution 3 for AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T17:53:15.585914+00:00
-- url     : https://prove2.me/submissions/b19d36c9-5a4b-4c0d-9283-b7afb248561b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_uniform_bound_of_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_positive_monotoneOn_bounded_tendsto_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-! Corrected exit implies a positive finite limit for the Esscher tilt. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (nhds L) := by
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  have hdecay :=
    unbounded_fixedroot_decay_of_corrected_exit_identity
      X q hq W hW hnbv φ hφ hroot hExit
  have hmonoFn : MonotoneOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) :=
    exit_decay_implies_tilted_monotone W φ
      (by simpa only [neg_mul] using hdecay)
  have hmonoV : MonotoneOn V (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    rw [hV x hx, hV y hy]
    simpa only [neg_mul] using hmonoFn hx hy hxy
  have hupper : ∃ C : ℝ, ∀ x : ℝ, 0 < x → V x ≤ C :=
    ⟨Real.exp 2 * (φ / q),
      esscher_tilted_uniform_bound_of_monotone
        X q hq W hW φ hφ hroot V hV hmonoV⟩
  have hposV : ∀ x : ℝ, 0 < x → 0 < V x := by
    intro x hx
    rw [hV x hx]
    exact mul_pos (Real.exp_pos _) 
      (scaleFunction_strict_pos_of_unbounded_variation
        X q W hW hnbv x hx)
  exact positive_monotoneOn_bounded_tendsto_positive V hposV hmonoV hupper
