-- Prove2me | solution 5 for AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:49:54.221267+00:00
-- url     : https://prove2.me/submissions/859c9d11-a403-4820-8eec-0829d97c34a8

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_esscher_decay_of_stopped_scale_balance
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
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
  have hbalance : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by
    intro a x ha hx hxa
    exact chat04_unbounded_two_sided_exit_stopped_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  have hdecay := chat01_unbounded_esscher_decay_of_stopped_scale_balance
    X q hq W hW hnbv φ hφ hroot hbalance
  have hmonoFn : MonotoneOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) :=
    exit_decay_implies_tilted_monotone W φ (by simpa only [neg_mul] using hdecay)
  have hmonoV : MonotoneOn V (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    rw [hV x hx, hV y hy]
    simpa only [neg_mul] using hmonoFn hx hy hxy
  refine ⟨hmonoV, ⟨Real.exp 2 * (φ / q), ?_⟩⟩
  exact esscher_tilted_uniform_bound_of_monotone
    X q hq W hW φ hφ hroot V hV hmonoV
