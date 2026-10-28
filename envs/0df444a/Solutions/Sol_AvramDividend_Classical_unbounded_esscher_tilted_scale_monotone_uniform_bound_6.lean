-- Prove2me | solution 6 for AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:38:58.437119+00:00
-- url     : https://prove2.me/submissions/56042cf2-ab7b-4757-8d75-22e680326c56
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_first_passage_scale_decay
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_uniform_bound_of_monotone
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Esscher decay gives a monotone tilt and its global bound. -/
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
  have hdecay :=
    unbounded_esscher_root_first_passage_scale_decay
      X q hq W hW hnbv φ hφ hroot
  have hmonoFn : MonotoneOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) :=
    exit_decay_implies_tilted_monotone W φ
      (by simpa only [neg_mul] using hdecay)
  have hmonoV : MonotoneOn V (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    rw [hV x hx, hV y hy]
    simpa only [neg_mul] using hmonoFn hx hy hxy
  refine ⟨hmonoV, ⟨Real.exp 2 * (φ / q), ?_⟩⟩
  exact esscher_tilted_uniform_bound_of_monotone
    X q hq W hW φ hφ hroot V hV hmonoV
