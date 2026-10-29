-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:27:18.787013+00:00
-- url     : https://prove2.me/submissions/2972ae8c-7f0d-4484-aa08-73baceb9bb37

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_first_passage_scale_decay
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_uniform_bound_of_monotone
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

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
  have hexit :
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x ≤ Real.exp (-(φ * (y - x))) * W y :=
    unbounded_esscher_root_first_passage_scale_decay
      X q hq W hW hnbv φ hφ hroot
  have hmonoTilt :
      MonotoneOn
        (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi (0 : ℝ)) := by
    apply exit_decay_implies_tilted_monotone W φ
    intro x y hx hxy
    simpa only [neg_mul] using hexit x y hx hxy
  have hmono : MonotoneOn V (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    rw [hV x hx, hV y hy]
    simpa only [neg_mul] using hmonoTilt hx hy hxy
  refine ⟨hmono, ⟨Real.exp 2 * (φ / q), ?_⟩⟩
  intro x hx
  exact esscher_tilted_uniform_bound_of_monotone
    X q hq W hW φ hφ hroot V hV hmono x hx
