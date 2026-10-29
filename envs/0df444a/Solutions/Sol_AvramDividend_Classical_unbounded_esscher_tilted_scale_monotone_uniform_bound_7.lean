-- Prove2me | solution 7 for AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:07:19.554993+00:00
-- url     : https://prove2.me/submissions/faffc7cc-f712-462c-8a86-222f716e075f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_first_passage_scale_decay
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_uniform_bound_of_monotone
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
  -- Tilted monotonicity plus uniform bound from the first-passage decay sketch
  -- (680362b2, SKETCH_ACCEPTED via 14542) through two Proved converters.
  -- Negation-placement discipline (cf. parent 14541 CE): the decay sketch
  -- concludes with `-(φ * (y - x))`; the monotone converter demands
  -- `-φ * (y - x)`; bridge with `← neg_mul`. The monotone conclusion, stated
  -- with `-φ * x`, is transferred to V (stated with `-(φ * x)`) the same way.
  -- Principal lemmas: exit_decay_implies_tilted_monotone,
  -- esscher_tilted_uniform_bound_of_monotone (both Proved).
  -- Exact unresolved identity: first-passage decay 680362b2 (sketch; frontier:
  -- unbounded stopped leaf aed50a34).
  have hdec : ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-(φ * (y - x))) * W y :=
    AvramDividend.Classical.unbounded_esscher_root_first_passage_scale_decay
      X q hq W hW hnbv φ hφ hroot
  have hdecB : ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-φ * (y - x)) * W y := by
    simpa only [← neg_mul] using hdec
  have hmono : MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi (0 : ℝ)) :=
    AvramDividend.Classical.exit_decay_implies_tilted_monotone W φ hdecB
  have hmonoV : MonotoneOn V (Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    have ha0 : (0 : ℝ) < a := ha
    have hb0 : (0 : ℝ) < b := hb
    rw [hV a ha0, hV b hb0]
    -- NOTE (repair of parent 14575, E01+E03): `simpa ... using ...` is a tactic,
    -- not a term — the `exact` prefix made the parser read `simpa` as a command.
    simpa only [neg_mul] using hmono ha hb hab
  have hbound : ∀ x : ℝ, 0 < x → V x ≤ Real.exp 2 * (φ / q) :=
    AvramDividend.Classical.esscher_tilted_uniform_bound_of_monotone
      X q hq W hW φ hφ hroot V hV hmonoV
  exact ⟨hmonoV, _, hbound⟩
