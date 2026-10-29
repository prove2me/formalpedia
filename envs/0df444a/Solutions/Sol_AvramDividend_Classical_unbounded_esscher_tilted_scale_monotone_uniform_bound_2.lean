-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T06:41:38.881703+00:00
-- url     : https://prove2.me/submissions/22e8d61e-f8c5-40f8-a2bb-3392f2a2651d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_exit_decay
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
  have hratio : ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-φ * (y - x)) * W y :=
    unbounded_esscher_root_exit_decay X q hq W hW hnbv φ hφ hroot
  have hmonotilt : MonotoneOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi (0 : ℝ)) :=
    exit_decay_implies_tilted_monotone W φ hratio
  have hmono : MonotoneOn V (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    rw [hV x (Set.mem_Ioi.mp hx), hV y (Set.mem_Ioi.mp hy)]
    simpa only [neg_mul] using hmonotilt hx hy hxy
  refine ⟨hmono, ?_⟩
  refine ⟨Real.exp 2 * (φ / q), ?_⟩
  exact esscher_tilted_uniform_bound_of_monotone
    X q hq W hW φ hφ hroot V hV hmono
