-- Prove2me | solution 5 for AvramDividend.Classical.unbounded_tilted_scale_log_concavity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:04:40.185349+00:00
-- url     : https://prove2.me/submissions/08eb51b6-a724-4f41-a7dd-99454d545109
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_log_concavity_core
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_log_concave_of_scale_log_concave
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
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (hVdiff : ∀ x : ℝ, 0 < x → HasDerivAt V (deriv V x) x) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) := by
  have hWpos : ∀ x : ℝ, 0 < x → 0 < W x :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  have hcore : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => Real.log (W x)) :=
    AvramDividend.Classical.unbounded_scale_log_concavity_core X q hq W hW hnbv
  exact AvramDividend.Classical.esscher_tilted_log_concave_of_scale_log_concave
    φ W V hWpos hV hcore
