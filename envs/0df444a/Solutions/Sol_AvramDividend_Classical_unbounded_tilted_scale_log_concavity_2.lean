-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_tilted_scale_log_concavity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:16:56.133331+00:00
-- url     : https://prove2.me/submissions/e2389111-01a2-4a3a-becf-9e6141ed9463
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_log_concavity_core
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_log_concave_of_scale_log_concave
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
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
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  have hWconcave : ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun x : ℝ => Real.log (W x)) :=
    unbounded_scale_log_concavity_core X q hq W hW hnbv
  exact esscher_tilted_log_concave_of_scale_log_concave φ W V hWpos hV hWconcave
