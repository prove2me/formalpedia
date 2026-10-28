-- Prove2me | solution 8 for AvramDividend.Classical.unbounded_tilted_positive_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:34:11.915794+00:00
-- url     : https://prove2.me/submissions/1e10d56c-b39e-4677-97f9-be8ef69c3846
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
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
    (hnbv : ¬ X.BoundedVariation) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  -- Principal route: Proved 4b96094e gives positivity plus tilted monotonicity
  -- (with Esscher root equation) from a universal corrected-exit hypothesis.
  -- Supply that hypothesis pointwise from Open 6d3911f8 with verbatim binders.
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) :=
    fun a x ha hx hxa =>
      AvramDividend.Classical.unbounded_corrected_exit_scale_identity
        X q hq W hW hnbv a x ha hx hxa
  obtain ⟨hpos, φ, hφ, _hroot, hmono⟩ :=
    AvramDividend.Classical.unbounded_positive_tilt_of_corrected_exit
      X q hq W hW hnbv hExit
  refine ⟨hpos, φ, hφ, ?_⟩
  have hfun : (fun x : ℝ => Real.exp (-φ * x) * W x) =
      (fun x : ℝ => Real.exp (-(φ * x)) * W x) := by
    funext x
    congr 1
    congr 1
    ring
  rw [hfun]
  exact hmono
