-- Prove2me | solution 1 for AvramDividend.Classical.bv_ac_esscher_tilted_scale_positive_finite_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:46:13.327731+00:00
-- url     : https://prove2.me/submissions/aeb6b300-c84e-4dc6-bc95-dd36d13ebc30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_esscher_finite_renewal_cumulative_representation
import Theorems.Thm_AvramDividend_Classical_positive_finite_measure_cumulative_converges

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, V x = Real.exp (-(φ * x)) * W x) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (𝓝 L) := by
  obtain ⟨β, hβpos, hβfinite, hcumulative⟩ :=
    bv_esscher_finite_renewal_cumulative_representation
      X hX q hq W hW hbv φ hφ hroot
  obtain ⟨L, hLpos, hLlim⟩ :=
    positive_finite_measure_cumulative_converges β hβfinite hβpos
  refine ⟨L, hLpos, ?_⟩
  have hevent :
      V =ᶠ[atTop] (fun x : ℝ => (β (Iic x)).toReal) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [hV x]
    exact hcumulative x hx
  exact hLlim.congr' hevent.symm
