-- Prove2me | solution 1 for AvramDividend.Classical.bv_ac_tilted_scale_log_concavity_and_flat_tail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:02:47.223008+00:00
-- url     : https://prove2.me/submissions/319926b3-54a5-48ee-9176-452f58917798
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_bv_scale_exponential_tilt_strict_positive
import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_tilted_scale_log_concave
import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_tilted_scale_positive_finite_limit
import Theorems.Thm_AvramDividend_Classical_tendsto_deriv_zero_of_concave_finite_limit

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
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) ∧
      Tendsto (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x)
        atTop (𝓝 (0 : ℝ)) := by
  have hWone : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_absolutely_continuous_levy X hX q hq W hW hac
  have hEone : ContDiffOn ℝ 1
      (fun x : ℝ => Real.exp (-(φ * x))) (Ioi (0 : ℝ)) := by
    fun_prop
  have hVfun : V = (fun x : ℝ => Real.exp (-(φ * x)) * W x) :=
    funext hV
  have hVone : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by
    rw [hVfun]
    exact hEone.mul hWone
  have hVpos : ∀ x : ℝ, 0 < x → 0 < V x := by
    intro x hx
    rw [hV x]
    exact bv_scale_exponential_tilt_strict_positive X hX q hq W hW hbv φ x hx
  have hLogOne : ContDiffOn ℝ 1 (fun x : ℝ => Real.log (V x))
      (Ioi (0 : ℝ)) := by
    exact hVone.log (by
      intro x hx
      exact (hVpos x hx).ne')
  have hLogDiff :
      ∀ x : ℝ, 0 < x →
        DifferentiableAt ℝ (fun y : ℝ => Real.log (V y)) x := by
    intro x hx
    exact (hLogOne.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt_one
  have hconc :=
    bv_ac_esscher_tilted_scale_log_concave
      X hX q hq W hW hbv hac φ hφ hroot V hV
  obtain ⟨L, hL, hVlim⟩ :=
    bv_ac_esscher_tilted_scale_positive_finite_limit
      X hX q hq W hW hbv hac φ hφ hroot V hV
  have hloglim :
      Tendsto (fun x : ℝ => Real.log (V x))
        atTop (𝓝 (Real.log L)) :=
    (Real.continuousAt_log hL.ne').tendsto.comp hVlim
  have hflat :
      Tendsto (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x)
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_deriv_zero_of_concave_finite_limit
      (fun x : ℝ => Real.log (V x)) (Real.log L)
      hconc hLogDiff hloglim
  exact ⟨hconc, hflat⟩
