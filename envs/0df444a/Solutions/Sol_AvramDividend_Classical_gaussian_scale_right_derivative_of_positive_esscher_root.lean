-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_scale_right_derivative_of_positive_esscher_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:02:15.246153+00:00
-- url     : https://prove2.me/submissions/8dedab0b-6db1-423b-8507-9d89a4bce82d

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_native_C1_derivative_resolvent_with_variance
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilt_vanishes_right_origin
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_continuous
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_locally_bounded
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_positive_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_causal_volterra_deriv_eq_resolvent_on_positive
import Theorems.Thm_AvramDividend_Classical_gaussian_right_slope_of_native_full_volterra_resolvent
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

/-- Recover the Gaussian right derivative using the native Esscher resolvent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 (2 / X.σ ^ 2)) := by
  let V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x
  have hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x := by
    intro x _
    rfl
  obtain ⟨β, K, g, hK, hg, hgC1, hVe, hge⟩ :=
    gaussian_esscher_native_C1_derivative_resolvent_with_variance
      X q hq W hW hσ φ hφ hroot V hV
  have hVlim : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    gaussian_esscher_tilt_vanishes_right_origin
      X q hq W hW hσ φ V hV
  have hVc : ContinuousOn V (Ioi (0 : ℝ)) :=
    gaussian_esscher_tilted_scale_continuous X q hq W hW hσ φ V hV
  have hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C :=
    gaussian_esscher_tilted_scale_locally_bounded
      X q hq W hW hσ φ hφ V hV
  have ha : 0 < X.σ ^ 2 / 2 := by positivity
  have hd : ∀ x : ℝ, 0 < x → deriv V x = g x :=
    causal_volterra_deriv_eq_resolvent_on_positive
      K g V (X.σ ^ 2 / 2) β ha hK hVc hVb hVe hg hge
  have hVdiff : DifferentiableOn ℝ V (Ioi (0 : ℝ)) := by
    have hc : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) :=
      esscher_tilted_scale_C1_of_positive_gaussian_without_standing
        X q hq W hW hσ φ hφ hroot V hV
    exact (contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn).1 hc |>.1
  have hVderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (g x) x := by
    intro x hx
    have hAt : DifferentiableAt ℝ V x :=
      (hVdiff x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
    rw [← hd x hx]
    exact hAt.hasDerivAt
  have hWpos : ∀ x : ℝ, 0 < x →
      W x = Real.exp (φ * x) * V x := by
    intro x _
    dsimp [V]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  exact gaussian_right_slope_of_native_full_volterra_resolvent
    X hσ W V g K φ β hWpos hVlim hK hg hge hVderiv
