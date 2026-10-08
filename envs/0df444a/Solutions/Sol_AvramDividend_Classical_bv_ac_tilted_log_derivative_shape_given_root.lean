-- Prove2me | solution 1 for AvramDividend.Classical.bv_ac_tilted_log_derivative_shape_given_root
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:38:07.860489+00:00
-- url     : https://prove2.me/submissions/d3190522-4031-48ef-912c-c60016e6f353
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_bv_scale_exponential_tilt_strict_positive
import Theorems.Thm_AvramDividend_Classical_continuous_log_derivative_of_positive_C1
import Theorems.Thm_AvramDividend_Classical_log_derivative_antitone_of_concave_log
import Theorems.Thm_AvramDividend_Classical_nonnegative_of_positive_axis_antitone_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_bv_ac_tilted_scale_log_concavity_and_flat_tail

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
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (V g : ℝ → ℝ),
      (∀ x : ℝ, 0 < x → 0 < V x) ∧
      ContinuousOn g (Ioi (0 : ℝ)) ∧
      AntitoneOn g (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x → 0 ≤ g x) ∧
      Tendsto g atTop (𝓝 (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x) ∧
      (∀ x : ℝ, 0 < x → HasDerivAt V (V x * g x) x) := by
  let V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x
  have hVpos : ∀ x : ℝ, 0 < x → 0 < V x := by
    intro x hx
    exact bv_scale_exponential_tilt_strict_positive X hX q hq W hW hbv φ x hx
  have hWone : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_absolutely_continuous_levy X hX q hq W hW hac
  have hEone : ContDiffOn ℝ 1
      (fun x : ℝ => Real.exp (-(φ * x))) (Ioi (0 : ℝ)) := by
    fun_prop
  have hVone : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by
    exact hEone.mul hWone
  have hVdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ V x := by
    intro x hx
    exact (hVone.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt_one
  let g : ℝ → ℝ := fun x => deriv (fun y : ℝ => Real.log (V y)) x
  have hgcont : ContinuousOn g (Ioi (0 : ℝ)) :=
    continuous_log_derivative_of_positive_C1 V hVpos hVone
  have hVeq : ∀ x : ℝ, V x = Real.exp (-(φ * x)) * W x := by
    intro x
    rfl
  obtain ⟨hconcave, hglim⟩ :=
    bv_ac_tilted_scale_log_concavity_and_flat_tail
      X hX q hq W hW hbv hac φ hφ hroot V hVeq
  have hVderiv :
      ∀ x : ℝ, 0 < x → HasDerivAt V (V x * g x) x := by
    intro x hx
    have hv : V x ≠ 0 := (hVpos x hx).ne'
    have hd := (hVdiff x hx).hasDerivAt
    have hlog :
        deriv (fun y : ℝ => Real.log (V y)) x = deriv V x / V x :=
      (hd.log hv).deriv
    have heq : deriv V x = V x * g x := by
      calc
        deriv V x = V x * (deriv V x / V x) := by
          field_simp [hv]
        _ = V x * g x := by
          rw [← hlog]
    rw [← heq]
    exact hd
  have hganti : AntitoneOn g (Ioi (0 : ℝ)) :=
    log_derivative_antitone_of_concave_log V g hVpos hconcave hVderiv
  have hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x :=
    nonnegative_of_positive_axis_antitone_tendsto_zero g hganti hglim
  have htilt : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x := by
    intro x hx
    have he : Real.exp (φ * x) * Real.exp (-(φ * x)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      W x = 1 * W x := (one_mul _).symm
      _ = (Real.exp (φ * x) * Real.exp (-(φ * x))) * W x := by
        rw [he]
      _ = Real.exp (φ * x) * V x := by
        dsimp [V]
        ring
  exact ⟨V, g, hVpos, hgcont, hganti, hgnonneg, hglim, htilt, hVderiv⟩
