-- Prove2me | solution 8 for AvramDividend.Classical.unbounded_tilted_scale_log_concavity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T20:48:59.138523+00:00
-- url     : https://prove2.me/submissions/0a192c92-4d16-4e30-ab35-f22dd7ff4069

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_log_concavity_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity

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
  have hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    have hx0 : 0 ≤ x := le_of_lt hx
    exact AvramDividend.Classical.unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a x ha hx0 hxa
  have hVd : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ V x := by
    intro x hx
    exact (hVdiff x hx).differentiableAt
  have hWdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    have hmem : Ioi (0 : ℝ) ∈ 𝓝 x := Ioi_mem_nhds hx
    have hEq : ∀ᶠ y in 𝓝 x, W y = Real.exp (φ * y) * V y := by
      filter_upwards [hmem] with y hy
      have hypos : 0 < y := hy
      have hVy : V y = Real.exp (-(φ * y)) * W y := hV y hypos
      have hexp : Real.exp (φ * y) * Real.exp (-(φ * y)) = 1 := by
        rw [← Real.exp_add]
        simp [add_neg_cancel]
      calc W y = 1 * W y := by ring_nf
        _ = (Real.exp (φ * y) * Real.exp (-(φ * y))) * W y := by rw [hexp]
        _ = Real.exp (φ * y) * (Real.exp (-(φ * y)) * W y) := by ring
        _ = Real.exp (φ * y) * V y := by rw [← hVy]
    have hExp : DifferentiableAt ℝ (fun y : ℝ => Real.exp (φ * y)) x :=
      (Real.differentiableAt_exp.comp x
        (((differentiableAt_const φ).mul differentiableAt_id)))
    have hProd : DifferentiableAt ℝ (fun y => Real.exp (φ * y) * V y) x :=
      hExp.mul (hVd x hx)
    exact hProd.congr_of_eventuallyEq hEq
  have hConc := AvramDividend.Classical.unbounded_tilted_scale_log_concavity_of_corrected_exit
    X q hq W hW hnbv hExit φ hWdiff
  have hEqOn : Set.EqOn (fun z : ℝ => Real.log (Real.exp (-φ * z) * W z))
      (fun x : ℝ => Real.log (V x)) (Ioi (0 : ℝ)) := by
    intro z hz
    simp only [Set.mem_Ioi] at hz
    show Real.log (Real.exp (-φ * z) * W z) = Real.log (V z)
    rw [hV z hz]
    rw [show -φ * z = -(φ * z) from by ring]
  exact hConc.congr hEqOn
