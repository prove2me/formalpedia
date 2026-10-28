-- Prove2me | solution 7 for AvramDividend.Classical.unbounded_tilted_scale_log_concavity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:58:18.348869+00:00
-- url     : https://prove2.me/submissions/ae2f6017-0e10-45b1-9e98-22551eea0bf2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
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
  have hWdiff : ∀ z : ℝ, 0 < z → DifferentiableAt ℝ W z := by
    intro z hz
    have hVd : DifferentiableAt ℝ V z := (hVdiff z hz).differentiableAt
    have hexp : DifferentiableAt ℝ (fun w : ℝ => Real.exp (φ * w)) z :=
      Real.differentiableAt_exp.comp z ((differentiableAt_const φ).mul differentiableAt_id)
    have hprod : DifferentiableAt ℝ (fun w : ℝ => Real.exp (φ * w) * V w) z :=
      hexp.mul hVd
    have heq : (fun w : ℝ => Real.exp (φ * w) * V w) =ᶠ[𝓝 z] W := by
      filter_upwards [Ioi_mem_nhds hz] with w hw
      have hVw : V w = Real.exp (-(φ * w)) * W w := hV w hw
      have hinv : Real.exp (φ * w) * Real.exp (-(φ * w)) = 1 := by
        rw [← Real.exp_add]
        simp
      calc Real.exp (φ * w) * V w
          = (Real.exp (φ * w) * Real.exp (-(φ * w))) * W w := by
            rw [hVw]; ring
        _ = W w := by rw [hinv, one_mul]
    exact hprod.congr_of_eventuallyEq heq.symm
  have hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact AvramDividend.Classical.unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a x ha (le_of_lt hx) hxa
  have hConc : ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun z : ℝ => Real.log (Real.exp (-φ * z) * W z)) :=
    AvramDividend.Classical.unbounded_tilted_scale_log_concavity_of_corrected_exit
      X q hq W hW hnbv hExit φ hWdiff
  have hEq : Set.EqOn (fun z : ℝ => Real.log (Real.exp (-φ * z) * W z))
      (fun x : ℝ => Real.log (V x)) (Ioi (0 : ℝ)) := by
    intro w hw
    simp only [Set.mem_Ioi] at hw
    show Real.log (Real.exp (-φ * w) * W w) = Real.log (V w)
    rw [hV w hw, neg_mul]
  exact hConc.congr hEq
