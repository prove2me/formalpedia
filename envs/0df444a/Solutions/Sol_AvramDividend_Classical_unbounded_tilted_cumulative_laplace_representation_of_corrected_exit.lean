-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_corrected_exit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:28:02.62827+00:00
-- url     : https://prove2.me/submissions/118ed015-02f4-4a01-995b-6d90507c9322

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilt_global_monotone_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_continuous_monotone_real_has_stieltjes_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x) =
          ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
            (β (Iic x)).toReal := by
  obtain ⟨φ, hφ, hroot⟩ := AvramDividend.Classical.positive_esscher_root_of_unbounded_variation X hnbv q hq
  have hW0 := AvramDividend.Classical.unbounded_scale_zero_origin_nonnegative_discount X hnbv q hq.le W hW
  have hWc := AvramDividend.Classical.scaleFunction_global_continuous_of_zero_origin X q W hW hW0
  have hmono := AvramDividend.Classical.unbounded_esscher_tilt_global_monotone_of_corrected_exit
    X q hq W hW hnbv φ hφ hroot hExit
  have hWnn : ∀ y, 0 ≤ W y := by
    intro y
    rcases lt_or_ge y 0 with h | h
    · rw [hW.1 y h]
    · exact hW.2.1 y h
  set F : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x with hF
  have hFc : Continuous F := (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul hWc
  have hFbot : Filter.Tendsto F Filter.atBot (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_lt_atBot (0:ℝ)] with x hx
    simp [hF, hW.1 x hx]
  obtain ⟨β, hβ⟩ :=
    AvramDividend.Classical.continuous_monotone_real_has_stieltjes_cumulative_measure F hmono hFc hFbot
  obtain ⟨b0, hb0, hb⟩ := AvramDividend.Classical.chat04_psi_eventually_gt_of_unbounded_variation X q hq hnbv
  have hFnn : ∀ x, 0 ≤ F x := fun x => mul_nonneg (Real.exp_pos _).le (hWnn x)
  have e1 : ∀ θ : ℝ, (fun x : ℝ => Real.exp (-θ * x) * (Real.exp (-φ * x) * W x)) =
      fun x => Real.exp (-((θ + φ) * x)) * W x := by
    intro θ; funext x
    rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  have e2 : ∀ θ : ℝ, (fun x : ℝ => Real.exp (-θ * x) * (β (Iic x)).toReal) =
      fun x => Real.exp (-θ * x) * (Real.exp (-φ * x) * W x) := by
    intro θ; funext x
    rw [hβ x, ENNReal.toReal_ofReal (hFnn x), hF]; simp only [neg_mul]
  refine ⟨β, φ, b0 - φ, hφ, fun x => by rw [hβ x]; exact ENNReal.ofReal_ne_top, ?_, ?_⟩
  · intro x hx
    rw [hβ x]
    exact ENNReal.ofReal_pos.2 (mul_pos (Real.exp_pos _)
      (AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv x hx))
  · intro θ hθ
    obtain ⟨hint, -⟩ := hW.2.2.2.2 (θ + φ) (by linarith) (hb (θ + φ) (by linarith))
    have h1 : IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * (Real.exp (-φ * x) * W x)) (Ioi 0) := by
      rw [e1 θ]; exact hint
    refine ⟨h1, ?_, ?_⟩
    · rw [e2 θ]; exact h1
    · rw [e2 θ]
