-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_unit_damped_indicator_bounded_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T19:26:42.654983+00:00
-- url     : https://prove2.me/submissions/56ab646f-7ea4-4af4-8abe-476e1824dd04

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_positive_indicator_continuous
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_psi_strictly_above_root
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_norm_bddAbove

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    Continuous ((Ioi (0 : ℝ)).indicator
      (fun x : ℝ => Real.exp (-x) * V x)) ∧
    BddAbove (Set.range (fun x : ℝ =>
      ‖(Ioi (0 : ℝ)).indicator (fun y : ℝ => Real.exp (-y) * V y) x‖)) := by
  have hcontV :=
    gaussian_esscher_positive_indicator_continuous
      X q hq W hW hσ φ V hV
  have hfun :
      ((Ioi (0 : ℝ)).indicator (fun x : ℝ => Real.exp (-x) * V x)) =
        (fun x : ℝ => Real.exp (-x) *
          ((Ioi (0 : ℝ)).indicator V) x) := by
    funext x
    by_cases hx : 0 < x
    · simp only [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    · simp only [Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), mul_zero]
  have hcont :
      Continuous ((Ioi (0 : ℝ)).indicator
        (fun x : ℝ => Real.exp (-x) * V x)) := by
    rw [hfun]
    exact (Real.continuous_exp.comp continuous_neg).mul hcontV
  have hneg : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) < ⊤ := by
    exact lt_of_le_of_lt
      (lintegral_mono_set (Set.subset_univ _))
      (by simpa only [Measure.restrict_univ] using X.ν_integrable)
  have hpush := gaussian_levy_square_integrable_neg_pushforward X.ν hneg
  have hψ : q < X.ψ (φ + 1) :=
    gaussian_esscher_psi_strictly_above_root
      X q φ 1 hq hφ (by norm_num) hσ hroot hpush
  obtain ⟨C, hC⟩ := scaleFunction_global_weighted_norm_bddAbove
    X q W hW (φ + 1) (by linarith) hψ
  have hC0 : 0 ≤ C := by
    have hb : ‖Real.exp (-((φ + 1) * (0 : ℝ))) * W 0‖ ≤ C :=
      hC ⟨0, rfl⟩
    exact le_trans (norm_nonneg _) hb
  refine ⟨hcont, ⟨C, ?_⟩⟩
  rintro z ⟨x, rfl⟩
  by_cases hx : 0 < x
  · have hv : Real.exp (-x) * V x =
        Real.exp (-((φ + 1) * x)) * W x := by
      rw [hV x hx]
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      ring
    change ‖(Ioi (0 : ℝ)).indicator
      (fun y : ℝ => Real.exp (-y) * V y) x‖ ≤ C
    rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), hv]
    exact hC ⟨x, rfl⟩
  · change ‖(Ioi (0 : ℝ)).indicator
      (fun y : ℝ => Real.exp (-y) * V y) x‖ ≤ C
    rw [Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
    simpa using hC0
