-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_global_weighted_norm_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T19:08:20.351666+00:00
-- url     : https://prove2.me/submissions/8c3acb53-2dea-425c-af2a-e1c0a9f711af

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_chat03_scale_global_weighted_exponential_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) :
    BddAbove (Set.range (fun y : ℝ =>
      ‖Real.exp (-(θ * y)) * W y‖)) := by
  have hmono : Monotone W := scaleFunction_monotone X q W hW
  have hnonneg (y : ℝ) : 0 ≤ W y := by
    by_cases hneg : y < 0
    · simp [hW.1 y hneg]
    · have hnegone : W (-1) = 0 := hW.1 (-1) (by norm_num)
      have hh := hmono (show (-1 : ℝ) ≤ y by linarith)
      simpa [hnegone] using hh
  let C : ℝ := Real.exp θ * (X.ψ θ - q)⁻¹
  refine ⟨C, ?_⟩
  rintro z ⟨y, rfl⟩
  have hb := chat03_scale_global_weighted_exponential_bound
    X q W hW θ y hθ hψ
  have he : Real.exp (-(θ * y)) =
      Real.exp θ * Real.exp (-(θ * (y + 1))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hnonnegvalue : 0 ≤ Real.exp (-(θ * y)) * W y :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (hnonneg y)
  change ‖Real.exp (-(θ * y)) * W y‖ ≤ C
  rw [Real.norm_eq_abs, abs_of_nonneg hnonnegvalue, he]
  dsimp [C]
  calc
    (Real.exp θ * Real.exp (-(θ * (y + 1)))) * W y =
        Real.exp θ * (Real.exp (-(θ * (y + 1))) * W y) := by ring
    _ ≤ Real.exp θ * (X.ψ θ - q)⁻¹ :=
      mul_le_mul_of_nonneg_left hb (le_of_lt (Real.exp_pos θ))
