-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_strict_pos_of_infinite_small_jump_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:03:34.459541+00:00
-- url     : https://prove2.me/submissions/ddac8b19-b1b1-4a17-83e7-ec2c4b5652c2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_gaussian
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_psi_quadratic_upper
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_eventual_psi_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
        ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ∀ a : ℝ, 0 < a → 0 < W a := by
  intro a ha
  by_cases hσpos : 0 < X.σ
  · exact scaleFunction_strict_pos_of_gaussian X q W hW hσpos a ha
  · have hσzero : X.σ = 0 :=
      le_antisymm (le_of_not_gt hσpos) X.σ_nonneg
    let qpos : ℝ := max q 1
    have hqpos : 0 < qpos := by
      dsimp [qpos]
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right q 1)
    have hqqpos : q ≤ qpos := le_max_left q 1
    obtain ⟨β₀, hβ₀, hψpos⟩ :=
      psi_eventually_gt_of_infinite_small_jump_moment
        X hσzero hvar qpos hqpos
    let β : ℝ := max 1 β₀
    let K : ℝ :=
      |X.c| + X.σ ^ 2 / 2 +
        ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂X.ν
    let C : ℝ := |K| + |q|
    have hβ : 0 ≤ β := by
      dsimp [β]
      linarith [le_max_left (1 : ℝ) β₀]
    have hβone : 1 ≤ β := le_max_left _ _
    have hβ₀β : β₀ ≤ β := le_max_right _ _
    have hψ : ∀ θ : ℝ, β ≤ θ → q < X.ψ θ := by
      intro θ hθ
      exact lt_of_le_of_lt hqqpos (hψpos θ (le_trans hβ₀β hθ))
    have hquadratic : ∀ θ : ℝ, β ≤ θ →
        X.ψ θ - q ≤ C * (1 + θ ^ 2) := by
      intro θ hθ
      have hθone : 1 ≤ θ := le_trans hβone hθ
      have hup := psi_quadratic_upper X θ hθone
      have hK : X.ψ θ ≤ K * θ ^ 2 := by
        simpa only [K] using hup
      have hKabs : K ≤ |K| := le_abs_self K
      have hqabs : -q ≤ |q| := neg_le_abs q
      have hθsq : 0 ≤ θ ^ 2 := sq_nonneg θ
      have hKabs0 : 0 ≤ |K| := abs_nonneg K
      have hqabs0 : 0 ≤ |q| := abs_nonneg q
      have hKmul : K * θ ^ 2 ≤ |K| * θ ^ 2 :=
        mul_le_mul_of_nonneg_right hKabs hθsq
      have hqmul : 0 ≤ |q| * θ ^ 2 :=
        mul_nonneg hqabs0 hθsq
      dsimp [C]
      nlinarith
    exact scaleFunction_strict_pos_of_eventual_psi_bound
      X q W hW β C hβ hψ hquadratic a ha
