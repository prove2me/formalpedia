-- Prove2me | solution 1 for AvramDividend.Classical.levy_grid_upper_exit_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:37:49.43098+00:00
-- url     : https://prove2.me/submissions/2ad6add2-9e91-407b-b12b-202a590e14b7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_compensated_exp_integrable
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_compensated_exp_moment_one
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The stopped Lévy exponential bounds the discounted upper exit of a finite two-sided grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → NNReal) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Ioi (0 : ℝ)) 0 m ω)
    (hpart : Integrable
      ({ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
        (fun ω => Real.exp
          (-((clock (K ω)) : ℝ) * X.ψ θ))) P) :
    (∫ ω, {ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
      (fun z => Real.exp (-((clock (K z)) : ℝ) * X.ψ θ)) ω ∂P) ≤
      Real.exp (-θ * upper) := by
  have hint :=
    chat03_two_sided_grid_compensated_exp_integrable
      X clock hc H hH θ hθ lower upper m K hK
  have hmean :=
    chat03_two_sided_grid_compensated_exp_moment_one
      X clock hc hc0 H hH θ hθ lower upper m K hK
  let Y : Ω → ℝ := fun ω => X.X (clock (K ω)) ω
  let D : Ω → ℝ := fun ω => ((clock (K ω)) : ℝ) * X.ψ θ
  let S : Set Ω := {ω | upper < Y ω}
  have hI : Integrable (fun ω => Real.exp (θ * Y ω - D ω)) P := hint
  have hJ : Integrable
      (S.indicator (fun ω => Real.exp (-D ω))) P := by
    simpa only [S, D, Y, neg_mul] using hpart
  have hM : (∫ ω, Real.exp (θ * Y ω - D ω) ∂P) ≤ 1 :=
    le_of_eq hmean
  have hpoint : ∀ ω : Ω,
      S.indicator (fun z => Real.exp (-D z)) ω ≤
        Real.exp (-θ * upper) *
          Real.exp (θ * Y ω - D ω) := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have hupper : upper ≤ Y ω := le_of_lt hω
      have ha : θ * upper ≤ θ * Y ω :=
        mul_le_mul_of_nonneg_left hupper hθ
      have he : Real.exp (θ * upper - D ω) ≤
          Real.exp (θ * Y ω - D ω) :=
        Real.exp_le_exp.mpr (by linarith)
      calc
        Real.exp (-D ω) =
            Real.exp (-θ * upper) *
              Real.exp (θ * upper - D ω) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-θ * upper) *
            Real.exp (θ * Y ω - D ω) :=
          mul_le_mul_of_nonneg_left he (le_of_lt (Real.exp_pos _))
    · simp only [Set.indicator, if_neg hω]
      exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (le_of_lt (Real.exp_pos _))
  have hscaled : Integrable
      (fun ω => Real.exp (-θ * upper) *
        Real.exp (θ * Y ω - D ω)) P := hI.const_mul _
  have hfinal : (∫ ω, S.indicator
      (fun z => Real.exp (-D z)) ω ∂P) ≤
        Real.exp (-θ * upper) := by
    calc
      (∫ ω, S.indicator
          (fun z => Real.exp (-D z)) ω ∂P) ≤
        ∫ ω, Real.exp (-θ * upper) *
          Real.exp (θ * Y ω - D ω) ∂P :=
        integral_mono hJ hscaled hpoint
      _ = Real.exp (-θ * upper) *
          (∫ ω, Real.exp (θ * Y ω - D ω) ∂P) :=
        integral_const_mul _ _
      _ ≤ Real.exp (-θ * upper) * 1 :=
        mul_le_mul_of_nonneg_left hM (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-θ * upper) := mul_one _
  simpa only [S, D, Y, neg_mul] using hfinal
