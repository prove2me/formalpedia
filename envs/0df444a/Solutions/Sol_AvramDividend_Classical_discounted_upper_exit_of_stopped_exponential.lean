-- Prove2me | solution 1 for AvramDividend.Classical.discounted_upper_exit_of_stopped_exponential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:36:53.6378+00:00
-- url     : https://prove2.me/submissions/abc39dc6-7ff3-441c-8f93-69fedcb2fc69

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (a θ : ℝ) (hθ : 0 ≤ θ)
    (Y D : Ω → ℝ) (A : Set Ω)
    (hupper : ∀ ω : Ω, ω ∈ A → a ≤ Y ω)
    (hwhole : Integrable
      (fun ω => Real.exp (θ * Y ω - D ω)) P)
    (hpart : Integrable
      (A.indicator (fun ω => Real.exp (-D ω))) P)
    (hmean : (∫ ω, Real.exp (θ * Y ω - D ω) ∂P) ≤ 1) :
    (∫ ω, A.indicator (fun ω => Real.exp (-D ω)) ω ∂P) ≤
      Real.exp (-θ * a) := by
  have hpoint : ∀ ω : Ω,
      A.indicator (fun z => Real.exp (-D z)) ω ≤
        Real.exp (-θ * a) * Real.exp (θ * Y ω - D ω) := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have ha : θ * a ≤ θ * Y ω :=
        mul_le_mul_of_nonneg_left (hupper ω hω) hθ
      have he : Real.exp (θ * a - D ω) ≤
          Real.exp (θ * Y ω - D ω) :=
        Real.exp_le_exp.mpr (by linarith)
      calc
        Real.exp (-D ω) =
            Real.exp (-θ * a) * Real.exp (θ * a - D ω) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-θ * a) * Real.exp (θ * Y ω - D ω) :=
          mul_le_mul_of_nonneg_left he (le_of_lt (Real.exp_pos _))
    · rw [Set.indicator_of_notMem hω]
      exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (le_of_lt (Real.exp_pos _))
  have hscaled : Integrable
      (fun ω => Real.exp (-θ * a) * Real.exp (θ * Y ω - D ω)) P :=
    hwhole.const_mul _
  calc
    (∫ ω, A.indicator (fun z => Real.exp (-D z)) ω ∂P) ≤
        ∫ ω, Real.exp (-θ * a) *
          Real.exp (θ * Y ω - D ω) ∂P :=
      integral_mono hpart hscaled hpoint
    _ = Real.exp (-θ * a) *
        (∫ ω, Real.exp (θ * Y ω - D ω) ∂P) :=
      integral_const_mul _ _
    _ ≤ Real.exp (-θ * a) * 1 :=
      mul_le_mul_of_nonneg_left hmean (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-θ * a) := mul_one _
