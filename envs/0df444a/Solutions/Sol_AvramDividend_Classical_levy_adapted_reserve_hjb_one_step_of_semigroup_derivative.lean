-- Prove2me | solution 1 for AvramDividend.Classical.levy_adapted_reserve_hjb_one_step_of_semigroup_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:20:23.43512+00:00
-- url     : https://prove2.me/submissions/ed522a12-3230-4a35-a8e1-3761a0b0009b

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_levy_discounted_semigroup_le_initial_of_deriv_le
import Theorems.Thm_AvramDividend_Classical_levy_adapted_reserve_hjb_one_step_budget
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A differential HJB transition inequality closes the semigroup premise of the adapted one-step stochastic verification bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (w : ℝ → ℝ) (hw : Measurable w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (hInt : ∀ x : ℝ, Integrable (fun η => w (x + X.X (t - s) η)) P)
    (u a : Ω → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (ha : ∀ᵐ ω ∂P, 0 ≤ a ω)
    (hua : ∀ᵐ ω ∂P, a ω ≤ u ω)
    (huC : ∀ᵐ ω ∂P, ENNReal.ofReal (u ω) ≤ C)
    (hZ : Measurable[𝓕 s] (fun ω => u ω - a ω))
    (hZm : Measurable (fun ω => u ω - a ω))
    (hZI : Integrable (fun ω => u ω - a ω) P)
    (hZPay : Integrable
      (fun ω => w (u ω - a ω + (X.X t ω - X.X s ω))) P)
    (hSPay : ∀ n : ℕ, Integrable (fun ω =>
      w ((SimpleFunc.approxOn (fun η => u η - a η) hZm
        (Set.range (fun η => u η - a η) ∪ {0}) 0
        (by simp) n) ω + (X.X t ω - X.X s ω))) P)
    (f : Ω → ℝ → ℝ)
    (hf : ∀ᵐ ω ∂P,
      ContinuousOn (f ω) (Ici 0) ∧
      (∀ r : ℝ, 0 < r → DifferentiableAt ℝ (f ω) r) ∧
      (∀ r : ℝ, 0 < r → deriv (f ω) r ≤ q * f ω r) ∧
      f ω 0 ≤ w (u ω - a ω) ∧
      f ω ((t - s : ℝ≥0) : ℝ) =
        (∫ η, w (u ω - a ω + X.X (t - s) η) ∂P)) :
    ∀ᵐ ω ∂P,
      a ω + Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (P[(fun η => w (u η - a η +
          (X.X t η - X.X s η))) | 𝓕 s]) ω ≤
      w (u ω) := by
  have hsemi : ∀ᵐ ω ∂P,
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (∫ η, w (u ω - a ω + X.X (t - s) η) ∂P) ≤
      w (u ω - a ω) := by
    filter_upwards [hf] with ω hω
    rcases hω with ⟨hc, hd, hdr, hzero, htime⟩
    have hdt : (0 : ℝ) ≤ ((t - s : ℝ≥0) : ℝ) := by
      exact (t - s).property
    have hbound :=
      levy_discounted_semigroup_le_initial_of_deriv_le
        (f ω) q hc hd hdr ((t - s : ℝ≥0) : ℝ) hdt
    have hswap : -(q * ((t - s : ℝ≥0) : ℝ)) = -((t - s : ℝ≥0) : ℝ) * q := by ring
    rw [hswap] at hbound
    calc
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
          (∫ η, w (u ω - a ω + X.X (t - s) η) ∂P) =
        Real.exp (-((t - s : ℝ≥0) : ℝ) * q) * f ω ((t - s : ℝ≥0) : ℝ) := by rw [htime]
      _ ≤ f ω 0 := hbound
      _ ≤ w (u ω - a ω) := hzero
  exact levy_adapted_reserve_hjb_one_step_budget
    X s t hst w hw L hL hLip hInt u a q C
    hw_cont hw_smooth hw_hjb ha hua huC hZ hZm hZI
    hZPay hSPay hsemi
