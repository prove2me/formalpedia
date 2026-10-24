-- Prove2me | solution 1 for AvramDividend.Classical.levy_adapted_reserve_hjb_one_step_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:40:59.587067+00:00
-- url     : https://prove2.me/submissions/23bdc762-29f2-4486-9497-c08486af4aab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap
import Theorems.Thm_AvramDividend_Classical_levy_adapted_reserve_one_step_dividend_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (w : ℝ → ℝ) (hw : Measurable w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (hInt : ∀ x : ℝ, Integrable
      (fun η => w (x + X.X (t - s) η)) P)
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
    (hsemi : ∀ᵐ ω ∂P,
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (∫ η, w (u ω - a ω + X.X (t - s) η) ∂P) ≤ w (u ω - a ω)) :
    ∀ᵐ ω ∂P,
      a ω + Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
          (P[(fun η => w (u η - a η +
            (X.X t η - X.X s η))) | 𝓕 s]) ω ≤
      w (u ω) := by
  have hsec : ∀ᵐ ω ∂P, a ω ≤ w (u ω) - w (u ω - a ω) := by
    filter_upwards [ha, hua, huC] with ω haω huaω hcapω
    exact AvramDividend.Classical.local_verification_hjb_controls_dividend_jump_le_cap
      X q w C hw_cont hw_smooth hw_hjb
      (u ω) (a ω) haω huaω hcapω
  exact AvramDividend.Classical.levy_adapted_reserve_one_step_dividend_budget
    X s t hst w hw L hL hLip hInt u a q
    hZ hZm hZI hZPay hSPay hsec hsemi
