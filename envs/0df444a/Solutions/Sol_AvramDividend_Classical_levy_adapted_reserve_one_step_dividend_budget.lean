-- Prove2me | solution 1 for AvramDividend.Classical.levy_adapted_reserve_one_step_dividend_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:30:59.416268+00:00
-- url     : https://prove2.me/submissions/8a525af5-e016-4681-9dbe-db3677916018

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_integrable_adapted_reserve_lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
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
    (u a : Ω → ℝ) (q : ℝ)
    (hZ : Measurable[𝓕 s] (fun ω => u ω - a ω))
    (hZm : Measurable (fun ω => u ω - a ω))
    (hZI : Integrable (fun ω => u ω - a ω) P)
    (hZPay : Integrable
      (fun ω => w (u ω - a ω + (X.X t ω - X.X s ω))) P)
    (hSPay : ∀ n : ℕ, Integrable (fun ω =>
      w ((SimpleFunc.approxOn (fun η => u η - a η) hZm
        (Set.range (fun η => u η - a η) ∪ {0}) 0
        (by simp) n) ω + (X.X t ω - X.X s ω))) P)
    (hsec : ∀ᵐ ω ∂P, a ω ≤ w (u ω) - w (u ω - a ω))
    (hsemi : ∀ᵐ ω ∂P,
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (∫ η, w (u ω - a ω + X.X (t - s) η) ∂P) ≤ w (u ω - a ω)) :
    ∀ᵐ ω ∂P,
      a ω + Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
          (P[(fun η => w (u η - a η +
            (X.X t η - X.X s η))) | 𝓕 s]) ω ≤
      w (u ω) := by
  have hm :=
    AvramDividend.Classical.levy_increment_condExp_integrable_adapted_reserve_lipschitz
      X s t hst w hw L hL hLip hInt
      (fun ω => u ω - a ω) hZ hZm hZI hZPay hSPay
  filter_upwards [hm, hsec, hsemi] with ω hω hsecω hsemiω
  rw [hω]
  linarith
