-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb64_compensated_positive_part_expected_budget_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:42:09.2702+00:00
-- url     : https://prove2.me/submissions/70953f2b-1dda-4015-b412-cfd91b960943

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F J V : ℕ → Ω → ℝ) (b : ℝ)
    (hF : ∀ n, Integrable (F n) P)
    (hJ : ∀ n, Integrable (J n) P)
    (hV : ∀ n, Integrable (V n) P)
    (hMean : ∀ n, (∫ ω, J n ω ∂P) = (∫ ω, V n ω ∂P))
    (hPos : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in (atTop : Filter ℕ),
        (∫ ω, max (F n ω - (b + (J n ω - V n ω))) 0 ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in (atTop : Filter ℕ), (∫ ω, F n ω ∂P) ≤ b + ε  := by
  intro ε hε
  filter_upwards [hPos ε hε] with n hn
  have hN : Integrable (fun ω => J n ω - V n ω) P :=
    (hJ n).sub (hV n)
  have hBN : Integrable (fun ω => b + (J n ω - V n ω)) P :=
    (integrable_const _).add hN
  have hDiff : Integrable
      (fun ω => F n ω - (b + (J n ω - V n ω))) P :=
    (hF n).sub hBN
  have hMax : Integrable
      (fun ω => max (F n ω - (b + (J n ω - V n ω))) 0) P :=
    hDiff.sup (integrable_const _)
  have hLe : (∫ ω, F n ω - (b + (J n ω - V n ω)) ∂P) ≤
      (∫ ω, max (F n ω - (b + (J n ω - V n ω))) 0 ∂P) :=
    integral_mono hDiff hMax (fun ω => le_max_left _ _)
  have hDiffEq :
      (∫ ω, F n ω - (b + (J n ω - V n ω)) ∂P) =
      (∫ ω, F n ω ∂P) - b := by
    rw [integral_sub (hF n) hBN]
    have hB :
        (∫ ω, b + (J n ω - V n ω) ∂P) =
          b + ((∫ ω, J n ω ∂P) - (∫ ω, V n ω ∂P)) := by
      rw [integral_add (integrable_const _) hN]
      rw [integral_sub (hJ n) (hV n)]
      simp
    rw [hB, hMean n]
    ring
  linarith
