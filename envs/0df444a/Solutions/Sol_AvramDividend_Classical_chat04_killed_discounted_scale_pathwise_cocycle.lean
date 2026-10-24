-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_discounted_scale_pathwise_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:40:18.865112+00:00
-- url     : https://prove2.me/submissions/39c173fb-c34b-4f41-818e-3c0a33390b18

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_lower_killing_indicator_factorisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! Pathwise decomposition of the discounted killed scale payoff
across [0,s] and [s,u]. All states and endpoints are preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    ({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) =
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (s : ℝ))) *
          ({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
            0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
            (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
              W (x + X.X u ω)) ω) := by
  let A : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}
  let B : Set Ω := {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
    0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}
  let D : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}
  have hExp : Real.exp (-(q * (u : ℝ))) =
      Real.exp (-(q * (s : ℝ))) *
        Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsplit := AvramDividend.Classical.chat04_lower_killing_indicator_factorisation
    X x s u hsu
    (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω))
  change D.indicator (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) =
    A.indicator (fun ω => Real.exp (-(q * (s : ℝ))) *
      B.indicator (fun ω =>
        Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) * W (x + X.X u ω)) ω)
  have hInner :
      B.indicator (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) =
        (fun ω => Real.exp (-(q * (s : ℝ))) *
          B.indicator (fun ω =>
            Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) * W (x + X.X u ω)) ω) := by
    funext ω
    by_cases hb : ω ∈ B
    · have hterm : Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω) =
          Real.exp (-(q * (s : ℝ))) *
            (Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) * W (x + X.X u ω)) := by
          rw [hExp]
          ring
      simpa only [Set.indicator_of_mem hb] using hterm
    · simp only [Set.indicator_of_notMem hb, mul_zero]
  rw [hsplit]
  exact congrArg (fun g : Ω → ℝ => A.indicator g) hInner