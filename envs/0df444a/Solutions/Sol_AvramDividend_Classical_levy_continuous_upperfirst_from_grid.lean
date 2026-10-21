-- Prove2me | solution 1 for AvramDividend.Classical.levy_continuous_upperfirst_from_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:20:27.509426+00:00
-- url     : https://prove2.me/submissions/4d938114-450b-41f5-8f65-3f14b3d6b4b5

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_two_sided_strict_exit_no_finite_tie
import Theorems.Thm_AvramDividend_Classical_continuous_upperfirst_bound_from_grid
import Mathlib.Order.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- For separated Lévy barriers, upper-first continuous discount bounds follow from grid limits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a x : ℝ) (ha : 0 < a) (hxa : x ≤ a)
    (upGrid downGrid : ℕ → Ω → ENNReal)
    (hu : ∀ ω, Tendsto (fun n => upGrid n ω) atTop
      (nhds (twoSidedExitUpTime X (a - x) ω)))
    (hd : ∀ ω, Tendsto (fun n => downGrid n ω) atTop
      (nhds (twoSidedExitDownTime X (-x) ω)))
    (hMeas : ∀ n : ℕ, Measurable
      (fun ω => if upGrid n ω < downGrid n ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (upGrid n ω))))
        else 0))
    (B : ENNReal)
    (hGrid : ∀ n : ℕ,
      (∫⁻ ω, (if upGrid n ω < downGrid n ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (upGrid n ω))))
        else 0) ∂P) ≤ B) :
    (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp
        (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0) ∂P) ≤ B := by
  have hSep : ∀ ω,
      twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω ∨
      twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω ∨
      (twoSidedExitUpTime X (a - x) ω = ⊤ ∧
        twoSidedExitDownTime X (-x) ω = ⊤) := by
    intro ω
    by_cases hUpper : twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω
    · exact Or.inl hUpper
    by_cases hLower : twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω
    · exact Or.inr (Or.inl hLower)
    have heq : twoSidedExitUpTime X (a - x) ω =
        twoSidedExitDownTime X (-x) ω :=
      le_antisymm (le_of_not_gt hLower) (le_of_not_gt hUpper)
    have hInf :=
      chat04_two_sided_strict_exit_no_finite_tie X a x ha hxa ω heq
    exact Or.inr (Or.inr ⟨hInf, heq.symm.trans hInf⟩)
  exact AvramDividend.Classical.continuous_upperfirst_bound_from_grid
    P q (twoSidedExitUpTime X (a - x))
    (twoSidedExitDownTime X (-x))
    upGrid downGrid hu hd hSep hMeas B hGrid
