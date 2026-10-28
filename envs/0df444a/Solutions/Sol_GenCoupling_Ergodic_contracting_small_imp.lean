-- Prove2me | solution 1 for GenCoupling.Ergodic.contracting_small_imp
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:31:18.146731+00:00
-- url     : https://prove2.me/submissions/f8cdc0c3-1d67-485d-8361-d18137b35dbf

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open GenCoupling.Ergodic in
theorem solution {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℝ≥0 → Kernel E E) (hP : IsMarkovSemigroup P) (t : ℝ≥0) (d : E → E → ℝ) (B : Set E)
    (hc : IsContracting P t d) (hs : IsSmall P t d B) :
    (∀ x y, W d (P t x) (P t y) ≤ ENNReal.ofReal (d x y)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ B, ∀ y ∈ B,
        W d (P t x) (P t y) ≤ ENNReal.ofReal ((1 - ε) * d x y) := by
  obtain ⟨hd, hd1, α, hα, hW⟩ := hc
  obtain ⟨ε, hε, hsm⟩ := hs
  haveI := hP.1 t
  have hW1 : ∀ x y, W d (P t x) (P t y) ≤ 1 := by
    intro x y
    unfold W
    have hcpl : (P t x).prod (P t y) ∈ couplings (P t x) (P t y) := by
      constructor <;> simp
    refine (iInf₂_le _ hcpl).trans ?_
    calc ∫⁻ p, ENNReal.ofReal (d p.1 p.2) ∂((P t x).prod (P t y))
        ≤ ∫⁻ _p, 1 ∂((P t x).prod (P t y)) := by
          apply lintegral_mono
          intro p
          exact ENNReal.ofReal_le_one.mpr (hd1 _ _)
      _ = 1 := by simp
  have hdnn : ∀ x y, 0 ≤ d x y := hd.1
  constructor
  · intro x y
    by_cases hlt : d x y < 1
    · refine (hW x y hlt).trans (ENNReal.ofReal_le_ofReal ?_)
      nlinarith [hdnn x y]
    · have : d x y = 1 := le_antisymm (hd1 x y) (not_lt.mp hlt)
      rw [this, ENNReal.ofReal_one]
      exact hW1 x y
  · refine ⟨min ε (1 - α), lt_min hε (by linarith), ?_⟩
    intro x hx y hy
    have hm1 : min ε (1 - α) ≤ ε := min_le_left _ _
    have hm2 : min ε (1 - α) ≤ 1 - α := min_le_right _ _
    by_cases hlt : d x y < 1
    · refine (hW x y hlt).trans (ENNReal.ofReal_le_ofReal ?_)
      have : α ≤ 1 - min ε (1 - α) := by linarith
      exact mul_le_mul_of_nonneg_right this (hdnn x y)
    · have : d x y = 1 := le_antisymm (hd1 x y) (not_lt.mp hlt)
      rw [this, mul_one]
      exact (hsm x hx y hy).trans (ENNReal.ofReal_le_ofReal (by linarith))
