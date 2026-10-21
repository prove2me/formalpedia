-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_ratio_bound_tilted_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:26:29.678419+00:00
-- url     : https://prove2.me/submissions/92e7b173-62ac-42b6-bb75-300db21dfb98

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Gaussian Esscher ratio estimates imply tilted scale-function monotonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hσ : 0 < X.σ)
    (W : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hratio : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x / W y ≤ Real.exp (-φ * (y - x))) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  obtain ⟨φ, hφ, hψ⟩ :=
    positive_esscher_root_of_gaussian X q hq hσ
  have hdecay : ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-φ * (y - x)) * W y := by
    intro x y hx hxy
    have hy : 0 < W y := hpos y (lt_of_lt_of_le hx hxy)
    exact (div_le_iff₀ hy).mp (hratio φ hφ hψ x y hx hxy)
  exact ⟨φ, hφ, hψ,
    exit_decay_implies_tilted_monotone W φ hdecay⟩
