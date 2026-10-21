-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_hjb_finite_dividend_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T14:46:39.450141+00:00
-- url     : https://prove2.me/submissions/e56a9843-66dc-4ab6-9ee2-b6b33289166a

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (u d : ℕ → ℝ)
    (hupdate : ∀ k : ℕ, u (k + 1) = u k - d k)
    (hpos : ∀ k : ℕ, 0 ≤ d k)
    (hsolv : ∀ k : ℕ, d k ≤ u k)
    (hcap : ∀ k : ℕ, ENNReal.ofReal (u k) ≤ C)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, d k) ≤ w (u 0) - w (u n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hsec : d n ≤ w (u n) - w (u (n + 1)) := by
        have hs := local_verification_hjb_controls_dividend_jump_le_cap
          X q w C hw_cont hw_smooth hw_hjb
          (u n) (d n) (hpos n) (hsolv n) (hcap n)
        rw [hupdate n]
        exact hs
      rw [Finset.sum_range_succ]
      change (∑ k ∈ Finset.range n, d k) + d n ≤
        w (u 0) - w (u (n + 1))
      linarith
