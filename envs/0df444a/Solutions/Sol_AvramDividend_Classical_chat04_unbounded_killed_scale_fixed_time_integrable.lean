-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_killed_scale_fixed_time_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:00:11.40613+00:00
-- url     : https://prove2.me/submissions/32f54b2e-a342-4b3f-99f5-c89c828c1760

import Mathlib.Data.Nat.Pairing
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_scale_fixed_time_integrable_of_cover
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (t : ℝ≥0) :
    Integrable (({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
      (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) P := by
  let τ : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)
  have hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹ := by
    intro n hn k
    exact chat04_nat_pairing_rational_grid_coverage n k hn
  exact chat04_unbounded_killed_scale_fixed_time_integrable_of_cover
    X τ hCover q hq W hW hnbv x t
