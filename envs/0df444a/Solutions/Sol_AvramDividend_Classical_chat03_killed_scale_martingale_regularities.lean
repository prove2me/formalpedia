-- Prove2me | solution 1 for AvramDividend.Classical.chat03_killed_scale_martingale_regularities
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T10:59:40.042984+00:00
-- url     : https://prove2.me/submissions/008794db-ac68-4091-9b35-ebb75ff01564

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_payoff_adapted
import Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Mathlib.Data.Nat.Pairing
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
The downward-killed discounted scale payoff is adapted and integrable
at every finite deterministic time under Standing. Cantor pairing supplies
an explicit schedule, so there is no auxiliary grid assumption.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) :
    (Adapted 𝓕
      (fun (t : ℝ≥0) ω =>
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t ω)) ω)) ∧
    (∀ t : ℝ≥0, Integrable
      (({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω))) P) := by
  let τ : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)
  have hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹ := by
    intro n hn k
    simpa only [τ] using
      chat04_nat_pairing_rational_grid_coverage n k hn
  constructor
  · exact chat03_killed_scale_payoff_adapted X τ hCover q x W hW
  · intro t
    exact chat03_killed_scale_fixed_time_integrable
      X hX τ hCover q hq W hW x t
