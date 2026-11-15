-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a306_original_true_fullcell_preincrement_reserve_uniform_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:03:43.288783+00:00
-- url     : https://prove2.me/submissions/fa482a80-42d2-42dc-b70f-e42324b76a7e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gledger73_original_strict_prefix_postpayment_ceiling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let B : ℝ := x + ((j : ℝ) + 1)
    0 ≤ B ∧ ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      s < ρ ω →
        x + X.X s ω - rightLimit D s ω ≤ B := by
  dsimp
  constructor
  · have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    linarith
  · intro m
    filter_upwards [hprefix] with ω hp
    intro i hi hs
    let Δ : ℝ≥0 := (n : ℝ≥0)/((m : ℝ≥0)+1)
    let s : ℝ≥0 := (i : ℝ≥0)*Δ
    change s < ρ ω at hs
    change x+X.X s ω-rightLimit D s ω ≤ x+((j : ℝ)+1)
    exact avram_gledger73_original_strict_prefix_postpayment_ceiling
      X x D hD ω (ρ ω) (x+((j : ℝ)+1))
      (fun t ht hts => (hp t ht hts).2) s hs
