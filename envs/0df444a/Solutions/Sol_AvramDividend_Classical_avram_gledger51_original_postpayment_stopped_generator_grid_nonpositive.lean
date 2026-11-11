-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger51_original_postpayment_stopped_generator_grid_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:29:36.802425+00:00
-- url     : https://prove2.me/submissions/3ebf5dd5-45b8-41b2-bbb5-726a394140cc

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j n m : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let G : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) *
            (X.generator w (x + X.X s ω - rightLimit D s ω) -
              q * w (x + X.X s ω - rightLimit D s ω))
        else 0
    ∀ᵐ ω ∂P, G ω ≤ 0 := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let G : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) *
          (X.generator w (x + X.X s ω - rightLimit D s ω) -
            q * w (x + X.X s ω - rightLimit D s ω))
      else 0
  change ∀ᵐ ω ∂P, G ω ≤ 0
  filter_upwards [hprefix] with ω hω
  dsimp [G]
  apply Finset.sum_nonpos
  intro i hi
  split_ifs with hs
  · have hpost :=
      (avram_gledger20_original_strict_prefix_postpayment_floor
        X x D hD ω (ρ ω) ((1 : ℝ) / ((j : ℝ) + 1)) hω)
        ((i : ℝ≥0) * Δ) hs
    have hy : 0 < x + X.X ((i : ℝ≥0) * Δ) ω -
        rightLimit D ((i : ℝ≥0) * Δ) ω := by
      have hb : 0 < (1 : ℝ) / ((j : ℝ) + 1) := by positivity
      exact lt_of_lt_of_le hb hpost
    have hcap : ENNReal.ofReal
        (x + X.X ((i : ℝ≥0) * Δ) ω -
          rightLimit D ((i : ℝ≥0) * Δ) ω) < C := by
      simp [hTopCap]
    have hsign := hw_gen _ hy hcap
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact mul_nonneg (by positivity) (le_of_lt (Real.exp_pos _))
    · exact hsign
  · exact le_refl 0
