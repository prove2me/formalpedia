-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger54_original_stopped_source_cell_prepayment_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:32:04.630705+00:00
-- url     : https://prove2.me/submissions/35b3411d-8ae2-4a67-8758-f3678cd52e0b

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_positive_stop_terminal_prepayment_band
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- A stopped physical cell retains the strict prefix floor before its right-endpoint dividend. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j n m : ℕ) (hn : 0 < n)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let v : ℝ≥0 := min (((i + 1 : ℕ) : ℝ≥0) * Δ) (ρ ω)
      s < ρ ω →
        (1 : ℝ) / ((j : ℝ) + 1) ≤
          x + X.X v ω - rightLimit D s ω := by
  let u : ℝ := (1 : ℝ) / ((j : ℝ) + 1)
  let b : ℝ := x + ((j : ℝ) + 1)
  have hterm :=
    avram_gledger20_original_positive_stop_terminal_prepayment_band
      X hν x D hD ρ u b hprefix
  filter_upwards [hprefix, hterm] with ω hω htω
  intro i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let v : ℝ≥0 := min (((i + 1 : ℕ) : ℝ≥0) * Δ) (ρ ω)
  change s < ρ ω → u ≤ x + X.X v ω - rightLimit D s ω
  intro hs
  have hΔ : 0 < Δ := by
    dsimp [Δ]
    apply div_pos
    · exact_mod_cast hn
    · positivity
  have hi : (i : ℝ≥0) < ((i + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.lt_succ_self i
  have hstep : s < ((i + 1 : ℕ) : ℝ≥0) * Δ :=
    mul_lt_mul_of_pos_right hi hΔ
  have hsv : s < v := lt_min hstep hs
  have hvpos : 0 < v := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hsv
  have hvle : v ≤ ρ ω := min_le_right _ _
  have hu : u ≤ riskProcess X x D v ω := by
    rcases lt_or_eq_of_le hvle with hvlt | hveq
    · exact (hω v hvpos hvlt).1
    · have hρpos : 0 < ρ ω :=
        lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hs
      simpa [hveq] using (htω hρpos).1
  have hnonneg : ∀ t : ℝ≥0, 0 ≤ D t ω := by
    intro t
    have ht := (hD.2.1 ω) (show (0 : ℝ≥0) ≤ t from zero_le)
    simpa [hD.1 ω] using ht
  have hbdd : BddBelow
      (Set.range (fun t : Ioi s => D (t : ℝ≥0) ω)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨t, rfl⟩
    exact hnonneg t
  have hDle : rightLimit D s ω ≤ D v ω := by
    unfold rightLimit
    exact ciInf_le hbdd (⟨v, hsv⟩ : Ioi s)
  dsimp [riskProcess] at hu
  linarith
