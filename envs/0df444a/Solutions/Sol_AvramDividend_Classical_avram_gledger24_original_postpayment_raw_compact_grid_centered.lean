-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger24_original_postpayment_raw_compact_grid_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:47:29.086369+00:00
-- url     : https://prove2.me/submissions/7ca3b0b3-ba1b-4661-b3ee-d8b6df166fc6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger23_original_postpayment_physical_grid_centered
import Theorems.Thm_AvramDividend_Classical_avram_gledger18_original_topcap_grid_zero_cell_band
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical compact-prefix bound removes the indicator from the exact
    postpayment-centred original Gaussian grid at strictly stopped times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (j n m : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let M : Ω → ℝ := fun ω => ∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let y := x + X.X s ω - rightLimit D s ω
        let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        Real.exp (-(q * (s : ℝ))) *
          (deriv w y * z + (iteratedDeriv 2 w y / 2) *
            (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by
  classical
  let a := min x ((1 : ℝ) / ((j : ℝ) + 1))
  let b := x + ((j : ℝ) + 1)
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - rightLimit D t ω
  let interior : ℝ → Prop := fun y => 0 < y ∧ ENNReal.ofReal y < C
  let M : Ω → ℝ := fun ω => ∑ i ∈ Finset.range m,
    let t : ℝ≥0 := (i : ℝ≥0) * Δ
    if t < ρ ω then
      let y := x + X.X t ω - rightLimit D t ω
      let z := X.X (t + Δ) ω - X.X t ω - (Δ : ℝ) * X.c
      Real.exp (-(q * (t : ℝ))) *
        (deriv w y * z + (iteratedDeriv 2 w y / 2) *
          (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
    else 0
  change Integrable M P ∧ (∫ ω, M ω ∂P) = 0
  have hPreBand :=
    avram_gledger18_original_topcap_grid_zero_cell_band
      X x hx D hD ρ j n m hprefix
  have hPostBand : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      s i < ρ ω → Y (s i) ω ∈ Icc a b := by
    filter_upwards [hprefix, hPreBand] with ω hp hb
    intro i hi hs
    have hLower := avram_gledger20_original_strict_prefix_postpayment_floor
      X x D hD ω (ρ ω) ((1 : ℝ) / ((j : ℝ) + 1))
      (fun t ht hlt => (hp t ht hlt).1) (s i) hs
    have hUpper := (hb i hi hs).2
    have hDiv := dividendStrategy_le_rightLimit D hD ω (s i)
    constructor
    · exact le_trans (min_le_right x ((1 : ℝ) / ((j : ℝ) + 1))) hLower
    · change x + X.X (s i) ω - rightLimit D (s i) ω ≤ b
      change x + X.X (s i) ω - D (s i) ω ≤ b at hUpper
      linarith
  have hClipped :=
    avram_gledger23_original_postpayment_physical_grid_centered
      X hBV hν q hq w C hTopCap hw x hx D hD ρ hρstop j n m
  have hAgree : M =ᵐ[P] (fun ω => ∑ i ∈ Finset.range m,
      let t : ℝ≥0 := (i : ℝ≥0) * Δ
      if t < ρ ω ∧ Y t ω ∈ Icc a b then
        let z := X.X (t + Δ) ω - X.X t ω - (Δ : ℝ) * X.c
        Real.exp (-(q * (t : ℝ))) *
          ((if interior (Y t ω) then deriv w (Y t ω) else 0) * z +
            ((if interior (Y t ω) then iteratedDeriv 2 w (Y t ω) else 0) / 2) *
              (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0) := by
    filter_upwards [hPostBand] with ω hb
    dsimp [M]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hs : s i < ρ ω
    · have he : s i < ρ ω ∧ Y (s i) ω ∈ Icc a b := ⟨hs, hb i hi hs⟩
      have ha : 0 < a := lt_min hx (one_div_pos.mpr (by positivity))
      have hInt : interior (Y (s i) ω) := by
        exact ⟨lt_of_lt_of_le ha he.2.1, by simp [hTopCap]⟩
      simp [s, Y, hs, he, hInt, mul_add] <;> ring
    · simp [s, hs]
  refine ⟨hClipped.1.congr hAgree.symm, ?_⟩
  exact (integral_congr_ae hAgree).trans hClipped.2
