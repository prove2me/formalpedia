-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a194_original_fullcell_small_Taylor_positive_raw_square_control
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:04:10.57749+00:00
-- url     : https://prove2.me/submissions/027cdecb-e326-4337-a7f7-cb38c3389961

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a190_original_stopped_source_small_raw_C2_Taylor_cell_modulus
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual full-cell discounted positive Taylor remainder is uniformly
bounded by arbitrarily small squared raw source energy on small cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hTopCap : C = ⊤) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ)
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ ω ∂P, ∀ m i : ℕ,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        s < ρ ω → s + Δ ≤ ρ ω → |r| < δ →
        max (Real.exp (-(q * (s : ℝ))) *
          (w (y + r) - w y - deriv w y * r -
            iteratedDeriv 2 w y / 2 * r^2)) 0 ≤ ε * r^2 := by
  intro ε hε
  obtain ⟨δ,hδ,hMod⟩ :=
    avram_ga_a190_original_stopped_source_small_raw_C2_Taylor_cell_modulus
      X x hx D hD C hTopCap w hw ρ j hprefix ε hε
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hMod] with ω hω
  intro m i
  dsimp only
  intro hs hfull hsmall
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let r : ℝ := X.X (s + Δ) ω - X.X s ω
  let y : ℝ := x + X.X s ω - rightLimit D s ω
  have hErr : |w (y + r) - w y - deriv w y * r -
        (iteratedDeriv 2 w y * r^2) / 2| ≤ ε * r^2 :=
    hω s (s + Δ) hs hsmall
  have hErr' : |w (y + r) - w y - deriv w y * r -
      iteratedDeriv 2 w y / 2 * r^2| ≤ ε * r^2 := by
    have hEq : (iteratedDeriv 2 w y * r^2) / 2 =
        iteratedDeriv 2 w y / 2 * r^2 := by ring
    simpa only [hEq] using hErr
  have he : 0 ≤ Real.exp (-(q * (s : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  have he1 : Real.exp (-(q * (s : ℝ))) ≤ 1 := by
    apply (Real.exp_le_one_iff).mpr
    have hs0 : 0 ≤ (s : ℝ) := NNReal.coe_nonneg _
    nlinarith
  calc
    max (Real.exp (-(q * (s : ℝ))) *
      (w (y + r) - w y - deriv w y * r -
        iteratedDeriv 2 w y / 2 * r^2)) 0 ≤
      |Real.exp (-(q * (s : ℝ))) *
        (w (y + r) - w y - deriv w y * r -
          iteratedDeriv 2 w y / 2 * r^2)| := by
        exact max_le (le_abs_self _) (abs_nonneg _)
    _ = Real.exp (-(q * (s : ℝ))) *
      |w (y + r) - w y - deriv w y * r -
        iteratedDeriv 2 w y / 2 * r^2| := by
        rw [abs_mul,abs_of_nonneg he]
    _ ≤ Real.exp (-(q * (s : ℝ))) * (ε * r^2) :=
      mul_le_mul_of_nonneg_left hErr' he
    _ ≤ ε * r^2 := by
      have hp : 0 ≤ ε * r^2 := mul_nonneg (le_of_lt hε) (sq_nonneg _)
      nlinarith
