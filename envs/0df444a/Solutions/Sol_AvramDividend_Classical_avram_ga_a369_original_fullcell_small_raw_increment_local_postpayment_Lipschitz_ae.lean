-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a369_original_fullcell_small_raw_increment_local_postpayment_Lipschitz_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:16:53.723188+00:00
-- url     : https://prove2.me/submissions/5229c1e8-69e4-47dc-99db-a5da00768509

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_ga_a204_positive_compact_C2_source_small_raw_local_Lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n : ℕ) (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧
      ∀ᵐ ω ∂P, ∀ m i : ℕ,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        s < ρ ω → |r| < δ →
          |w (y + r) - w y| ≤ L * |r| := by
  let a : ℝ := 1 / ((j : ℝ) + 1)
  let b : ℝ := x + ((j : ℝ) + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hDen : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact (div_le_iff₀ hDen).2 (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
  have hb1 : 1 ≤ b := by
    dsimp [b]
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hab : a ≤ b := le_trans ha1 hb1
  have hSub : {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} = Ioi (0 : ℝ) := by
    ext y
    simp [hTopCap]
  have hwPos : ContDiffOn ℝ 2 w (Ioi (0 : ℝ)) := by
    simpa only [hSub] using hw
  obtain ⟨L,hL,hLip⟩ :=
    avram_ga_a204_positive_compact_C2_source_small_raw_local_Lipschitz
      w hwPos a b ha hab
  have hBand := avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
    X x D hD ρ j hprefix
  refine ⟨a / 2,by positivity,L,hL,?_⟩
  filter_upwards [hBand] with ω hω
  intro m i
  dsimp
  intro hs hr
  have hy : x + X.X ((i : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
      rightLimit D ((i : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω ∈ Icc a b := by
    exact hω _ hs
  exact hLip _ hy _ hr
