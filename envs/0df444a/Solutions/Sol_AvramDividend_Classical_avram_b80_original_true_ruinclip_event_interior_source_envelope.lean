-- Prove2me | solution 1 for AvramDividend.Classical.avram_b80_original_true_ruinclip_event_interior_source_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:02:22.564186+00:00
-- url     : https://prove2.me/submissions/ed3bec11-b62c-4d69-abe4-1bb1a60b85c3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b65_original_strict_preruin_X_lower
import Theorems.Thm_AvramDividend_Classical_avram_b69_original_true_spatial_clock_ruin_clipped
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On any selected good event the original ruin-clipped strict interior cells remain in their physical source compact band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (k : ℕ) (A : Set Ω) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hInterior : ∀ ω ∈ A, ∀ i ∈ S,
      s i ω ≤ t i ω ∧
      (t i ω : ℝ≥0∞) < (κ k ω : ℝ≥0∞)) :
    ∀ ω ∈ A, ∀ i ∈ S,
      (s i ω ≤ t i ω ∧ t i ω ≤ (n : ℝ≥0)) ∧
      (-x ≤ X.X (s i ω) ω ∧ -x ≤ X.X (t i ω) ω) ∧
      ((s i ω : ℝ≥0∞) <
         twoSidedExitUpTime X ((k : ℝ) + 1) ω ∧
       (t i ω : ℝ≥0∞) <
         twoSidedExitUpTime X ((k : ℝ) + 1) ω) := by
  intro ω hω i hi
  obtain ⟨hst, htk⟩ := hInterior ω hω i hi
  have hκ :=
    avram_b69_original_true_spatial_clock_ruin_clipped
      X x D n ρ hρclip κ hκexact k ω
  have hTκ : t i ω ≤ κ k ω := by
    exact_mod_cast (le_of_lt htk)
  have hTn : t i ω ≤ (n : ℝ≥0) :=
    (hTκ.trans hκ.1).trans (hρbound ω)
  have hstE : (s i ω : ℝ≥0∞) ≤ (t i ω : ℝ≥0∞) := by
    exact_mod_cast hst
  have hTRuin : (t i ω : ℝ≥0∞) < ruinTime X x D ω :=
    lt_of_lt_of_le htk hκ.2
  have hSRuin : (s i ω : ℝ≥0∞) < ruinTime X x D ω :=
    lt_of_le_of_lt hstE hTRuin
  have hSLower : -x ≤ X.X (s i ω) ω :=
    avram_b65_original_strict_preruin_X_lower
      X x C D hD ω (s i ω) (Or.inr hSRuin)
  have hTLower : -x ≤ X.X (t i ω) ω :=
    avram_b65_original_strict_preruin_X_lower
      X x C D hD ω (t i ω) (Or.inr hTRuin)
  have hκup : (κ k ω : ℝ≥0∞) ≤
      twoSidedExitUpTime X ((k : ℝ) + 1) ω := by
    rw [hκexact k ω]
    have hminfinite :
        min (ρ ω : ℝ≥0∞)
          (twoSidedExitUpTime X ((k : ℝ) + 1) ω) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp)
        (min_le_left (ρ ω : ℝ≥0∞)
          (twoSidedExitUpTime X ((k : ℝ) + 1) ω))
    rw [ENNReal.coe_toNNReal hminfinite]
    exact min_le_right _ _
  have hTUp : (t i ω : ℝ≥0∞) <
      twoSidedExitUpTime X ((k : ℝ) + 1) ω :=
    lt_of_lt_of_le htk hκup
  have hSUp : (s i ω : ℝ≥0∞) <
      twoSidedExitUpTime X ((k : ℝ) + 1) ω :=
    lt_of_le_of_lt hstE hTUp
  exact ⟨⟨hst, hTn⟩, ⟨hSLower, hTLower⟩, ⟨hSUp, hTUp⟩⟩
