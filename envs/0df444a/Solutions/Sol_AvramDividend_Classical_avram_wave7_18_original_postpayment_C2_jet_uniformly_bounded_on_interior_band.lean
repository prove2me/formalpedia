-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_postpayment_C2_jet_uniformly_bounded_on_interior_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:07:22.203746+00:00
-- url     : https://prove2.me/submissions/cdd83921-045d-4722-b62b-bf530dd4cc80

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (ω : Ω) (t : ℝ≥0),
        x + X.X t ω - rightLimit D t ω ∈ Set.Icc a b →
        |w (x + X.X t ω - rightLimit D t ω)| ≤ M ∧
        |deriv w (x + X.X t ω - rightLimit D t ω)| ≤ M ∧
        |deriv (deriv w) (x + X.X t ω - rightLimit D t ω)| ≤ M := by
  let S : Set ℝ := {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
  have hopen : IsOpen S := by
    have h1 : IsOpen {y : ℝ | 0 < y} := isOpen_Ioi
    have h2 : IsOpen {y : ℝ | ENNReal.ofReal y < C} :=
      isOpen_Iio.preimage ENNReal.continuous_ofReal
    exact h1.inter h2
  have hband : Set.Icc a b ⊆ S := by
    intro y hy
    exact ⟨lt_of_lt_of_le ha hy.1,
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hy.2) hbcap⟩
  have hw0 : ContinuousOn w (Set.Icc a b) :=
    hw.continuousOn.mono hband
  have hw1 : ContinuousOn (deriv w) (Set.Icc a b) :=
    (hw.continuousOn_deriv_of_isOpen hopen (by norm_num)).mono hband
  have hdiff1 : ContDiffOn ℝ 1 (deriv w) S :=
    hw.deriv_of_isOpen hopen (by norm_num)
  have hw2 : ContinuousOn (deriv (deriv w)) (Set.Icc a b) :=
    (hdiff1.continuousOn_deriv_of_isOpen hopen (by norm_num)).mono hband
  obtain ⟨M0, hM0⟩ :=
    (isCompact_Icc.bddAbove_image hw0.norm)
  obtain ⟨M1, hM1⟩ :=
    (isCompact_Icc.bddAbove_image hw1.norm)
  obtain ⟨M2, hM2⟩ :=
    (isCompact_Icc.bddAbove_image hw2.norm)
  let M : ℝ := max 0 (max M0 (max M1 M2))
  refine ⟨M, le_max_left _ _, ?_⟩
  intro ω t hz
  let z : ℝ := x + X.X t ω - rightLimit D t ω
  have hz0 : ‖w z‖ ≤ M0 := hM0 ⟨z, hz, rfl⟩
  have hz1 : ‖deriv w z‖ ≤ M1 := hM1 ⟨z, hz, rfl⟩
  have hz2 : ‖deriv (deriv w) z‖ ≤ M2 := hM2 ⟨z, hz, rfl⟩
  have hbound0 : M0 ≤ M :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hbound1 : M1 ≤ M :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hbound2 : M2 ≤ M :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  exact ⟨by simpa only [Real.norm_eq_abs] using le_trans hz0 hbound0,
    by simpa only [Real.norm_eq_abs] using le_trans hz1 hbound1,
    by simpa only [Real.norm_eq_abs] using le_trans hz2 hbound2⟩
