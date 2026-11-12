-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja22_original_finite_cutoff_strip_finite_mark_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:24:39.001268+00:00
-- url     : https://prove2.me/submissions/d20a48f9-c07e-4a8f-b144-bdc1e671f15f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18j_public_original_compensated_finsum
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n m : ℕ) (t : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    ∃ (F G : Finset ℝ≥0),
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ t ∧
        -1 < j u ∧ j u ≤ -(1 / ((n : ℝ) + 1))) ∧
      (∀ u : ℝ≥0, u ∈ G ↔ 0 < u ∧ u ≤ t ∧
        -1 < j u ∧ j u ≤ -(1 / ((m : ℝ) + 1))) ∧
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω =
          ((∑ u ∈ G, j u) -
            (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
              (-(1 / ((m : ℝ) + 1))), z ∂X.ν)) -
          ((∑ u ∈ F, j u) -
            (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
              (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) := by
  obtain ⟨F, hF, hFEq⟩ :=
    avram_ja18j_public_original_compensated_finsum X n t ω
  obtain ⟨G, hG, hGEq⟩ :=
    avram_ja18j_public_original_compensated_finsum X m t ω
  refine ⟨F, G, hF, hG, ?_⟩
  rw [avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
    X n m t ω, hGEq, hFEq]
