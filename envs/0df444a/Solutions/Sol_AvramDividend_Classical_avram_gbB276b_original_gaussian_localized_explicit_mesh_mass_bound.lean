-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB276b_original_gaussian_localized_explicit_mesh_mass_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:38:44.273196+00:00
-- url     : https://prove2.me/submissions/aa9a69b7-e995-4a2d-922f-53d7f98ed03d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_gbB304_original_localized_fixed_level_hit_mesh_cover
import Theorems.Thm_AvramDividend_Classical_avram_gbB290_original_dividend_bad_cell_probability_time_mass_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB296_original_gaussian_good_cell_probability_time_mass_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB297_original_mesh_endpoint_probability_time_null
import Theorems.Thm_AvramDividend_Classical_avram_gbB298_original_bad_grid_hit_event_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB301_original_gaussian_good_bad_mesh_constant_assembly
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n M : ℕ) (m : ℕ) (hm : 0 < m) :
    (P.prod volume)
      {z : Ω × ℝ |
        0 < z.2 ∧ z.2 < (n : ℝ) ∧
        x + X.X (Real.toNNReal z.2) z.1 -
          rightLimit D (Real.toNNReal z.2) z.1 = b ∧
        D n z.1 - D 0 z.1 ≤ (M : ℝ)} ≤
      (Real.toNNReal
        (1 + (M : ℝ) +
          (2 * (n : ℝ)) /
            (X.σ * Real.sqrt (2 * Real.pi))) : ℝ≥0∞) *
            (m : ℝ≥0∞)⁻¹ := by
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℝ := 1 / ((m : ℝ) ^ 4)
  let N : ℕ := n * m ^ 4
  let E : Set (Ω × ℝ) := {z | z.2 ∈ Set.range
    (fun i : Fin N => (i : ℝ) * δ)}
  let B : Set (Ω × ℝ) := {z | ∃ i ∈ Finset.range N,
    z.2 ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) ∧
    1 / ((m : ℝ) ^ 3) <
      D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b ∧
    D n z.1 - D 0 z.1 ≤ (M : ℝ)}
  let G : Set (Ω × ℝ) := {z | ∃ i ∈ Finset.range N,
    z.2 ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) ∧
    D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
        1 / ((m : ℝ) ^ 3) ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b}
  let S : Set (Ω × ℝ) := {z |
    0 < z.2 ∧ z.2 < (n : ℝ) ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b ∧
    D n z.1 - D 0 z.1 ≤ (M : ℝ)}
  have hCover : S ⊆ E ∪ (B ∪ G) :=
    avram_gbB304_original_localized_fixed_level_hit_mesh_cover
      X x b D hD n M m hm
  have hBMeas : MeasurableSet B := by
    exact avram_gbB298_original_bad_grid_hit_event_joint_measurable
      X x b D hD n m M
  have hBinc : ∀ ω, (Prod.mk ω ⁻¹' B) ⊆
      ⋃ i ∈ ((Finset.range (n * m ^ 4)).filter
        (fun i => 1 / ((m : ℝ) ^ 3) <
          D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω -
          D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω)),
      Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) := by
    intro ω t ht
    obtain ⟨i, hi, hcell, hBad, _, _⟩ := ht
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨hi, hBad⟩, hcell⟩⟩
  have hBLocal : ∀ ω, (∃ t : ℝ, (ω, t) ∈ B) →
      D n ω - D 0 ω ≤ (M : ℝ) := by
    intro ω ⟨t, ht⟩
    obtain ⟨i, hi, hcell, hBad, hhit, hloc⟩ := ht
    exact hloc
  have hB : (P.prod volume) B ≤
      ENNReal.ofReal ((M : ℝ) / (m : ℝ)) := by
    exact avram_gbB290_original_dividend_bad_cell_probability_time_mass_bound
      D hD P n m M hm B hBMeas hBinc hBLocal
  have hG : (P.prod volume) G ≤
      (Real.toNNReal ((2 * (n : ℝ)) /
        (X.σ * Real.sqrt (2 * Real.pi))) : ℝ≥0∞) *
        (m : ℝ≥0∞)⁻¹ := by
    exact avram_gbB296_original_gaussian_good_cell_probability_time_mass_bound
      X hBV hν x b D hD n m hm
  have hE : (P.prod volume) E = 0 := by
    exact avram_gbB297_original_mesh_endpoint_probability_time_null P N δ
  have hσ : 0 < X.σ :=
    avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
      X hBV hν
  have hArith := avram_gbB301_original_gaussian_good_bad_mesh_constant_assembly
    X.σ hσ n M m hm
  change (P.prod volume) S ≤ _
  calc
    (P.prod volume) S ≤ (P.prod volume) (E ∪ (B ∪ G)) :=
      measure_mono hCover
    _ ≤ (P.prod volume) E + (P.prod volume) (B ∪ G) :=
      measure_union_le E _
    _ ≤ (P.prod volume) E + ((P.prod volume) B + (P.prod volume) G) := by
      exact add_le_add_right (measure_union_le B _) _
    _ = (P.prod volume) B + (P.prod volume) G := by rw [hE]; simp
    _ ≤ ENNReal.ofReal ((M : ℝ) / (m : ℝ)) +
      (Real.toNNReal ((2 * (n : ℝ)) /
        (X.σ * Real.sqrt (2 * Real.pi))) : ℝ≥0∞) *
        (m : ℝ≥0∞)⁻¹ := add_le_add hB hG
    _ ≤ _ := hArith
