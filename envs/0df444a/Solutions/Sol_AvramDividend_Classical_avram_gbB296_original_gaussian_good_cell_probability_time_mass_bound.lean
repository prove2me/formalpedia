-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB296_original_gaussian_good_cell_probability_time_mass_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:53:51.190066+00:00
-- url     : https://prove2.me/submissions/75370be2-be52-4316-acd9-0b4046a59d3f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_gbB299_original_single_gaussian_good_cell_probability_time_mass
import Theorems.Thm_AvramDividend_Classical_avram_gbB300_gaussian_fourth_power_cell_sum_scaling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n m : ℕ) (hm : 0 < m) :
    (P.prod volume)
      {z : Ω × ℝ | ∃ i ∈ Finset.range (n * m ^ 4),
        z.2 ∈ Set.Ioo
          ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
          (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
        D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
          D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
          1 / ((m : ℝ) ^ 3) ∧
        x + X.X (Real.toNNReal z.2) z.1 -
          rightLimit D (Real.toNNReal z.2) z.1 = b} ≤
      (Real.toNNReal ((2 * (n : ℝ)) /
        (X.σ * Real.sqrt (2 * Real.pi))) : ℝ≥0∞) *
        (m : ℝ≥0∞)⁻¹ := by
  have hσ : 0 < X.σ :=
    avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
      X hBV hν
  let K : ℝ≥0∞ := (Real.toNNReal (2 /
    (X.σ * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5))) : ℝ≥0∞)
  let S : ℕ → Set (Ω × ℝ) := fun i =>
    {z : Ω × ℝ |
            z.2 ∈ Set.Ioo
              ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
              (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
            D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
              D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
              1 / ((m : ℝ) ^ 3) ∧
            x + X.X (Real.toNNReal z.2) z.1 -
              rightLimit D (Real.toNNReal z.2) z.1 = b}
  have hSingle (i : ℕ) : (P.prod volume) (S i) ≤ K := by
    exact avram_gbB299_original_single_gaussian_good_cell_probability_time_mass
      X hBV hν x b D hD m i hm
  have hSum :
      (P.prod volume) (⋃ i ∈ Finset.range (n * m ^ 4), S i) ≤
        ∑ i ∈ Finset.range (n * m ^ 4), (P.prod volume) (S i) :=
    measure_biUnion_finset_le (Finset.range (n * m ^ 4)) S
  have hCount : (∑ i ∈ Finset.range (n * m ^ 4), K) =
      ((n * m ^ 4 : ℕ) : ℝ≥0∞) * K := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hCover : {z : Ω × ℝ | ∃ i ∈ Finset.range (n * m ^ 4),
        z.2 ∈ Set.Ioo
          ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
          (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
        D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
          D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
          1 / ((m : ℝ) ^ 3) ∧
        x + X.X (Real.toNNReal z.2) z.1 -
          rightLimit D (Real.toNNReal z.2) z.1 = b} =
        (⋃ i ∈ Finset.range (n * m ^ 4), S i) := by
    ext z
    constructor
    · rintro ⟨i, hi, htime, hdiv, hhit⟩
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨hi, ⟨htime, hdiv, hhit⟩⟩⟩
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hi, htime, hdiv, hhit⟩ := Set.mem_iUnion.mp hi
      exact ⟨i, hi, htime, hdiv, hhit⟩
  rw [hCover]
  calc
    (P.prod volume) (⋃ i ∈ Finset.range (n * m ^ 4), S i) ≤
        ∑ i ∈ Finset.range (n * m ^ 4), (P.prod volume) (S i) := hSum
    _ ≤ ∑ i ∈ Finset.range (n * m ^ 4), K := by
      exact Finset.sum_le_sum (fun i _ => hSingle i)
    _ = ((n * m ^ 4 : ℕ) : ℝ≥0∞) * K := hCount
    _ = _ := by
      exact avram_gbB300_gaussian_fourth_power_cell_sum_scaling
        X.σ hσ n m hm
