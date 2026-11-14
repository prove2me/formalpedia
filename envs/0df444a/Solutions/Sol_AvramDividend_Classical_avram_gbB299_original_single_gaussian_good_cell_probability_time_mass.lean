-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB299_original_single_gaussian_good_cell_probability_time_mass
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:06:05.137901+00:00
-- url     : https://prove2.me/submissions/7c075d5b-9a20-4c6f-9c34-a598bbf3d4e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_gbB305_original_single_cell_fibre_probability_envelope
import Theorems.Thm_AvramDividend_Classical_avram_gbB306_original_real_time_good_cell_gaussian_fibre_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB307_original_good_cell_fixed_level_hit_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB308_original_gaussian_fibre_exact_cell_time_lintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (m i : ℕ) (hm : 0 < m) :
    (P.prod volume)
      {z : Ω × ℝ |
        z.2 ∈ Set.Ioo
          ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
          (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
        D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
          D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
          1 / ((m : ℝ) ^ 3) ∧
        x + X.X (Real.toNNReal z.2) z.1 -
          rightLimit D (Real.toNNReal z.2) z.1 = b} ≤
      (Real.toNNReal (2 /
        (X.σ * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5))) : ℝ≥0∞) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let s : ℝ := (i : ℝ) * (1 / ((m : ℝ) ^ 4))
  let u : ℝ := ((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))
  let C : ℝ≥0∞ :=
    (Real.toNNReal (2 /
      (X.σ * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5))) : ℝ≥0∞)
  let S : Set (Ω × ℝ) := {z |
    z.2 ∈ Set.Ioo s u ∧
    D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
      1 / ((m : ℝ) ^ 3) ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b}
  let g : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal
      ((Real.sqrt (2 * Real.pi *
        (((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) *
          ((Real.toNNReal t -
            ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) : ℝ≥0) : NNReal) : ℝ))))⁻¹) *
      ENNReal.ofReal (1 / ((m : ℝ) ^ 3))
  have hσ : 0 < X.σ :=
    avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos X hBV hν
  have hS : MeasurableSet S :=
    avram_gbB307_original_good_cell_fixed_level_hit_joint_measurable
      X x b D hD m i
  have hInside : ∀ t ∈ Set.Ioo s u,
      P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t := by
    intro t ht
    have hEq : ((fun ω : Ω => (ω, t)) ⁻¹' S) =
        {ω : Ω |
          D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω -
            D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω ≤
            1 / ((m : ℝ) ^ 3) ∧
          x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω = b} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, S, ht, true_and]
    rw [hEq]
    exact avram_gbB306_original_real_time_good_cell_gaussian_fibre_bound
      X hBV hν D hD m i hm t ht x b
  have hOutside : ∀ t ∉ Set.Ioo s u,
      P ((fun ω : Ω => (ω, t)) ⁻¹' S) = 0 := by
    intro t ht
    have hempty : ((fun ω : Ω => (ω, t)) ⁻¹' S) = ∅ := by
      ext ω
      constructor
      · intro hz
        exact False.elim (ht hz.1)
      · simp
    simp [hempty]
  have hIntegral : (∫⁻ t in Set.Ioo s u, g t ∂volume) ≤ C :=
    avram_gbB308_original_gaussian_fibre_exact_cell_time_lintegral
      X.σ hσ m i hm
  change (P.prod volume) S ≤ C
  exact avram_gbB305_original_single_cell_fibre_probability_envelope
    P S hS s u g C hInside hOutside hIntegral
