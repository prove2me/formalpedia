-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB284_original_bad_cell_prob_time_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:04:48.802671+00:00
-- url     : https://prove2.me/submissions/17804c68-c887-471c-8846-09524002b474

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB278_bad_dividend_grid_time_union_le_inverse_mesh_variation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A sample-path bad-grid time bound gives a probability-time bound. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : Ω → ℕ → ℝ) (hmono : ∀ ω, Monotone (d ω))
    (n m M : ℕ) (hm : 0 < m)
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (hinc : ∀ ω, (Prod.mk ω ⁻¹' S) ⊆
      ⋃ i ∈ ((Finset.range (n * m ^ 4)).filter
        (fun i => 1 / ((m : ℝ) ^ 3) < d ω (i + 1) - d ω i)),
      Set.Ioo ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))))
    (hloc : ∀ ω, (∃ t : ℝ, (ω, t) ∈ S) →
      d ω (n * m ^ 4) - d ω 0 ≤ (M : ℝ)) :
    (P.prod volume) S ≤ ENNReal.ofReal ((M : ℝ) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfiber : ∀ ω, volume (Prod.mk ω ⁻¹' S) ≤
      ENNReal.ofReal ((M : ℝ) / (m : ℝ)) := by
    intro ω
    by_cases hne : ∃ t : ℝ, (ω, t) ∈ S
    · calc
        volume (Prod.mk ω ⁻¹' S) ≤
            volume (⋃ i ∈ ((Finset.range (n * m ^ 4)).filter
              (fun i => 1 / ((m : ℝ) ^ 3) < d ω (i + 1) - d ω i)),
              Set.Ioo ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
                (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4)))) :=
          measure_mono (hinc ω)
        _ ≤ ENNReal.ofReal ((d ω (n * m ^ 4) - d ω 0) / (m : ℝ)) :=
          avram_gbB278_bad_dividend_grid_time_union_le_inverse_mesh_variation
            (d ω) (hmono ω) n m hm
        _ ≤ ENNReal.ofReal ((M : ℝ) / (m : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          exact div_le_div_of_nonneg_right (hloc ω hne) hmR.le
    · have hempty : Prod.mk ω ⁻¹' S = ∅ := by
        ext t
        constructor
        · intro ht
          exact False.elim (hne ⟨t, ht⟩)
        · simp
      simp [hempty]
  rw [Measure.prod_apply hS]
  calc
    (∫⁻ ω, volume (Prod.mk ω ⁻¹' S) ∂P) ≤
      ∫⁻ _ω, ENNReal.ofReal ((M : ℝ) / (m : ℝ)) ∂P := by
        exact lintegral_mono hfiber
    _ = _ := by simp
