-- Prove2me | solution 1 for AvramDividend.Classical.avram_b109_original_no_negative_band_implies_jumpfree_from_spectral_noPos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:12:12.421192+00:00
-- url     : https://prove2.me/submissions/fc4bd5d5-986e-485b-a122-a6851696a5ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_interval_negative_band_count_ncard
import Theorems.Thm_AvramDividend_Classical_avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0)
    (hNoBand : ∀ n : ℕ, ∀ u : ℝ≥0, s < u → u ≤ t →
      ¬ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1)))) :
    ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by
  by_cases hst : s ≤ t
  · have hZero : ∀ n : ℕ,
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0 := by
      intro n
      rw [avram_p2_e_compensator_original_interval_negative_band_count_ncard
        X ω s t hst n]
      have hEmpty : {u : ℝ≥0 | s < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))} = ∅ := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hsu, hut, hneg⟩
        exact hNoBand n u hsu hut hneg
      rw [hEmpty]
      simp
    exact avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
      X ω s t hst hZero
  · intro u hsu hut
    exact False.elim (hst (le_trans hsu.le hut))
