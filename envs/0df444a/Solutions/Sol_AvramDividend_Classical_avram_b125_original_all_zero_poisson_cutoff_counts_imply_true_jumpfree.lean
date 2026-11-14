-- Prove2me | solution 1 for AvramDividend.Classical.avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:48:20.640542+00:00
-- url     : https://prove2.me/submissions/17f70dee-ea7e-42aa-bed8-21b7273d392d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b118_original_finite_physically_marked_cells_one_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original all-negative-cutoff zero source counts forbid every true physical jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (hZero : ∀ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0) :
    ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by
  intro u hsu hut
  by_contra hne
  have hMarked : ∀ i ∈ ({0} : Finset ℕ), ∃ v : ℝ≥0,
      (fun _ : ℕ => s) i < v ∧ v ≤ (fun _ : ℕ => t) i ∧
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0 := by
    intro i hi
    exact ⟨u, hsu, hut, hne⟩
  obtain ⟨n, hCut⟩ :=
    avram_b118_original_finite_physically_marked_cells_one_cutoff
      X ω ({0} : Finset ℕ) (fun _ => s) (fun _ => t) hMarked
  obtain ⟨v, hsv, hvt, hBand⟩ := hCut 0 (by simp)
  have hNonzero :=
    (avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
      X ω s t hst n).mpr ⟨v, hsv, hvt, hBand⟩
  exact hNonzero (hZero n)
