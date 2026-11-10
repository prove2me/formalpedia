-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin_source13_original_annulus_count_finite_every_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:51:15.445194+00:00
-- url     : https://prove2.me/submissions/02566f35-9c76-467e-8335-89b5cb41fa9a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_nested_cutoff_annulus_count_additive
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_factorial_pair_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every physical original annulus count is finite pathwise, not merely almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) (ω : Ω) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : ℝ≥0∞ :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    N ≠ ⊤ := by
  let c : ℝ := -(1 / ((n : ℝ) + 1))
  let d : ℝ := -(1 / ((m : ℝ) + 1))
  let J : Set ℝ → ℝ≥0∞ := fun B =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  change J (Ioc c d) ≠ ⊤
  have hSplit :=
    avram_mixed_source13_original_nested_cutoff_annulus_count_additive
      X T n m hnm ω
  change J (Iic d) = J (Iic c) + J (Ioc c d) at hSplit
  have hFull :=
    (avram_p4_f_assembly_original_negative_band_factorial_pair_identity
      X ω T m).1
  change J (Iic d) =
      ((avram_wave7_06_original_negative_band_marked_times_finite
        X ω T m).toFinset.card : ℝ≥0∞) at hFull
  have hFinite : J (Iic d) ≠ ⊤ := by
    rw [hFull]
    simp
  intro hTop
  have hBad : J (Iic d) = ⊤ := by
    simpa only [hTop, add_top] using hSplit
  exact hFinite hBad