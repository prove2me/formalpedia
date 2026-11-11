-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:45:23.815291+00:00
-- url     : https://prove2.me/submissions/1d999bee-f625-4006-aee6-88f4a55392d7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys72_original_zero_negative_mark_count_excludes_each_band
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A negative original jump would lie in one fixed negative annulus,
contradicting the source-exact zero marked count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hZero : ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) :
    ∀ u : ℝ≥0, 0 < u → u ≤ T →
      0 ≤ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u := by
  intro u hu huT
  let z : ℝ := X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  by_contra hnz
  have hz : z < 0 := lt_of_not_ge hnz
  let a : ℝ := -z
  have ha : 0 < a := by dsimp [a]; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / a)
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmul : 1 < (n : ℝ) * a :=
    (div_lt_iff₀ ha).mp hn
  have hmul2 : 1 ≤ a * ((n : ℝ) + 1) := by nlinarith
  have hdiv : 1 / ((n : ℝ) + 1) ≤ a :=
    (div_le_iff₀ hnpos).mpr hmul2
  have hband : z ≤ -(1 / ((n : ℝ) + 1)) := by
    dsimp [a] at hdiv
    linarith
  have hnone := avram_bvb_phys72_original_zero_negative_mark_count_excludes_each_band
    X ω T n hZero
  exact hnone ⟨u, hu, huT, hband⟩
