-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise18_original_negative_cutoff_counts_monotone_exhaust
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:44:49.099123+00:00
-- url     : https://prove2.me/submissions/7e447a00-7751-4d31-8d44-b5147a7fc3e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_all_negative_marks_exhausted_by_threshold_bands

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original negative-mark cutoff counts increase to the full count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω) :
    let Ncut : ℕ → ℝ≥0∞ := fun n =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let Nall : ℝ≥0∞ :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))
    Monotone Ncut ∧ Nall = ⨆ n : ℕ, Ncut n := by
  intro Ncut Nall
  let J : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hInterval (n : ℕ) :
      {z : ℝ | z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z} =
        Iic (-(1 / ((n : ℝ) + 1))) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    constructor
    · intro hz
      linarith [hz.2]
    · intro hz
      have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      exact ⟨by linarith, by linarith⟩
  have hMono : Monotone Ncut := by
    intro n m hnm
    have hm : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hRec : (1 : ℝ) / ((m : ℝ) + 1) ≤
        1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hm
    have hSet :
        Iic (-(1 / ((n : ℝ) + 1))) ⊆
          Iic (-(1 / ((m : ℝ) + 1))) := by
      intro z hz
      exact hz.trans (neg_le_neg hRec)
    change J (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≤
      J (Ioc 0 T ×ˢ Iic (-(1 / ((m : ℝ) + 1))))
    exact measure_mono (Set.prod_mono (Subset.rfl) hSet)
  refine ⟨hMono, ?_⟩
  have hCount :
      Nall = ⨆ n : ℕ,
        J (Ioc 0 T ×ˢ
          {z : ℝ | z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}) := by
    exact avram_p4_b_smalljump_original_intrinsic_all_negative_marks_exhausted_by_threshold_bands
      X 0 T ω
  calc
    Nall = ⨆ n : ℕ,
        J (Ioc 0 T ×ˢ
          {z : ℝ | z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}) := hCount
    _ = ⨆ n : ℕ, Ncut n := by
      apply iSup_congr
      intro n
      simpa only [hInterval n, Ncut, J]