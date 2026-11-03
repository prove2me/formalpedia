-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_and_levy_intensity_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:30:16.513362+00:00
-- url     : https://prove2.me/submissions/c9c92aea-34bd-4b97-bdcd-06b6979de8ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Both actual intrinsic counts and Lévy intensity increase with the small-jump cutoff index. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    (let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     NX (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≤
       NX (Ioc 0 T ×ˢ Iic (-(1 / ((m : ℝ) + 1)))) ∧
     X.ν (Iic (-(1 / ((n : ℝ) + 1)))) ≤
       X.ν (Iic (-(1 / ((m : ℝ) + 1)))) ) := by
  classical
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change NX (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≤
      NX (Ioc 0 T ×ˢ Iic (-(1 / ((m : ℝ) + 1)))) ∧
    X.ν (Iic (-(1 / ((n : ℝ) + 1)))) ≤
      X.ν (Iic (-(1 / ((m : ℝ) + 1))))
  have hnmR : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    exact_mod_cast (Nat.add_le_add_right hnm 1)
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hfrac : (1 : ℝ) / ((m : ℝ) + 1) ≤
      1 / ((n : ℝ) + 1) := by
    apply (div_le_div_iff₀ hmpos hnpos).2
    simpa using hnmR
  have hmark : -(1 / ((n : ℝ) + 1)) ≤
      -(1 / ((m : ℝ) + 1)) := neg_le_neg hfrac
  constructor
  · apply measure_mono
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    exact ⟨ht, hz.trans hmark⟩
  · apply measure_mono
    intro z hz
    exact hz.trans hmark
