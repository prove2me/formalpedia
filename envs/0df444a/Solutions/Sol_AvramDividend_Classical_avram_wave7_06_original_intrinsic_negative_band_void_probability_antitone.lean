-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_probability_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:34:04.405535+00:00
-- url     : https://prove2.me/submissions/7513b22b-04bc-43ea-99bd-2839402490ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original-source negative-band void probabilities decrease as the cutoff index increases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     P {ω : Ω | NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((m : ℝ) + 1)))) = 0} ≤
       P {ω : Ω | NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change P {ω : Ω | NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((m : ℝ) + 1)))) = 0} ≤
    P {ω : Ω | NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}
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
  apply measure_mono
  intro ω hZero
  apply le_antisymm
  · calc
      NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≤
          NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((m : ℝ) + 1)))) := by
        apply measure_mono
        rintro ⟨t, z⟩ ⟨ht, hz⟩
        exact ⟨ht, hz.trans hmark⟩
      _ = 0 := hZero
  · exact bot_le
