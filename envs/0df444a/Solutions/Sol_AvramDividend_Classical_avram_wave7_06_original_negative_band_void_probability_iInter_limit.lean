-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_void_probability_iInter_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:47:48.896549+00:00
-- url     : https://prove2.me/submissions/6db07444-915b-4071-8642-48d78d4b176b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_and_levy_intensity_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-band void probabilities converge from above under explicit measurability and finiteness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     let E : ℕ → Set Ω := fun k =>
       {ω : Ω | NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1)))) = 0}
     (∀ k, NullMeasurableSet (E k) P) →
     (∃ k, P (E k) ≠ ⊤) →
     P (⋂ k, E k) = ⨅ k, P (E k)) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let E : ℕ → Set Ω := fun k =>
    {ω : Ω | NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1)))) = 0}
  change (∀ k, NullMeasurableSet (E k) P) →
    (∃ k, P (E k) ≠ ⊤) →
    P (⋂ k, E k) = ⨅ k, P (E k)
  intro hNull hFinite
  have hAnti : Antitone E := by
    intro n m hnm
    intro ω hZero
    have hCount :
        NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≤
          NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((m : ℝ) + 1)))) :=
      (avram_wave7_06_original_intrinsic_negative_band_and_levy_intensity_monotone
        X ω T n m hnm).1
    change NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((m : ℝ) + 1)))) = 0 at hZero
    have hLe :
        NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≤ 0 := by
      calc
        _ ≤ NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((m : ℝ) + 1)))) := hCount
        _ = 0 := hZero
    exact le_antisymm hLe bot_le
  exact hAnti.measure_iInter hNull hFinite
