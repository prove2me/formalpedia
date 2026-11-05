-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_g_localise_original_finite_cap_contact_real_prestate_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:45:18.032784+00:00
-- url     : https://prove2.me/submissions/c8d1d126-cfa0-430f-9639-a670996218cb

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- For a finite cap, contact of the actual nonnegative original
pre-reserve is exactly equality with its real-valued cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (p : ℝ≥0 × Ω)
    (hZ : 0 ≤ Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) :
    ENNReal.ofReal (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) = C ↔
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 =
      C.toReal := by
  let z : ℝ := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  change ENNReal.ofReal z = C ↔ z = C.toReal
  constructor
  · intro h
    have hzNonneg : 0 ≤ z := hZ
    have hReal := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal hzNonneg] at hReal
    exact hReal
  · intro hz
    rw [hz]
    exact ENNReal.ofReal_toReal hC
