-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb29_original_constant_pre_right_reserve_stieltjes_exact_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:55:23.723605+00:00
-- url     : https://prove2.me/submissions/06f73bd7-2af6-4b8a-9f51-0f2c5c2d28b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b) (k : ℝ)
    (ha : riskProcess X x D a ω = k)
    (hb : riskProcess X x D b ω = k)
    (hAtomA : rightLimit D a ω = D a ω)
    (hAtomB : rightLimit D b ω = D b ω)
    (hLine : X.X b ω - X.X a ω =
      X.drift * ((b : ℝ) - (a : ℝ))) :
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (X.drift * ((b : ℝ) - (a : ℝ)))  := by
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hIncrement : D b ω - D a ω =
      X.X b ω - X.X a ω := by
    unfold riskProcess at ha hb
    linarith
  rw [dividendMeasure_Ioc_rightLimit D hStrat ω a b,
      hAtomB, hAtomA, hIncrement, hLine]
