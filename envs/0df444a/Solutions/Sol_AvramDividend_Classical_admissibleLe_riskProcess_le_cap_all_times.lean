-- Prove2me | solution 1 for AvramDividend.Classical.admissibleLe_riskProcess_le_cap_all_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:31:17.233886+00:00
-- url     : https://prove2.me/submissions/cc8a7bd9-89f5-48a9-aead-5fb88e27a9b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (t : ℝ≥0) :
    ENNReal.ofReal (riskProcess X x D t ω) ≤ C := by
  by_cases h0 : t = 0
  · subst t
    have hU0 : riskProcess X x D 0 ω = x := by
      unfold riskProcess
      rw [X.X_zero ω, hD.1.1.1 ω]
      ring
    simpa only [hU0] using hxC
  · have ht : 0 < t := lt_of_le_of_ne (bot_le : (0 : ℝ≥0) ≤ t) (Ne.symm h0)
    exact hD.2 ω t ht
