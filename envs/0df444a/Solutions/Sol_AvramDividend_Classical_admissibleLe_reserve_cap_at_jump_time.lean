-- Prove2me | solution 1 for AvramDividend.Classical.admissibleLe_reserve_cap_at_jump_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:02:09.227079+00:00
-- url     : https://prove2.me/submissions/0fe89176-2e16-4c1b-a55c-78602bbec750

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    ENNReal.ofReal (riskProcess X x D t ω) ≤ C := by
  by_cases ht0 : t = 0
  · subst t
    have hrisk0 : riskProcess X x D 0 ω = x := by
      unfold riskProcess
      rw [X.X_zero ω, hD.1.1.1 ω]
      ring
    rw [hrisk0]
    exact hxc
  · exact hD.2 ω t (pos_iff_ne_zero.mpr ht0)
