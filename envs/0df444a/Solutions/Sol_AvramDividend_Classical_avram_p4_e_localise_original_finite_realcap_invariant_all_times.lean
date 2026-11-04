-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_finite_realcap_invariant_all_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:13:20.716567+00:00
-- url     : https://prove2.me/submissions/25ca6e60-f3a1-4ddd-8916-085ff1692f44

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The original reserve respects the real cap at zero and at every positive time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D) :
    ∀ ω (s : ℝ≥0), riskProcess X x D s ω ≤ c := by
  intro ω s
  by_cases hs0 : s = 0
  · subst s
    have hX0 := X.X_zero ω
    have hD0 := hD.1.1.1 ω
    have hxle : x ≤ c := (ENNReal.ofReal_le_ofReal_iff hc).mp hxc
    simpa [riskProcess, hX0, hD0] using hxle
  · have hspos : 0 < s :=
      lt_of_le_of_ne (show (0 : ℝ≥0) ≤ s from zero_le) (Ne.symm hs0)
    exact (ENNReal.ofReal_le_ofReal_iff hc).mp (hD.2 ω s hspos)
