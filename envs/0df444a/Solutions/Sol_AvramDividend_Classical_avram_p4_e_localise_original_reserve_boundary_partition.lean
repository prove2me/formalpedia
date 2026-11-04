-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_reserve_boundary_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:50:05.040657+00:00
-- url     : https://prove2.me/submissions/ea7c9e0c-da2b-43ad-a863-671f25695070

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The actual controlled state can touch either boundary; those cases remain explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    riskProcess X x D t ω < 0 ∨
    riskProcess X x D t ω = 0 ∨
    (0 < riskProcess X x D t ω ∧
      ENNReal.ofReal (riskProcess X x D t ω) < C) ∨
    (0 < riskProcess X x D t ω ∧
      ENNReal.ofReal (riskProcess X x D t ω) = C) := by
  rcases lt_trichotomy (riskProcess X x D t ω) 0 with hneg | hzero | hpos
  · exact Or.inl hneg
  · exact Or.inr (Or.inl hzero)
  · have hcap := hD.2 ω t ht
    rcases lt_or_eq_of_le hcap with hinside | heq
    · exact Or.inr (Or.inr (Or.inl ⟨hpos, hinside⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hpos, heq⟩))
