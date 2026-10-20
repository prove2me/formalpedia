-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_mono_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:36:53.359694+00:00
-- url     : https://prove2.me/submissions/836811c1-bc4b-48c5-a5cf-cd721806e80c

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier

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
    (a b q : ℝ) (hab : a ≤ b) :
    barrierSupValue X a q ≤ barrierSupValue X b q := by
  unfold barrierSupValue
  apply lintegral_mono
  intro ω
  apply lintegral_mono_set
  intro t ht
  change 0 ≤ t ∧ (t = 0 ∨
      ENNReal.ofReal t < barrierRuinTime X b ω)
  change 0 ≤ t ∧ (t = 0 ∨
      ENNReal.ofReal t < barrierRuinTime X a ω) at ht
  refine ⟨ht.1, ?_⟩
  rcases ht.2 with h0 | hBefore
  · exact Or.inl h0
  · exact Or.inr
      (lt_of_lt_of_le hBefore
        (barrierRuinTime_mono_barrier X a b hab ω))
