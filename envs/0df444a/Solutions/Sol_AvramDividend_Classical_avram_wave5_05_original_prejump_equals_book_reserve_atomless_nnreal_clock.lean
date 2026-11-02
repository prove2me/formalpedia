-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:23:22.735363+00:00
-- url     : https://prove2.me/submissions/b888a1c9-0274-4f49-b0bb-2fe7c24e3979

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_atomless_continuity
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightJump_support_countable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
NNReal-time original predictable/current reserve identification is needed to
evaluate an Ito generator at its true pre-jump argument. The two exceptional
jump supports are countable, so every atomless physical-time clock ignores them.
-/

/-- Chronological pre-event U⁻ equals genuine prepayment U for atomless clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ν : Measure ℝ≥0) [NullSingletonClass ν] :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂ν, 0 < t →
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
        riskProcess X x D t ω := by
  have hPost :=
    avram_wave4_p2_original_postpayment_reserve_atomless_continuity
      X x D hD ν
  filter_upwards [hPost] with ω hωPost
  have hCountReal :=
    dividendStrategy_rightJump_support_countable D hD ω
  have hCountNN : Set.Countable
      {t : ℝ≥0 | rightLimit D t ω ≠ D t ω} := by
    have hPre : Set.Countable
        ((fun t : ℝ≥0 => (t : ℝ)) ⁻¹'
          {s : ℝ | 0 ≤ s ∧
            rightLimit D s.toNNReal ω ≠ D s.toNNReal ω}) :=
      hCountReal.preimage (fun a b hab => NNReal.coe_injective hab)
    simpa using hPre
  have hωRight : ∀ᵐ t ∂ν, rightLimit D t ω = D t ω := by
    apply ae_iff.mpr
    simpa using (hCountNN.measure_zero ν)
  filter_upwards [hωPost, hωRight] with t hPostAt hRightAt
  intro ht
  calc
    Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      x + X.X t ω - rightLimit D t ω := (hPostAt ht).symm
    _ = riskProcess X x D t ω := by
      rw [hRightAt]
      rfl
