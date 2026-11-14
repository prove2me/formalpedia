-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_uniform_ae_small_positive_error_integral_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:37:14.761665+00:00
-- url     : https://prove2.me/submissions/73e74ee7-c7c7-4a4c-8e60-0d386aca7392

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Err : ℕ → Ω → ℝ)
    (hErrI : ∀ m, Integrable (Err m) P)
    (hErrPos : ∀ m, ∀ᵐ ω ∂P, 0 ≤ Err m ω)
    (hSmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ∀ᵐ ω ∂P, Err m ω ≤ ε) :
    Tendsto (fun m => ∫ ω, Err m ω ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun m =>
      lt_of_lt_of_le ha (integral_nonneg_of_ae (hErrPos m)))
  · intro b hb
    have hb2 : 0 < b / 2 := by linarith
    filter_upwards [hSmall (b / 2) hb2] with m hm
    calc
      (∫ ω, Err m ω ∂P) ≤
        (∫ _ : Ω, b / 2 ∂P) :=
        integral_mono_ae (hErrI m) (integrable_const _) hm
      _ = b / 2 := by simp
      _ < b := by linarith
