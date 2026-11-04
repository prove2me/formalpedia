-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_rate_free_direct_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:21:23.625547+00:00
-- url     : https://prove2.me/submissions/157b1f4b-992a-443d-9e86-a314c3856af9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_finite_mean_condexp_independent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The finite-mean original intrinsic marked jump-count increment
centred by its own unconditional mean has zero conditional expectation given
its true past filtration, independent of any original Levy ν-rate identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hMeanFinite :  (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) < ⊤) :
    (condExp (𝓕 s) P (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
        ((∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P)).toReal)) =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
  let c : ℝ := (∫⁻ ω, N ω ∂P).toReal
  have hMeas : Measurable N :=
    avram_p2_e_compensator_intrinsic_rectangle_count_measurable
      X s t hst B hB
  have hInt : Integrable (fun ω => (N ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hMeas.aemeasurable
      (ne_of_lt hMeanFinite)
  have hCount :=
    avram_p2_e_compensator_original_finite_mean_condexp_independent
      X s t hst B hB hMeanFinite
  have hConst :
      (condExp (𝓕 s) P (fun _ : Ω => c)) = (fun _ : Ω => c) :=
    condExp_const (𝓕.le s) c
  have hSub := condExp_sub hInt (integrable_const c) (𝓕 s)
  refine hSub.trans ?_
  filter_upwards [hCount] with ω hω
  change (condExp (𝓕 s) P (fun ω => (N ω).toReal)) ω = c at hω
  simpa only [hConst, Pi.sub_apply, Pi.zero_apply, sub_self]
    using congrArg (fun z : ℝ => z - c) hω
