-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_finite_rate_direct_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:21:18.163253+00:00
-- url     : https://prove2.me/submissions/43e3e236-0fef-4c35-91bd-7983fe44dce2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_count_condexp_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original finite-rate compensated intrinsic marked count has zero
conditional expectation given the true original past filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (condExp (𝓕 s) P (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let c : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
  have hInt : Integrable (fun ω => (N ω).toReal) P :=
    avram_p2_e_compensator_finite_nu_count_real_integrable
      X s t hst B hB hν hRate
  have hCount :=
    avram_p2_e_compensator_original_count_condexp_rate
      X s t hst B hB hν hRate
  have hConst :
      (condExp (𝓕 s) P (fun _ : Ω => c)) = (fun _ : Ω => c) :=
    condExp_const (𝓕.le s) c
  have hSub :=
    condExp_sub hInt (integrable_const c) (𝓕 s)
  refine hSub.trans ?_
  filter_upwards [hCount] with ω hω
  change (condExp (𝓕 s) P (fun ω => (N ω).toReal)) ω = c at hω
  simpa only [hConst, Pi.sub_apply, Pi.zero_apply, sub_self]
    using congrArg (fun z : ℝ => z - c) hω
