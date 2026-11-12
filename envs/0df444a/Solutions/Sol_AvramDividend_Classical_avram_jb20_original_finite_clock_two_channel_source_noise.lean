-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb20_original_finite_clock_two_channel_source_noise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:31:43.097875+00:00
-- url     : https://prove2.me/submissions/cdd7a23d-34e7-4216-94b4-c10c57d15e72

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_finite_range_stop_condexp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- At each original finite-range random clock the two physical noise
channels are integrable, initially centred and split from the source X. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτbound : ∀ ω, τ ω ≤ T)
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (hJI : Integrable (fun ω => Jsmall (τ ω) ω) P)
    (hJcenter : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P
        (fun ω => Jsmall (τ ω) ω) ω = 0) :
    ∃ MG MJ : Ω → ℝ,
      Integrable MG P ∧ Integrable MJ P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MG ω = 0) ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MJ ω = 0) ∧
      (∀ᵐ ω ∂P,
        X.X (τ ω) ω =
          (τ ω : ℝ) * X.c + MG ω + MJ ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω) := by
  obtain ⟨hRI, hRcenter⟩ :=
    avram_jb20_original_gaussian_finite_range_stop_condexp
      X R hRsource hRint hRmart τ hτstop T hτbound S hτrange
  obtain ⟨M, hpath, hMeq, _, _⟩ :=
    avram_jb20_original_physical_random_clock_increment_split
      X R Jsmall hRsource hJsource
  refine ⟨(fun ω => R (τ ω) ω), (fun ω => Jsmall (τ ω) ω),
    hRI, hJI, hRcenter, hJcenter, ?_⟩
  filter_upwards [hMeq] with ω hEq
  calc
    X.X (τ ω) ω =
        (τ ω : ℝ) * X.c + M (τ ω) ω +
          Jsmall (τ ω) ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω :=
      hpath (τ ω) ω
    _ = _ := by rw [hEq (τ ω)]
