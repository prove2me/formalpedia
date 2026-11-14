-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_uniform_gaussian_independent_centered_L1_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:44:18.369229+00:00
-- url     : https://prove2.me/submissions/07f69e7c-450d-488c-b73b-7952220d66ac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_gaussian_limit_original_past_independent_rep_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- One coherent original-source Gaussian increment family is independent, integrable and centred at all deterministic times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
        atTop (𝓝 (R u ω)))
    (T : ℝ≥0) :
    ∃ D : ℝ≥0 → Ω → ℝ,
      (∀ s, Measurable (D s)) ∧
      (∀ s, ProbabilityTheory.Indep
        (MeasurableSpace.comap (D s) inferInstance)
        (𝓕.rightCont s) P) ∧
      (∀ s, Integrable (D s) P ∧ (∫ ω, D s ω ∂P) = 0) ∧
      (∀ᵐ ω ∂P, ∀ s : ℝ≥0,
        D s ω = R (s + T) ω - R s ω) := by
  obtain ⟨D, hMeas, hIndep, hEq⟩ :=
    avram_a24_uniform_gaussian_limit_original_past_independent_rep_20261113
      X hX hFinite R hR T
  have hMom :=
    avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
      X hX hFinite R hR
  refine ⟨D, hMeas, hIndep, ?_, hEq⟩
  intro s
  have hDiff : Integrable (fun ω => R (s + T) ω - R s ω) P :=
    (hMom (s + T)).1.sub (hMom s).1
  have hE : (fun ω => R (s + T) ω - R s ω) =ᵐ[P] (D s) := by
    filter_upwards [hEq] with ω hω
    exact (hω s).symm
  have hD : Integrable (D s) P := hDiff.congr hE
  constructor
  · exact hD
  · calc
      (∫ ω, D s ω ∂P) =
        (∫ ω, R (s + T) ω - R s ω ∂P) :=
          integral_congr_ae hE.symm
      _ = (∫ ω, R (s + T) ω ∂P) - (∫ ω, R s ω ∂P) :=
          integral_sub (hMom (s + T)).1 (hMom s).1
      _ = 0 := by rw [(hMom (s + T)).2, (hMom s).2, sub_self]
