-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_original_gaussian_increment_independent_centered_L1_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:29:01.77082+00:00
-- url     : https://prove2.me/submissions/226ba02b-c285-4135-b29b-d36a897a28ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a23_gaussian_limit_increment_original_past_independent_rep_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original Gaussian limit increment has an integrable, centred, future-independent representative. -/
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
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ D : Ω → ℝ,
      Measurable D ∧
      ProbabilityTheory.Indep (MeasurableSpace.comap D inferInstance)
        (𝓕.rightCont s) P ∧
      Integrable D P ∧
      (∫ ω, D ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, D ω = R t ω - R s ω) := by
  obtain ⟨D, hMeas, hIndep, hEq⟩ :=
    avram_a23_gaussian_limit_increment_original_past_independent_rep_20261113
      X hX hFinite R hR s t hst
  have hMom :=
    avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
      X hX hFinite R hR
  have hDiff : Integrable (fun ω => R t ω - R s ω) P :=
    (hMom t).1.sub (hMom s).1
  have hEqSymm : (fun ω => R t ω - R s ω) =ᵐ[P] D := by
    filter_upwards [hEq] with ω hω
    exact hω.symm
  have hD : Integrable D P := hDiff.congr hEqSymm
  have hMean : (∫ ω, D ω ∂P) = 0 := by
    calc
      (∫ ω, D ω ∂P) = (∫ ω, R t ω - R s ω ∂P) :=
        integral_congr_ae hEq
      _ = (∫ ω, R t ω ∂P) - (∫ ω, R s ω ∂P) :=
        integral_sub (hMom t).1 (hMom s).1
      _ = 0 := by rw [(hMom t).2, (hMom s).2, sub_self]
  exact ⟨D, hMeas, hIndep, hD, hMean, hEq⟩
