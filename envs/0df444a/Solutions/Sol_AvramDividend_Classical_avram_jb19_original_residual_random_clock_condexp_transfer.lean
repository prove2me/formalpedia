-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb19_original_residual_random_clock_condexp_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:54:02.794726+00:00
-- url     : https://prove2.me/submissions/234faa1d-0d7e-4eca-b9e8-3a7917f096db

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb19_original_gaussian_residual_totalise_source_path
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Preserve exact original Gaussian residual equality at arbitrary random
clocks, including stopped integrability and conditional expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
        atTop (nhds (Jsmall t ω))) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ t ω, X.X t ω =
        (t : ℝ) * X.c + M t ω + Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω) ∧
      (∀ σ : Ω → ℝ≥0,
        (fun ω => M (σ ω) ω) =ᵐ[P] (fun ω => R (σ ω) ω) ∧
        (Integrable (fun ω => R (σ ω) ω) P →
          Integrable (fun ω => M (σ ω) ω) P) ∧
        condExp (𝓕.rightCont 0) P (fun ω => M (σ ω) ω) =ᵐ[P]
          condExp (𝓕.rightCont 0) P (fun ω => R (σ ω) ω)) := by
  classical
  obtain ⟨M, hpath, hMeq⟩ :=
    avram_jb19_original_gaussian_residual_totalise_source_path
      X R Jsmall hRsource hJsource
  refine ⟨M, hpath, hMeq, ?_⟩
  intro σ
  have hstop :
      (fun ω => M (σ ω) ω) =ᵐ[P]
        (fun ω => R (σ ω) ω) := by
    filter_upwards [hMeq] with ω hω
    exact hω (σ ω)
  refine ⟨hstop, ?_, ?_⟩
  · intro hRI
    exact hRI.congr hstop.symm
  · exact condExp_congr_ae hstop
