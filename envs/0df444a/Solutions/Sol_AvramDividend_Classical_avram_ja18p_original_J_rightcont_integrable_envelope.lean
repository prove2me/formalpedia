-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18p_original_J_rightcont_integrable_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:04:48.293636+00:00
-- url     : https://prove2.me/submissions/199f0d63-8001-475b-a0e2-4e3d830dac81

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18s_original_J_zero_origin
import Theorems.Thm_AvramDividend_Classical_avram_ja18t_original_J_physical_jump_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_ja18w_original_largejump_sum_rightcont
import Theorems.Thm_AvramDividend_Classical_avram_ja18x_original_J_integrable_horizon_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_smallband_physical_path_envelopes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original compensated-J right-continuity and L1 horizon domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (n : ℕ) (hn : 0 < n) :
    let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    let J : ℝ≥0 → Ω → ℝ :=
      fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
    ∃ B : Ω → ℝ, Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => J u ω) (Set.Ici t) t) ∧
      (∀ᵐ ω ∂P, J 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
        ‖J t ω‖ ≤ B ω) := by
  let μ : ℝ := ∫ ω, X.X 1 ω ∂P
  let J : ℝ≥0 → Ω → ℝ :=
    fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
  let L : ℝ≥0 → Ω → ℝ := fun t ω =>
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω
  let drift : ℝ := X.c - μ
  change ∃ B : Ω → ℝ, Integrable B P ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => J u ω) (Set.Ici t) t) ∧
    (∀ᵐ ω ∂P, J 0 ω = 0) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
      ‖J t ω‖ ≤ B ω)
  obtain ⟨B, hBInt, hDom⟩ :=
    avram_ja18x_original_J_integrable_horizon_majorant
      X hX hFinite R hRsource n hn
  refine ⟨B, hBInt, ?_, ?_, hDom⟩
  · obtain ⟨Jsmall, hJlim, hJright, _, _, _⟩ :=
      avram_ja18_original_smallband_physical_path_envelopes
        X hX hFinite
    have hPhysical :=
      avram_ja18t_original_J_physical_jump_decomposition
        X R Jsmall hRsource hJlim
    filter_upwards [hJright, hPhysical] with ω hRight hPhys
    intro t
    have hEq : (fun u : ℝ≥0 => J u ω) =
        (fun u => Jsmall u ω + L u ω + (u : ℝ) * drift) := by
      funext u
      exact hPhys u
    rw [hEq]
    have hLinear : Continuous (fun u : ℝ≥0 => (u : ℝ) * drift) := by
      fun_prop
    exact ((hRight t).add
      (avram_ja18w_original_largejump_sum_rightcont X ω t)).add
        hLinear.continuousWithinAt
  · have hZero := avram_ja18s_original_J_zero_origin X R hRsource
    filter_upwards [hZero] with ω hω
    simpa [J, μ] using hω
