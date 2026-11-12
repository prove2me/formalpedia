-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18t_original_J_physical_jump_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:56:51.592763+00:00
-- url     : https://prove2.me/submissions/c3af032d-6d94-4d0f-921a-14651b501360

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Same-space physical identity of the compensated jump remainder. -/
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
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω - (t : ℝ) * (∫ η, X.X 1 η ∂P) - R t ω =
        Jsmall t ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        (t : ℝ) * (X.c - (∫ η, X.X 1 η ∂P)) := by
  filter_upwards [hRsource, hJsource] with ω hRω hJω
  intro t
  let S : ℕ → ℝ := fun k =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω
  let L : ℝ := avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω
  let A : ℝ := X.X t ω - (t : ℝ) * X.c - L
  have hEqCut : (fun k : ℕ => A - S k) =
      (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω) := by
    funext k
    change X.X t ω - (t : ℝ) * X.c -
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω =
      X.X t ω - (t : ℝ) * X.c -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω -
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω
    ring
  have hR : Tendsto (fun k : ℕ => A - S k)
      atTop (nhds (R t ω)) := by
    rw [hEqCut]
    exact hRω t
  have hA : Tendsto (fun _ : ℕ => A) atTop (nhds A) :=
    tendsto_const_nhds
  have hAS : Tendsto (fun k : ℕ => A - S k)
      atTop (nhds (A - Jsmall t ω)) :=
    hA.sub (hJω t)
  have hEq : R t ω = A - Jsmall t ω :=
    (tendsto_nhds_unique hR hAS)
  dsimp [A, L] at hEq
  rw [hEq]
  ring
