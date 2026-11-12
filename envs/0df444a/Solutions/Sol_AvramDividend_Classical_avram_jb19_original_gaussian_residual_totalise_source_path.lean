-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb19_original_gaussian_residual_totalise_source_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:06:46.966497+00:00
-- url     : https://prove2.me/submissions/38c7aef1-2ece-479a-893d-28f03e98db1d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18t_original_J_physical_jump_decomposition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Totalise the source residual on a null exceptional set while preserving its
simultaneous almost-sure values at every original nonnegative time. -/
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
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω) := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω
  refine ⟨M, ?_, ?_⟩
  · intro t ω
    dsimp [M]
    ring
  · have hdecomp :=
      avram_ja18t_original_J_physical_jump_decomposition
        X R Jsmall hRsource hJsource
    filter_upwards [hdecomp] with ω hω
    intro t
    dsimp [M]
    have ht := hω t
    linear_combination ht
