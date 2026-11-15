-- Prove2me | solution 6 for AvramDividend.Classical.avram_mix_fin16_gaussian_residual_original_bracket_l2_public
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:23:11.370674+00:00
-- url     : https://prove2.me/submissions/dfbb8298-f4b8-4206-9674-395a0c8180e6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_limit_gaussian_zero_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_limit_gaussian_positive_time_square_moment_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

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
    (hRadapt : ∀ t : ℝ≥0,
      AEStronglyMeasurable[𝓕.rightCont t] (R t) P) :
    ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 := by
  intro t
  by_cases ht0 : t = 0
  · subst t
    have hZero :=
      avram_a21_original_limit_gaussian_zero_time_square_moment_20261113
        X hX hFinite R hRsource
    simpa using hZero
  · have ht : 0 < t := lt_of_le_of_ne
      (by positivity : 0 ≤ t) (Ne.symm ht0)
    exact
      avram_a21_original_limit_gaussian_positive_time_square_moment_20261113
        X hX hFinite R hRsource t ht
