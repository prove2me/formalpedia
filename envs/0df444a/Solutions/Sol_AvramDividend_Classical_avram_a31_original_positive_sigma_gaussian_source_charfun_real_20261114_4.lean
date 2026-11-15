-- Prove2me | solution 4 for AvramDividend.Classical.avram_a31_original_positive_sigma_gaussian_source_charfun_real_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:39:02.019332+00:00
-- url     : https://prove2.me/submissions/0d382bf1-cd61-4cb9-b424-961e115323e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a34_original_gaussian_intrinsic_zero_time_charfun_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a44_original_zero_nu_positive_sigma_gaussian_physical_marginal_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a47_original_positive_sigma_nonzero_jump_positive_time_fourier_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ (t : ℝ≥0) (u : ℝ),
      charFun (P.map (G t)) u =
        charFun (gaussianReal 0
          (NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) u := by
  intro t u
  by_cases ht : 0 < t
  · by_cases hν : X.ν = 0
    · have hMap := avram_a44_original_zero_nu_positive_sigma_gaussian_physical_marginal_20261114
        X hν hPositive R hR t
      have hGR : G t =ᵐ[P] R t := by
        filter_upwards [hEq] with ω hω
        exact hω t
      have hMap' : P.map (G t) =
          gaussianReal 0 ((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * t) := by
        rw [Measure.map_congr hGR]
        exact hMap
      have hv : (NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * t =
          NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)) := by
        apply Subtype.ext
        change X.σ ^ 2 * (t : ℝ) = (t : ℝ) * X.σ ^ 2
        ring
      rw [hMap', hv]
    · exact avram_a47_original_positive_sigma_nonzero_jump_positive_time_fourier_20261114
        X hX hFinite hPositive hν R hR G hEq t ht u
  · have ht0 : t = 0 := le_antisymm (le_of_not_gt ht) zero_le
    subst t
    simpa using
      (avram_a34_original_gaussian_intrinsic_zero_time_charfun_20261114
        X R hR G hEq u)
