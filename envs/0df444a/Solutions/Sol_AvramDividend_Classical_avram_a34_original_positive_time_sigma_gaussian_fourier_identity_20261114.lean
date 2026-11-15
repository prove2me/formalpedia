-- Prove2me | solution 1 for AvramDividend.Classical.avram_a34_original_positive_time_sigma_gaussian_fourier_identity_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:35:42.915326+00:00
-- url     : https://prove2.me/submissions/79b4f322-153b-4ea4-b19c-e3e3074bb94e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
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
    ∀ (t : ℝ≥0) (ht : 0 < t) (u : ℝ),
      charFun (P.map (G t)) u =
        charFun (gaussianReal 0
          (NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) u := by
  intro t ht u
  by_cases hNu : X.ν = 0
  · have hMarginal :=
      avram_a44_original_zero_nu_positive_sigma_gaussian_physical_marginal_20261114
        X hNu hPositive R hR t
    have hPath : (G t) =ᵐ[P] (R t) := by
      filter_upwards [hEq] with ω hω
      exact hω t
    have hVariance :
        (NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * t =
          NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)) := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_mul, NNReal.coe_mk]
      ring
    calc
      charFun (P.map (G t)) u =
          charFun (P.map (R t)) u := by
            rw [Measure.map_congr hPath]
      _ = charFun (gaussianReal 0
            ((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * t)) u := by
          rw [hMarginal]
      _ = charFun (gaussianReal 0
            (NNReal.mk ((t : ℝ) * X.σ ^ 2)
              (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) u := by
          rw [hVariance]
  · exact
      avram_a47_original_positive_sigma_nonzero_jump_positive_time_fourier_20261114
        X hX hFinite hPositive hNu R hR G hEq t ht u
