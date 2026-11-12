-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb20_original_discounted_postpayment_random_clock_source_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:09:09.745023+00:00
-- url     : https://prove2.me/submissions/c26b4de0-c585-4659-a879-eae8921d15bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_discounted_increment_decomposition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Source-exact discounted post-payment reserve increment with the drift,
Gaussian and marked-jump channels and the full right-limit cash correction. -/
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
      (∀ (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
          (α β : Ω → ℝ≥0) (ω : Ω),
        Real.exp (-(q * (β ω : ℝ))) *
          (x + X.X (β ω) ω - rightLimit D (β ω) ω) -
        Real.exp (-(q * (α ω : ℝ))) *
          (x + X.X (α ω) ω - rightLimit D (α ω) ω) =
        Real.exp (-(q * (β ω : ℝ))) *
          (((β ω : ℝ) - (α ω : ℝ)) * X.c +
            (M (β ω) ω - M (α ω) ω) +
            (Jsmall (β ω) ω - Jsmall (α ω) ω) +
            (avram_p4_h_gaussian_intrinsic_large_jump_sum X (β ω) ω -
              avram_p4_h_gaussian_intrinsic_large_jump_sum X (α ω) ω) -
            (rightLimit D (β ω) ω - rightLimit D (α ω) ω)) +
        (Real.exp (-(q * (β ω : ℝ))) - Real.exp (-(q * (α ω : ℝ)))) *
          (x + X.X (α ω) ω - rightLimit D (α ω) ω)) := by
  classical
  obtain ⟨M, hpath, hMeq, hinc, _⟩ :=
    avram_jb20_original_physical_random_clock_increment_split
      X R Jsmall hRsource hJsource
  refine ⟨M, hpath, hMeq, ?_⟩
  intro x q D α β ω
  calc
    _ = Real.exp (-(q * (β ω : ℝ))) *
          ((X.X (β ω) ω - X.X (α ω) ω) -
            (rightLimit D (β ω) ω - rightLimit D (α ω) ω)) +
        (Real.exp (-(q * (β ω : ℝ))) - Real.exp (-(q * (α ω : ℝ)))) *
          (x + X.X (α ω) ω - rightLimit D (α ω) ω) :=
      postPaymentReserve_discounted_increment_decomposition
        X x q D ω (α ω) (β ω)
    _ = _ := by rw [hinc α β ω]
