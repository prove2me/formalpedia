-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_integrable_of_lintegral_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:36:32.894037+00:00
-- url     : https://prove2.me/submissions/98e8984a-fb0b-492a-bfac-3b86d164520c

import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Finite ENNReal nonnegative power moment implies its real Bochner integrability. -/
theorem solution
    (μ : Measure ℝ) (hpositive : ∀ᵐ z ∂μ, 0 ≤ z)
    (k : ℕ)
    (hfinite : (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤) :
    Integrable (fun z : ℝ => z ^ k) μ := by
  have hmeas : AEStronglyMeasurable (fun z : ℝ => z ^ k) μ := by
    fun_prop
  have hnonneg : ∀ᵐ z ∂μ, 0 ≤ z ^ k :=
    hpositive.mono (fun z hz => pow_nonneg hz k)
  have hpow : ∀ᵐ z ∂μ,
      ENNReal.ofReal (z ^ k) = (ENNReal.ofReal z) ^ k := by
    filter_upwards [hpositive] with z hz
    exact ENNReal.ofReal_pow hz k
  have hEq :
      (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂μ) =
        (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) :=
    lintegral_congr_ae hpow
  apply (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp
  rw [hEq]
  exact hfinite
