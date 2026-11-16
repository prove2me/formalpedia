-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_integrated_nat_pgf_quadratic_upper_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:14:00.54087+00:00
-- url     : https://prove2.me/submissions/23ab974a-bd65-4787-899a-c6f74a4ab059

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_a25_nat_pgf_quadratic_factorial_upper_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- Integrating the second-order factorial PGF Taylor bound. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hZ : Integrable (fun ω => z ^ (K ω)) P)
    (hPoly : Integrable (fun ω => (1 : ℝ) - (1 - z) * (K ω : ℝ) +
      (1 - z) ^ 2 * (K ω : ℝ) * ((K ω : ℝ) - 1) / 2) P) :
    (∫ ω, z ^ (K ω) ∂P) ≤
      (∫ ω, (1 : ℝ) - (1 - z) * (K ω : ℝ) +
        (1 - z) ^ 2 * (K ω : ℝ) * ((K ω : ℝ) - 1) / 2 ∂P) := by
  exact integral_mono hZ hPoly (fun ω =>
    AvramDividend.Classical.avram_a25_nat_pgf_quadratic_factorial_upper_20261115
      z hz0 hz1 (K ω))
