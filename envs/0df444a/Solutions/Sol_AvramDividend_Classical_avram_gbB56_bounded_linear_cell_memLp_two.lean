-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB56_bounded_linear_cell_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:27:29.114418+00:00
-- url     : https://prove2.me/submissions/9936192b-981f-451c-b8d6-9f2e63b2b730

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- Uniform coefficient bounds preserve the square-integrability of
an original real-valued noise increment. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F Z : Ω → ℝ) (K : ℝ)
    (hF : Measurable F) (hZ : Measurable Z)
    (hK : 0 ≤ K) (hFb : ∀ ω, |F ω| ≤ K)
    (hZ2 : Integrable (fun ω => Z ω ^ 2) μ) :
    MemLp (fun ω => F ω * Z ω) 2 μ := by
  have hMeas : Measurable (fun ω => F ω * Z ω) := hF.mul hZ
  have hBound (ω : Ω) :
      (F ω * Z ω) ^ 2 ≤ K ^ 2 * Z ω ^ 2 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hFb ω)
    have hFSq : F ω ^ 2 ≤ K ^ 2 := by nlinarith
    calc
      (F ω * Z ω) ^ 2 = F ω ^ 2 * Z ω ^ 2 := by ring
      _ ≤ K ^ 2 * Z ω ^ 2 :=
        mul_le_mul_of_nonneg_right hFSq (sq_nonneg _)
  have hDom : Integrable (fun ω => K ^ 2 * Z ω ^ 2) μ :=
    hZ2.const_mul (K ^ 2)
  have hSq : Integrable (fun ω => (F ω * Z ω) ^ 2) μ := by
    apply hDom.mono' (hMeas.pow_const 2).aestronglyMeasurable
    filter_upwards [] with ω
    have hn : 0 ≤ K ^ 2 * Z ω ^ 2 := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (F ω * Z ω)),
      abs_of_nonneg hn] using hBound ω
  apply (memLp_two_iff_integrable_sq_norm hMeas.aestronglyMeasurable).2
  simpa only [Real.norm_eq_abs, sq_abs] using hSq
