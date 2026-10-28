-- Prove2me | solution 1 for BidPriceControl.Asymptotic.gallego_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:53:06.068092+00:00
-- url     : https://prove2.me/submissions/55e5231c-ff6c-4650-afa7-793bd4b32f27

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

open MeasureTheory ProbabilityTheory

open BidPriceControl.Asymptotic in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : MemLp Z 2 P) (z : ℝ) :
    ∫ ω, max (Z ω - z) 0 ∂P ≤
      (Real.sqrt (variance Z P + (z - ∫ ω, Z ω ∂P) ^ 2) - (z - ∫ ω, Z ω ∂P)) / 2 := by
  have hY : MemLp (fun ω => Z ω - z) 2 P := hZ.sub (memLp_const z)
  have hA : MemLp (fun ω => |Z ω - z|) 2 P := by
    have := hY.norm
    simpa [Real.norm_eq_abs] using this
  have hZi : Integrable Z P := hZ.integrable one_le_two
  have hYi : Integrable (fun ω => Z ω - z) P := hY.integrable one_le_two
  have hAi : Integrable (fun ω => |Z ω - z|) P := hA.integrable one_le_two
  have hEY : ∫ ω, (Z ω - z) ∂P = (∫ ω, Z ω ∂P) - z := by
    rw [integral_sub hZi (integrable_const z)]
    simp
  have hVY : variance (fun ω => Z ω - z) P = variance Z P :=
    variance_sub_const hZ.aestronglyMeasurable z
  have h1 := variance_eq_sub hY
  have h2 := variance_eq_sub hA
  have h3 := variance_nonneg (fun ω => |Z ω - z|) P
  simp only [Pi.pow_apply, sq_abs] at h1 h2
  have hEA0 : 0 ≤ ∫ ω, |Z ω - z| ∂P := integral_nonneg (fun ω => abs_nonneg _)
  have hsq : (∫ ω, |Z ω - z| ∂P) ^ 2 ≤ variance Z P + (z - ∫ ω, Z ω ∂P) ^ 2 := by
    rw [hEY] at h1
    nlinarith
  have hEA : ∫ ω, |Z ω - z| ∂P ≤ Real.sqrt (variance Z P + (z - ∫ ω, Z ω ∂P) ^ 2) :=
    le_trans (le_abs_self _) (Real.abs_le_sqrt hsq)
  have hp : ∀ a : ℝ, max a 0 = (a + |a|) / 2 := by
    intro a
    rcases le_total a 0 with h | h
    · rw [max_eq_right h, abs_of_nonpos h]; ring
    · rw [max_eq_left h, abs_of_nonneg h]; ring
  simp_rw [hp]
  rw [integral_div, integral_add hYi hAi, hEY]
  linarith
