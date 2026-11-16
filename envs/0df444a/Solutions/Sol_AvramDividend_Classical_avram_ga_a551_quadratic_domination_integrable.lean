-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a551_quadratic_domination_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:55:14.670215+00:00
-- url     : https://prove2.me/submissions/26648d77-0344-4ae0-a2f3-2588edd4e055

import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (f z : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : AEStronglyMeasurable f P)
    (hz2 : Integrable (fun ω => (z ω)^2) P)
    (hconst : Integrable (fun _ : Ω => K) P)
    (hbound : ∀ᵐ ω ∂P, |f ω| ≤ K * (1 + (z ω)^2)) :
    Integrable f P := by
  have hdom : Integrable (fun ω => K + K * (z ω)^2) P :=
    hconst.add (hz2.const_mul K)
  apply hdom.mono' hf
  filter_upwards [hbound] with ω hω
  have hn : 0 ≤ K + K * (z ω)^2 := by
    exact add_nonneg hK (mul_nonneg hK (sq_nonneg _))
  simpa [Real.norm_eq_abs, abs_of_nonneg hn, mul_add] using hω
