-- Prove2me | solution 1 for AvramDividend.Classical.causal_exp_scaled_primitive_continuous_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:52:15.893976+00:00
-- url     : https://prove2.me/submissions/d0589cab-cda2-411b-939b-cac2c320897a

import Mathlib

open MeasureTheory Set

theorem solution
    (P : ℝ → ℝ) (a w : ℝ) (hw : 0 ≤ w)
    (hP : IntegrableOn P (Ioi (0 : ℝ)) volume) :
    ContinuousOn
      (fun x : ℝ => (Real.exp (-w * x) *
        (∫ s in Ioc (0 : ℝ) x,
          Real.exp (w * s) * P s ∂volume)) / a)
      (Ici (0 : ℝ)) := by
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := hx
  set f : ℝ → ℝ := fun s => Real.exp (w * s) * P s
  have hint : IntervalIntegrable f volume 0 (x + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    have hPI : IntegrableOn P (Ioc 0 (x + 1)) volume := hP.mono_set Ioc_subset_Ioi_self
    refine Integrable.bdd_mul (c := Real.exp (w * (x + 1))) hPI
      (by fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hw)
  have hmem : (0 : ℝ) ∈ uIcc 0 (x + 1) := left_mem_uIcc
  have hcont := intervalIntegral.continuousOn_primitive_interval' hint hmem
  have hU : uIcc (0 : ℝ) (x + 1) = Icc 0 (x + 1) := uIcc_of_le (by linarith)
  rw [hU] at hcont
  have hprim : ContinuousWithinAt (fun b => ∫ s in Ioc (0 : ℝ) b, f s ∂volume) (Icc 0 (x + 1)) x := by
    refine (hcont x ⟨hx0, by linarith⟩).congr (fun b hb => ?_) ?_
    · rw [intervalIntegral.integral_of_le hb.1]
    · rw [intervalIntegral.integral_of_le hx0]
  have hprim' : ContinuousWithinAt (fun b => ∫ s in Ioc (0 : ℝ) b, f s ∂volume) (Ici 0) x := by
    refine hprim.mono_of_mem_nhdsWithin ?_
    have : Iio (x + 1) ∈ nhds x := Iio_mem_nhds (by linarith)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds this] with b hb1 hb2
    exact ⟨hb1, le_of_lt hb2⟩
  exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousWithinAt).mul
    hprim').div_const a
