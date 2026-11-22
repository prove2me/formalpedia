-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_scale_head_bound
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T10:42:11.642101+00:00
-- url     : https://prove2.me/submissions/7156f3d8-46ac-485c-b4ed-e8a1c3841fd1

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Filter Set

set_option linter.unusedVariables false in
theorem solution (W : ℝ → ℝ) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (hMono : ∀ x : ℝ, x ∈ Ioc (0 : ℝ) a → W x ≤ W a) (hWaNN : 0 ≤ W a)
    (hint : IntegrableOn (fun x : ℝ => Real.exp (-(β * x)) * W x) (Ioc (0 : ℝ) a)) :
    (∫ x in Ioc (0 : ℝ) a, Real.exp (-(β * x)) * W x) ≤ W a / β := by
  have hneg : -β < 0 := neg_lt_zero.mpr hβ
  have hexp : IntegrableOn (fun x : ℝ => Real.exp (-(β * x))) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul] using integrableOn_exp_mul_Ioi hneg 0
  have hUpper : IntegrableOn (fun x : ℝ => Real.exp (-(β * x)) * W a) (Ioi (0 : ℝ)) :=
    hexp.mul_const (W a)
  calc
    (∫ x in Ioc (0 : ℝ) a, Real.exp (-(β * x)) * W x)
        ≤ ∫ x in Ioc (0 : ℝ) a, Real.exp (-(β * x)) * W a :=
      setIntegral_mono_on hint (hUpper.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc
        (fun x hx => mul_le_mul_of_nonneg_left (hMono x hx) (Real.exp_pos _).le)
    _ ≤ ∫ x in Ioi (0 : ℝ), Real.exp (-(β * x)) * W a :=
      setIntegral_mono_set hUpper
        (Eventually.of_forall (fun x => mul_nonneg (Real.exp_pos _).le hWaNN))
        (Eventually.of_forall Ioc_subset_Ioi_self)
    _ = W a / β := by
      have hIntegral : (∫ x in Ioi (0 : ℝ), Real.exp (-(β * x))) = 1 / β := by
        simpa [neg_mul] using integral_exp_mul_Ioi hneg 0
      rw [integral_mul_const, hIntegral]
      simp [div_eq_mul_inv, mul_comm]
