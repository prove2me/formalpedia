-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_kernel_product_le_sup_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:56:52.319746+00:00
-- url     : https://prove2.me/submissions/805fda81-f841-4fbe-81c3-bd2ad3ff48b9

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (L D : ℝ → ℝ) (w R x : ℝ)
    (hL : IntegrableOn L (Ioi (0 : ℝ)) volume)
    (hLnonneg : ∀ u : ℝ, 0 ≤ L u)
    (hDcont : ContinuousOn D (Ioi (0 : ℝ)))
    (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R)
    (hM : BddAbove ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
      Ioc (0 : ℝ) R)) :
    (∫ s in Ioc (0 : ℝ) x,
      L (x - s) * (Real.exp (-(w * s)) * |D s|) ∂volume) ≤
    sSup ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
      Ioc (0 : ℝ) R) *
    (∫ s in Ioc (0 : ℝ) x, L (x - s) ∂volume) := by
  let M : ℝ :=
    sSup ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) '' Ioc (0 : ℝ) R)
  have hMnonneg : 0 ≤ M := by
    have hle : Real.exp (-(w * x)) * |D x| ≤ M :=
      le_csSup hM ⟨x, hx, rfl⟩
    exact le_trans (mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)) hle
  have hKint : IntegrableOn (fun s : ℝ => L (x - s))
      (Ioc (0 : ℝ) x) volume := by
    simpa only [mul_one] using
      (causal_l1_kernel_continuous_input_integrable
        L (fun _ : ℝ => 1) hL continuousOn_const x hx.1)
  have hcD : ContinuousOn (fun s : ℝ =>
      Real.exp (-(w * s)) * |D s|) (Ioc (0 : ℝ) x) := by
    have hDc : ContinuousOn D (Ioc (0 : ℝ) x) :=
      hDcont.mono (by intro s hs; exact hs.1)
    have hEc : Continuous (fun s : ℝ => Real.exp (-(w * s))) := by fun_prop
    exact hEc.continuousOn.mul hDc.abs
  have hDmeas : AEStronglyMeasurable
      (fun s : ℝ => Real.exp (-(w * s)) * |D s|)
      (volume.restrict (Ioc (0 : ℝ) x)) :=
    hcD.aestronglyMeasurable measurableSet_Ioc
  have hprodmeas : AEStronglyMeasurable
      (fun s : ℝ => L (x - s) * (Real.exp (-(w * s)) * |D s|))
      (volume.restrict (Ioc (0 : ℝ) x)) :=
    hKint.aestronglyMeasurable.mul hDmeas
  have hbound : ∀ᵐ s : ℝ ∂(volume.restrict (Ioc (0 : ℝ) x)),
      L (x - s) * (Real.exp (-(w * s)) * |D s|) ≤ M * L (x - s) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with s hs
    have hsR : s ∈ Ioc (0 : ℝ) R := ⟨hs.1, le_trans hs.2 hx.2⟩
    have hsle : Real.exp (-(w * s)) * |D s| ≤ M :=
      le_csSup hM ⟨s, hsR, rfl⟩
    calc
      L (x - s) * (Real.exp (-(w * s)) * |D s|) ≤
          L (x - s) * M := mul_le_mul_of_nonneg_left hsle (hLnonneg _)
      _ = M * L (x - s) := mul_comm _ _
  have hnorm : ∀ᵐ s : ℝ ∂(volume.restrict (Ioc (0 : ℝ) x)),
      ‖L (x - s) * (Real.exp (-(w * s)) * |D s|)‖ ≤
        ‖M * L (x - s)‖ := by
    filter_upwards [hbound] with s hs
    have hExp : 0 ≤ Real.exp (-(w * s)) * |D s| :=
      mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
    have hK : 0 ≤ L (x - s) := hLnonneg _
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK,
      abs_of_nonneg hExp, abs_of_nonneg hMnonneg] using hs
  have hprod : Integrable
      (fun s : ℝ => L (x - s) * (Real.exp (-(w * s)) * |D s|))
      (volume.restrict (Ioc (0 : ℝ) x)) :=
    (hKint.const_mul M).mono hprodmeas hnorm
  have hmono := integral_mono_ae hprod (hKint.const_mul M) hbound
  simpa only [M, integral_const_mul] using hmono
