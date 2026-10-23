-- Prove2me | solution 1 for AvramDividend.Classical.positive_L1_kernel_exponential_weight_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:54:22.299984+00:00
-- url     : https://prove2.me/submissions/69f76ec2-1506-4700-a268-81b91afee423

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K : ℝ → ℝ) (w : ℝ) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun t : ℝ => Real.exp (-w * t) * K t)
      (Ioi (0 : ℝ)) volume := by
  have hfcont : Continuous (fun t : ℝ => Real.exp (-w * t)) := by
    fun_prop
  have hfmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-w * t))
      (volume.restrict (Ioi (0 : ℝ))) :=
    hfcont.aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖Real.exp (-w * t)‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have hnonneg : 0 ≤ w * t := mul_nonneg hw.le ht.le
    have hexp : Real.exp (-w * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    simpa only [Real.norm_eq_abs, Real.abs_exp] using hexp
  exact hK.bdd_mul hfmeas hbound
