-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_kernel_primitive_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T20:45:41.883626+00:00
-- url     : https://prove2.me/submissions/f821ae66-0181-4fe3-b030-4d0d3c5c4e04

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_causal_primitive_C1_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun s : ℝ =>
      K (x - s) * (∫ t in Ioc (0 : ℝ) s, g t ∂volume))
      (Ioc (0 : ℝ) x) volume := by
  let G : ℝ → ℝ := fun s =>
    ∫ t in Ioc (0 : ℝ) s, g t ∂volume
  have hC1 := (causal_primitive_C1_locally_bounded g hg).1
  have hGcont : ContinuousOn G (Ioc (0 : ℝ) x) :=
    hC1.continuousOn.mono (by intro s hs; exact hs.1)
  have hGmeas : AEStronglyMeasurable G
      (volume.restrict (Ioc (0 : ℝ) x)) :=
    hGcont.aestronglyMeasurable measurableSet_Ioc
  obtain ⟨C, hC⟩ := (causal_primitive_C1_locally_bounded g hg).2 x hx
  have hGbound : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) x), ‖G s‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simpa only [G, Real.norm_eq_abs] using hC s hs
  have hKone := (causal_l1_kernel_continuous_input_integrable
    K (fun _ : ℝ => (1 : ℝ)) hK continuousOn_const) x hx
  have hKint : IntegrableOn (fun s : ℝ => K (x - s))
      (Ioc (0 : ℝ) x) volume := by
    simpa only [mul_one] using hKone
  have hprod : Integrable (fun s : ℝ => G s * K (x - s))
      (volume.restrict (Ioc (0 : ℝ) x)) :=
    hKint.bdd_mul hGmeas hGbound
  change Integrable (fun s : ℝ => K (x - s) * G s)
    (volume.restrict (Ioc (0 : ℝ) x))
  simpa only [mul_comm] using hprod
