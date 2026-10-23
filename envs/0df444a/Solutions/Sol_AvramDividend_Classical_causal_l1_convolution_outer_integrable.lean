-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_convolution_outer_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T19:16:22.438764+00:00
-- url     : https://prove2.me/submissions/b69e50d9-2080-4826-ab08-79a3c1a89138

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ =>
      ∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume)
      (Ioc (0 : ℝ) x) volume := by
  let gc : ℝ → ℝ := (Ioc (0 : ℝ) x).indicator g
  have hcont : ContinuousOn g (Icc (0 : ℝ) x) :=
    hg.mono (by intro s hs; exact hs.1)
  have hgi : IntegrableOn g (Ioc (0 : ℝ) x) volume :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hgc : Integrable gc volume :=
    (integrable_indicator_iff measurableSet_Ioc).2 hgi
  have hgcpos : IntegrableOn gc (Ioi (0 : ℝ)) volume :=
    hgc.integrableOn
  have hcv : Integrable
      (posConvolution gc K (ContinuousLinearMap.mul ℝ ℝ) volume) volume :=
    integrable_posConvolution hgcpos hK (ContinuousLinearMap.mul ℝ ℝ)
  apply hcv.integrableOn.congr_fun _ measurableSet_Ioc
  intro t ht
  change (posConvolution gc K (ContinuousLinearMap.mul ℝ ℝ) volume) t =
    ∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume
  unfold posConvolution
  rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht.1)]
  rw [intervalIntegral.integral_of_le ht.1.le]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  have hsc : s ∈ Ioc (0 : ℝ) x := ⟨hs.1, le_trans hs.2 ht.2⟩
  simp [gc, Set.indicator_of_mem hsc, mul_comm]
