-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_kernel_primitive_C1_of_Ici_input
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:19:16.698857+00:00
-- url     : https://prove2.me/submissions/943d5692-761f-4af6-81a2-ce6a8486e4a4

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_local_fubini_C1_of_convolution_regular
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_Ici_input
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_outer_integrable
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem solution
    (f k g : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hk : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hg : ∀ x : ℝ, 0 < x →
      (∫ s in Ioc (0 : ℝ) x, k s ∂volume) = g x) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        f s * g (x - s) ∂volume) (Ioi (0 : ℝ)) := by
  have hfLocal (x : ℝ) (hx : 0 < x) :
      IntegrableOn f (Ioc (0 : ℝ) x) volume := by
    have hfc : ContinuousOn f (Icc (0 : ℝ) x) :=
      hf.mono (by intro y hy; exact hy.1)
    exact hfc.integrableOn_Icc.mono_set (by
      intro y hy
      exact ⟨le_of_lt hy.1, hy.2⟩)
  have hkLocal (x : ℝ) (hx : 0 < x) :
      IntegrableOn k (Ioc (0 : ℝ) x) volume :=
    hk.mono_set (by intro y hy; exact hy.1)
  let J : ℝ → ℝ := fun x =>
    ∫ s in Ioc (0 : ℝ) x, k (x - s) * f s ∂volume
  have hJcont : ContinuousOn J (Ioi (0 : ℝ)) :=
    causal_l1_convolution_continuousOn_positive_of_Ici_input k f hk hf
  have hJint (x : ℝ) (hx : 0 < x) :
      IntervalIntegrable J volume 0 x := by
    have hInt : IntegrableOn J (Ioc (0 : ℝ) x) volume :=
      causal_l1_convolution_outer_integrable k f hk hf x hx
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hx)).2 hInt
  have hJrev (x : ℝ) (hx : 0 < x) :
      J x = ∫ s in Ioc (0 : ℝ) x, f (x - s) * k s ∂volume := by
    calc
      J x = (∫ s in Ioc (0 : ℝ) x, k (x - s) * f s ∂volume) := rfl
      _ = (∫ s in Ioc (0 : ℝ) x, k s * f (x - s) ∂volume) :=
        causal_convolution_time_reversal k f x (le_of_lt hx)
      _ = (∫ s in Ioc (0 : ℝ) x, f (x - s) * k s ∂volume) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro s hs
        exact mul_comm _ _
  exact causal_local_fubini_C1_of_convolution_regular
    f k g hfLocal hkLocal hg J hJrev hJcont hJint
