-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_convolution_continuousOn_positive_of_Ici_input
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T06:56:52.895775+00:00
-- url     : https://prove2.me/submissions/4292633c-9bfb-4b93-9475-b5b6bba4ab07

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_zero_extension_continuous_of_Ici_zero
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_zero_extension
import Theorems.Thm_AvramDividend_Classical_causal_reflected_kernel_mass_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_convolution_split_at_input_origin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (K V : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hV : ContinuousOn V (Ici (0 : ℝ))) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume)
      (Ioi (0 : ℝ)) := by
  let D : ℝ → ℝ := fun s => V s - V 0
  have hDc : ContinuousOn D (Ici (0 : ℝ)) :=
    hV.sub continuousOn_const
  have hD0 : D 0 = 0 := by simp [D]
  have hDz : Continuous ((Ioi (0 : ℝ)).indicator D) :=
    causal_zero_extension_continuous_of_Ici_zero D hDc hD0
  have hConv : ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, K (x - s) * D s ∂volume)
      (Ioi (0 : ℝ)) :=
    causal_l1_convolution_continuousOn_positive_of_zero_extension K D hK hDz
  have hMass : ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, K (x - s) ∂volume)
      (Ioi (0 : ℝ)) :=
    (causal_reflected_kernel_mass_continuousOn_nonnegative K hK).mono
      (by intro x hx; change (0 : ℝ) < x at hx; exact hx.le)
  have hS : ContinuousOn (fun x : ℝ =>
      V 0 * (∫ s in Ioc (0 : ℝ) x, K (x - s) ∂volume) +
        (∫ s in Ioc (0 : ℝ) x, K (x - s) * D s ∂volume))
      (Ioi (0 : ℝ)) :=
    (continuousOn_const.mul hMass).add hConv
  apply hS.congr
  intro x hx
  change (0 : ℝ) < x at hx
  exact causal_convolution_split_at_input_origin K V hK hV x hx
