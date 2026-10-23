-- Prove2me | solution 1 for AvramDividend.Classical.positive_weighted_Ioc_convolution_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T19:16:40.697121+00:00
-- url     : https://prove2.me/submissions/e936d675-e245-4e59-9d56-fbf45280e4bb

import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuous_bounded_right
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (f g : ℝ → ℝ)
    (hf : IntegrableOn (fun t : ℝ => Real.exp (-t) * f t)
      (Ioi (0 : ℝ)) volume)
    (hg : Continuous ((Ioi (0 : ℝ)).indicator
      (fun t : ℝ => Real.exp (-t) * g t)))
    (hgb : BddAbove (Set.range (fun x : ℝ =>
      ‖(Ioi (0 : ℝ)).indicator
         (fun t : ℝ => Real.exp (-t) * g t) x‖))) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume)
      (Ioi (0 : ℝ)) := by
  let F : ℝ → ℝ := fun t => Real.exp (-t) * f t
  let G : ℝ → ℝ := fun t => Real.exp (-t) * g t
  have hc : Continuous (MeasureTheory.posConvolution F G
      (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    positive_causal_convolution_continuous_bounded_right F G hf hg hgb
  have heq (x : ℝ) (hx : 0 < x) :
      (∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume) =
        Real.exp x *
          MeasureTheory.posConvolution F G
            (ContinuousLinearMap.mul ℝ ℝ) volume x := by
    have hpc :
        MeasureTheory.posConvolution F G
          (ContinuousLinearMap.mul ℝ ℝ) volume x =
          ∫ s in Ioc (0 : ℝ) x, F s * G (x - s) ∂volume := by
      unfold MeasureTheory.posConvolution
      simp only [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx),
        ContinuousLinearMap.mul_apply]
      exact intervalIntegral.integral_of_le hx.le
    rw [hpc, ← integral_const_mul]
    have hc' :
        (∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume) =
          ∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume := by
      calc
        _ = ∫ s in Ioc (0 : ℝ) x, g s * f (x - s) ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with s
          ring
        _ = _ := positive_Ioc_causal_convolution_comm_real g f x hx.le
    rw [hc']
    apply integral_congr_ae
    filter_upwards [] with s
    dsimp [F, G]
    have hexp :
        Real.exp x * (Real.exp (-s) * Real.exp (-(x - s))) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      have hzero : x + (-s + -(x - s)) = 0 := by ring
      rw [hzero]
      exact Real.exp_zero
    calc
      f s * g (x - s) =
        (Real.exp x * (Real.exp (-s) * Real.exp (-(x - s)))) *
          (f s * g (x - s)) := by rw [hexp]; ring
      _ = Real.exp x * ((Real.exp (-s) * f s) *
          (Real.exp (-(x - s)) * g (x - s))) := by ring
  have hcont : Continuous
      (fun x : ℝ => Real.exp x *
        MeasureTheory.posConvolution F G
          (ContinuousLinearMap.mul ℝ ℝ) volume x) :=
    Real.continuous_exp.mul hc
  apply hcont.continuousOn.congr
  intro x hx
  exact heq x hx
