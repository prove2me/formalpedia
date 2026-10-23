-- Prove2me | solution 1 for AvramDividend.Classical.positive_real_laplace_causal_convolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T16:30:39.360652+00:00
-- url     : https://prove2.me/submissions/fc1449e2-f5ec-48a5-a5e3-7e622e55b98d

import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (f g : ℝ → ℝ) (θ : ℝ)
    (hf : IntegrableOn (fun s : ℝ => Real.exp (-θ * s) * f s)
      (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun s : ℝ => Real.exp (-θ * s) * g s)
      (Ioi (0 : ℝ)) volume) :
    (∫ x in Ioi (0 : ℝ), ∫ s in Ioc (0 : ℝ) x,
      Real.exp (-θ * x) * (f s * g (x - s)) ∂volume ∂volume) =
      (∫ s in Ioi (0 : ℝ), Real.exp (-θ * s) * f s ∂volume) *
        (∫ t in Ioi (0 : ℝ), Real.exp (-θ * t) * g t ∂volume) := by
  let F : ℝ → ℝ := fun s => Real.exp (-θ * s) * f s
  let G : ℝ → ℝ := fun s => Real.exp (-θ * s) * g s
  have hconv :
      (∫ x in Ioi (0 : ℝ), ∫ s in (0 : ℝ)..x,
        F s * G (x - s) ∂volume ∂volume) =
      (∫ s in Ioi (0 : ℝ), F s ∂volume) *
        (∫ t in Ioi (0 : ℝ), G t ∂volume) :=
    MeasureTheory.integral_posConvolution hf hg
      (ContinuousLinearMap.mul ℝ ℝ)
  have hpoint (x : ℝ) (hx : 0 < x) :
      (∫ s in (0 : ℝ)..x, F s * G (x - s) ∂volume) =
      (∫ s in Ioc (0 : ℝ) x,
        Real.exp (-θ * x) * (f s * g (x - s)) ∂volume) := by
    rw [intervalIntegral.integral_of_le hx.le]
    apply integral_congr_ae
    filter_upwards [] with s
    dsimp [F, G]
    have hexp :
        Real.exp (-θ * s) * Real.exp (-θ * (x - s)) =
          Real.exp (-θ * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      (Real.exp (-θ * s) * f s) *
          (Real.exp (-θ * (x - s)) * g (x - s)) =
        (Real.exp (-θ * s) * Real.exp (-θ * (x - s))) *
          (f s * g (x - s)) := by ring
      _ = Real.exp (-θ * x) * (f s * g (x - s)) := by rw [hexp]
  calc
    (∫ x in Ioi (0 : ℝ), ∫ s in Ioc (0 : ℝ) x,
      Real.exp (-θ * x) * (f s * g (x - s)) ∂volume ∂volume) =
        (∫ x in Ioi (0 : ℝ), ∫ s in (0 : ℝ)..x,
          F s * G (x - s) ∂volume ∂volume) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      exact (hpoint x hx).symm
    _ = _ := hconv
