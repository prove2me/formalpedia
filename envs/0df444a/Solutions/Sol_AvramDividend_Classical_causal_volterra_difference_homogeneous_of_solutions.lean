-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_difference_homogeneous_of_solutions
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:47:51.72975+00:00
-- url     : https://prove2.me/submissions/6f1a2d14-6c31-426f-b786-110ef45628f6

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_full_kernel_locally_bounded_input_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K V G : ℝ → ℝ) (a β : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hGc : ContinuousOn G (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C)
    (hGb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C)
    (hVe : ∀ x : ℝ, 0 < x →
      a * V x + (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * V s ∂volume) = x)
    (hGe : ∀ x : ℝ, 0 < x →
      a * G x + (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * G s ∂volume) = x) :
    ∀ x : ℝ, 0 < x →
      a * (V x - G x) +
      (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * (V s - G s) ∂volume) = 0 := by
  intro x hx
  have hVi :=
    causal_full_kernel_locally_bounded_input_integrable K V β hK hVc hVb x hx
  have hGi :=
    causal_full_kernel_locally_bounded_input_integrable K G β hK hGc hGb x hx
  have hIntegral :
      (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * (V s - G s) ∂volume) =
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) -
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * G s ∂volume) := by
    calc
      _ = ∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * V s -
              (β + K (x - s)) * G s ∂volume := by
          congr 1
          funext s
          ring
      _ = _ := integral_sub hVi hGi
  calc
    a * (V x - G x) +
      (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * (V s - G s) ∂volume) =
      (a * V x + ∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * V s ∂volume) -
      (a * G x + ∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * G s ∂volume) := by
          rw [hIntegral]
          ring
    _ = 0 := by rw [hVe x hx, hGe x hx]; ring
