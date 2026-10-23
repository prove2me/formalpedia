-- Prove2me | solution 1 for AvramDividend.Classical.causal_nonnegative_kernel_reflected_integral_le_global
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:46:22.567546+00:00
-- url     : https://prove2.me/submissions/f84d12e8-bb77-45ca-95de-cd792dd96729

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K : ℝ → ℝ) (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hKnonneg : ∀ t : ℝ, 0 < t → 0 ≤ K t)
    (x : ℝ) (hx : 0 < x) :
    (∫ s in Ioc (0 : ℝ) x, K (x - s) ∂volume) ≤
      ∫ s in Ioi (0 : ℝ), K s ∂volume := by
  have hrev := positive_Ioc_causal_convolution_comm_real
    (fun _ : ℝ => (1 : ℝ)) K x hx.le
  have hswap :
      (∫ s in Ioc (0 : ℝ) x, K (x - s) ∂volume) =
        ∫ s in Ioc (0 : ℝ) x, K s ∂volume := by
    simpa only [one_mul, mul_one] using hrev
  rw [hswap]
  have hpos : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] K := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact hKnonneg t ht
  have hsub : (Ioc (0 : ℝ) x) ≤ᵐ[volume] Ioi (0 : ℝ) := by
    filter_upwards [] with t ht
    exact ht.1
  exact setIntegral_mono_set hK hpos hsub
