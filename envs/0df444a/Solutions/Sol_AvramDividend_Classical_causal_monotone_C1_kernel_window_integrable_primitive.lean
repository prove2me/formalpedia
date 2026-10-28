-- Prove2me | solution 1 for AvramDividend.Classical.causal_monotone_C1_kernel_window_integrable_primitive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:59:35.129583+00:00
-- url     : https://prove2.me/submissions/be641849-0048-4419-bef8-b3890055c22c

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_monotone_C1_kernel_derivative_primitive_from_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

/-- Cut off a monotone C1 derivative while preserving its local primitives. -/
theorem solution
    (g : ℝ → ℝ) (hg0 : g 0 = 0)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgmono : MonotoneOn g (Ici (0 : ℝ)))
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (R : ℝ) (hR : 0 < R) :
    ∃ k : ℝ → ℝ,
      IntegrableOn k (Ioi (0 : ℝ)) volume ∧
      ∀ x : ℝ, 0 < x → x ≤ R →
        (∫ t in Ioc (0 : ℝ) x, k t ∂volume) = g x := by
  let k : ℝ → ℝ := (Ioc (0 : ℝ) R).indicator (deriv g)
  have hRint := monotone_C1_kernel_derivative_primitive_from_zero
    g hg0 hg hgmono hgC1 R hR
  have hKlocal : IntegrableOn (deriv g) (Ioc (0 : ℝ) R) volume :=
    hRint.1.1
  have hK : IntegrableOn k (Ioi (0 : ℝ)) volume :=
    (hKlocal.integrable_indicator measurableSet_Ioc).integrableOn
  refine ⟨k, hK, ?_⟩
  intro x hx hxR
  have hsubset : Ioc (0 : ℝ) x ⊆ Ioc (0 : ℝ) R := by
    intro t ht
    exact ⟨ht.1, le_trans ht.2 hxR⟩
  have hIoc : (∫ t in Ioc (0 : ℝ) x, k t ∂volume) =
      ∫ t in Ioc (0 : ℝ) x, deriv g t ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change (Ioc (0 : ℝ) R).indicator (deriv g) t = deriv g t
    exact Set.indicator_of_mem (hsubset ht) (deriv g)
  calc
    (∫ t in Ioc (0 : ℝ) x, k t ∂volume) =
        ∫ t in Ioc (0 : ℝ) x, deriv g t ∂volume := hIoc
    _ = ∫ t in (0 : ℝ)..x, deriv g t := by
      exact (intervalIntegral.integral_of_le hx.le).symm
    _ = g x :=
      (monotone_C1_kernel_derivative_primitive_from_zero
        g hg0 hg hgmono hgC1 x hx).2
