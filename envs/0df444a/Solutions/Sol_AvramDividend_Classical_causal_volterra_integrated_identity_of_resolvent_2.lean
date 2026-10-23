-- Prove2me | solution 2 for AvramDividend.Classical.causal_volterra_integrated_identity_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T20:57:21.365978+00:00
-- url     : https://prove2.me/submissions/5e843dcc-87cc-4514-b377-49bae6fa0423

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_causal_l1_fullkernel_primitive_fubini

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Integrating a derivative resolvent equation yields its integrated equation. -/
theorem solution
    (K g : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      a * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) :
    ∀ x : ℝ, 0 < x →
      a * (∫ t in Ioc (0 : ℝ) x, g t ∂volume) +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) *
            (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) = x := by
  intro x hx
  have hc : ContinuousOn g (Icc (0 : ℝ) x) :=
    hg.mono (by intro t ht; exact ht.1)
  have hgi : IntegrableOn g (Ioc (0 : ℝ) x) volume :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hagi : IntegrableOn (fun t : ℝ => a * g t)
      (Ioc (0 : ℝ) x) volume := hgi.const_mul a
  have hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Ioc (0 : ℝ) x) volume :=
    integrableOn_const (hs := (measure_Ioc_lt_top : volume (Ioc (0 : ℝ) x) < ⊤).ne)
  have hconvInt : IntegrableOn
      (fun t : ℝ => ∫ s in Ioc (0 : ℝ) t,
        (β + K (t - s)) * g s ∂volume)
      (Ioc (0 : ℝ) x) volume := by
    apply (hOne.sub hagi).congr_fun _ measurableSet_Ioc
    intro t ht
    dsimp
    linarith [hgeq t ht.1]
  have hPoint :
      (∫ t in Ioc (0 : ℝ) x,
        a * g t + (∫ s in Ioc (0 : ℝ) t,
          (β + K (t - s)) * g s ∂volume) ∂volume) =
      (∫ t in Ioc (0 : ℝ) x, (1 : ℝ) ∂volume) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hgeq t ht.1
  have hUnit : (∫ t in Ioc (0 : ℝ) x, (1 : ℝ) ∂volume) = x := by
    rw [← intervalIntegral.integral_of_le hx.le]
    simp
  calc
    a * (∫ t in Ioc (0 : ℝ) x, g t ∂volume) +
      (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) *
          (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) =
        (∫ t in Ioc (0 : ℝ) x, a * g t ∂volume) +
        (∫ t in Ioc (0 : ℝ) x,
          ∫ s in Ioc (0 : ℝ) t, (β + K (t - s)) * g s ∂volume ∂volume) := by
            rw [integral_const_mul,
              causal_l1_fullkernel_primitive_fubini K g β hK hg x hx]
    _ = (∫ t in Ioc (0 : ℝ) x,
          a * g t +
            (∫ s in Ioc (0 : ℝ) t,
              (β + K (t - s)) * g s ∂volume) ∂volume) :=
      (integral_add hagi hconvInt).symm
    _ = (∫ t in Ioc (0 : ℝ) x, (1 : ℝ) ∂volume) := hPoint
    _ = x := hUnit
