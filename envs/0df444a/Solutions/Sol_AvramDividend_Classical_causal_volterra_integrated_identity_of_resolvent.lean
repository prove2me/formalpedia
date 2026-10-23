-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_integrated_identity_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T17:54:30.93559+00:00
-- url     : https://prove2.me/submissions/d80b9bb3-4deb-47bc-8f14-86b29e30b765

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_l1_fullkernel_primitive_fubini

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

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
  have hcont : ContinuousOn g (Icc (0 : ℝ) x) :=
    hg.mono (by intro t ht; exact ht.1)
  have hgi : IntegrableOn g (Ioc (0 : ℝ) x) volume :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hunit : IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Ioc (0 : ℝ) x) volume := by
    exact integrableOn_const (by simp) (by simp)
  have hgmul : IntegrableOn (fun t : ℝ => a * g t)
      (Ioc (0 : ℝ) x) volume := hgi.const_mul a
  have hOne :
      (∫ t in Ioc (0 : ℝ) x, (1 : ℝ) ∂volume) = x := by
    simpa [setIntegral_const] using (Real.volume_real_Ioc_of_le hx.le)
  have hSub :
      (∫ t in Ioc (0 : ℝ) x, (1 - a * g t) ∂volume) =
        x - a * (∫ t in Ioc (0 : ℝ) x, g t ∂volume) := by
    rw [integral_sub hunit hgmul, integral_const_mul, hOne]
  have hConv :
      (∫ t in Ioc (0 : ℝ) x,
        (∫ s in Ioc (0 : ℝ) t,
          (β + K (t - s)) * g s ∂volume) ∂volume) =
        x - a * (∫ t in Ioc (0 : ℝ) x, g t ∂volume) := by
    calc
      _ = ∫ t in Ioc (0 : ℝ) x, (1 - a * g t) ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        have ht0 : 0 < t := ht.1
        linarith [hgeq t ht0]
      _ = _ := hSub
  calc
    a * (∫ t in Ioc (0 : ℝ) x, g t ∂volume) +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) *
            (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) =
      a * (∫ t in Ioc (0 : ℝ) x, g t ∂volume) +
        (∫ t in Ioc (0 : ℝ) x,
          (∫ s in Ioc (0 : ℝ) t,
            (β + K (t - s)) * g s ∂volume) ∂volume) := by
      rw [← causal_l1_fullkernel_primitive_fubini K g β hK hg x hx]
    _ = x := by rw [hConv]; ring