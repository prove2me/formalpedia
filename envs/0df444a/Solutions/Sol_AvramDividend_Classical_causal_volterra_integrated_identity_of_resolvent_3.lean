-- Prove2me | solution 3 for AvramDividend.Classical.causal_volterra_integrated_identity_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:12:44.453084+00:00
-- url     : https://prove2.me/submissions/fed3deb1-381f-4c2a-8dc9-d699076266bc

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
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
  let H : ℝ → ℝ := fun t =>
    ∫ s in Ioc (0 : ℝ) t, (β + K (t - s)) * g s ∂volume
  have hgc : ContinuousOn g (Icc (0 : ℝ) x) := hg.mono (by
    intro t ht
    exact ht.1)
  have hgi : IntegrableOn g (Ioc (0 : ℝ) x) volume :=
    hgc.integrableOn_Icc.mono_set (by
      intro t ht
      exact ⟨le_of_lt ht.1, ht.2⟩)
  have hHi : Integrable H (volume.restrict (Ioc (0 : ℝ) x)) := by
    have hb : Integrable (fun t : ℝ => (1 : ℝ) - a * g t)
        (volume.restrict (Ioc (0 : ℝ) x)) :=
      (integrable_const (μ := volume.restrict (Ioc (0 : ℝ) x)) (1 : ℝ)).sub (hgi.const_mul a)
    apply hb.congr
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    dsimp [H]
    linarith [hgeq t ht.1]
  have hcomp : (∫ t in Ioc (0 : ℝ) x,
      a * g t + H t ∂volume) =
      ∫ t in Ioc (0 : ℝ) x, (1 : ℝ) ∂volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    simpa only [H] using hgeq t ht.1
  have hFub := causal_l1_fullkernel_primitive_fubini K g β hK hg x hx
  calc
    a * (∫ t in Ioc (0 : ℝ) x, g t ∂volume) +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) *
            (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume)
        = (∫ t in Ioc (0 : ℝ) x, a * g t ∂volume) +
            (∫ t in Ioc (0 : ℝ) x, H t ∂volume) := by
              rw [integral_const_mul, ← hFub]
    _ = ∫ t in Ioc (0 : ℝ) x, a * g t + H t ∂volume := by
      exact (integral_add (hgi.const_mul a) hHi).symm
    _ = ∫ t in Ioc (0 : ℝ) x, (1 : ℝ) ∂volume := hcomp
    _ = x := by simp [Real.volume_Ioc, hx.le]
