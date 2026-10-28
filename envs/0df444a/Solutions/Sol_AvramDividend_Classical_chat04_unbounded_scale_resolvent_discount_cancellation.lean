-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_scale_resolvent_discount_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:51:13.140926+00:00
-- url     : https://prove2.me/submissions/01f5f4f0-c404-4e69-a485-7c4562171b48

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact q-scale convolution cancellation used by a killed resolvent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q p : ℝ) (hq : 0 ≤ q) (hp : 0 < p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (x : ℝ) (hx : 0 < x) :
    Wqp x / p -
      (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) =
    Wq x / p := by
  have hqp : 0 ≤ q + p := by linarith
  have hc :=
    unbounded_scale_resolvent_convolution
      X hnbv q (q + p) hq hqp Wq Wqp hWq hWqp x hx
  have hd : q + p - q = p := by ring
  rw [hd] at hc
  calc
    Wqp x / p -
      (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) =
      (Wq x + p *
        (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s))) / p -
      (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) := by rw [hc]
    _ = Wq x / p := by field_simp [ne_of_gt hp]; ring
