-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_measurable_signed_products
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:39:56.088688+00:00
-- url     : https://prove2.me/submissions/6e9a9587-96ce-4435-91e7-78146b16fef2

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Group.Arithmetic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Signed convolution products are measurable directly from the L1 powers. -/
theorem solution
    (k : ℝ → ℝ) (P : ℕ → ℝ → ℝ)
    (hkmeas : Measurable k)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      AEStronglyMeasurable
        (fun s : ℝ => k (x - s) * P n s)
        (volume.restrict (Ioc (0 : ℝ) x)) := by
  intro n x hx
  have hsubset : Ioc (0 : ℝ) x ⊆ Ioi (0 : ℝ) := by
    intro s hs
    exact hs.1
  have hPint : IntegrableOn (P n) (Ioc (0 : ℝ) x) volume :=
    (hPL1 n).mono_set hsubset
  have hkref : Measurable (fun s : ℝ => k (x - s)) :=
    hkmeas.comp (measurable_const.sub measurable_id)
  exact hkref.aestronglyMeasurable.mul hPint.aestronglyMeasurable
