-- Prove2me | solution 1 for AvramDividend.Classical.causal_signed_integrable_product_of_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:14:55.765684+00:00
-- url     : https://prove2.me/submissions/34959eee-96b4-4905-ba8c-48cd8c9b060e

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The signed causal product is integrable under an integrable positive envelope. -/
theorem solution
    (k κ P F : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hkdom : ∀ t : ℝ, 0 ≤ t → |k t| ≤ κ t)
    (hPdom : ∀ t : ℝ, 0 ≤ t → |P t| ≤ F t)
    (hMeas : AEStronglyMeasurable
      (fun s : ℝ => k (x - s) * P s)
      (volume.restrict (Ioc (0 : ℝ) x)))
    (hFint : IntervalIntegrable
      (fun s : ℝ => κ (x - s) * F s) volume 0 x) :
    IntervalIntegrable
      (fun s : ℝ => k (x - s) * P s) volume 0 x := by
  have hEnv : IntegrableOn (fun s : ℝ => κ (x - s) * F s)
      (Ioc (0 : ℝ) x) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).1 hFint
  have hAE : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) x)),
      ‖k (x - s) * P s‖ ≤ κ (x - s) * F s := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with s hs
    have hs0 : 0 ≤ s := hs.1.le
    have hxs : 0 ≤ x - s := sub_nonneg.mpr hs.2
    have hk := hkdom (x - s) hxs
    have hp := hPdom s hs0
    have hκ : 0 ≤ κ (x - s) := (abs_nonneg _).trans hk
    calc
      ‖k (x - s) * P s‖ = |k (x - s)| * |P s| := by
        rw [Real.norm_eq_abs, abs_mul]
      _ ≤ κ (x - s) * F s :=
        mul_le_mul hk hp (abs_nonneg _) hκ
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).2
    (hEnv.mono' hMeas hAE)
