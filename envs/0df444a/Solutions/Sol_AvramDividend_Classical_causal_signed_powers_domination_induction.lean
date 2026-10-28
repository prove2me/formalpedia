-- Prove2me | solution 1 for AvramDividend.Classical.causal_signed_powers_domination_induction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:26:10.000221+00:00
-- url     : https://prove2.me/submissions/fcee3ea8-4cc1-4817-b3bd-e28e7cbcfda6

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_signed_integrable_product_of_envelope
import Theorems.Thm_AvramDividend_Classical_causal_signed_convolution_integral_abs_le_majorant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Signed-power domination and product integrability propagate together. -/
theorem solution
    (k κ : ℝ → ℝ) (P F : ℕ → ℝ → ℝ)
    (hkdom : ∀ t : ℝ, 0 ≤ t → |k t| ≤ κ t)
    (hP0 : P 0 = k) (hF0 : F 0 = κ)
    (hPsucc : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      P (n + 1) x =
        ∫ s in (0 : ℝ)..x, k (x - s) * P n s)
    (hFsucc : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F (n + 1) x =
        ∫ s in (0 : ℝ)..x, κ (x - s) * F n s)
    (hPzero : ∀ n : ℕ, |P n 0| ≤ F n 0)
    (hMeas : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      AEStronglyMeasurable
        (fun s : ℝ => k (x - s) * P n s)
        (volume.restrict (Ioc (0 : ℝ) x)))
    (hFint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable
        (fun s : ℝ => κ (x - s) * F n s) volume 0 x) :
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → |P n t| ≤ F n t := by
  have hκnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t := by
    intro t ht
    exact (abs_nonneg (k t)).trans (hkdom t ht)
  intro n
  induction n with
  | zero =>
    intro t ht
    simpa only [hP0, hF0] using hkdom t ht
  | succ n ih =>
    intro x hx
    rcases lt_or_eq_of_le hx with hpos | hzero
    · have hPint :=
        causal_signed_integrable_product_of_envelope
          k κ (P n) (F n) x hpos hkdom ih
          (hMeas n x hpos) (hFint n x hpos)
      have hbound :=
        causal_signed_convolution_integral_abs_le_majorant
          k κ (P n) (F n) x hpos hPint (hFint n x hpos)
          (by
            intro s hs
            exact hkdom (x - s) (sub_nonneg.mpr hs.2.le))
          (by
            intro s hs
            exact ih s hs.1.le)
          (by
            intro s hs
            exact hκnonneg (x - s) (sub_nonneg.mpr hs.2.le))
      calc
        |P (n + 1) x| =
            |∫ s in (0 : ℝ)..x, k (x - s) * P n s| := by
              rw [hPsucc n x hpos]
        _ ≤ ∫ s in (0 : ℝ)..x, κ (x - s) * F n s := hbound
        _ = F (n + 1) x := (hFsucc n x hpos).symm
    · subst x
      exact hPzero (n + 1)
