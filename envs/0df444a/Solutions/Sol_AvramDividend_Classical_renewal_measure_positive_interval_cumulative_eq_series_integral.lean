-- Prove2me | solution 1 for AvramDividend.Classical.renewal_measure_positive_interval_cumulative_eq_series_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:08:10.741893+00:00
-- url     : https://prove2.me/submissions/23ab2ff2-e893-4531-9314-48dd8d7480ae

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_renewal_measure_atom_plus_real_density
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_density_Ioc_toReal_eq_intervalIntegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped ENNReal NNReal

/-- The positive-interval renewal cumulative is the real integral of its power series. -/
theorem solution
    (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hFsummable : ∀ x : ℝ,
      Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else F (n - 1) x))
    (hmzero : m 0 = Measure.dirac (0 : ℝ))
    (hmsucc : ∀ n : ℕ, m (n + 1) =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x)))
    (x : ℝ) (hx : 0 ≤ x)
    (hint : IntervalIntegrable
      (fun y : ℝ => ∑' n : ℕ,
        if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) :
    ((Measure.sum m) (Ioc (0 : ℝ) x)).toReal =
      ∫ y in (0 : ℝ)..x,
        (∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y) := by
  have hseriespos (y : ℝ) :
      0 ≤ ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y := by
    apply tsum_nonneg
    intro n
    cases n with
    | zero => simp
    | succ n => simpa using hFpos n y
  rw [renewal_measure_atom_plus_real_density F m hFpos hFmeas
    hFsummable hmzero hmsucc]
  rw [Measure.add_apply _ _ (Ioc (0 : ℝ) x)]
  have hdirac :
      (Measure.dirac (0 : ℝ)) (Ioc (0 : ℝ) x) = 0 := by simp
  rw [hdirac, zero_add]
  exact nonnegative_real_density_Ioc_toReal_eq_intervalIntegral
    _ hseriespos x hx hint
