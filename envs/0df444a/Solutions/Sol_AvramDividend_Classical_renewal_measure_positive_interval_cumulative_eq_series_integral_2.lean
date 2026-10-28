-- Prove2me | solution 2 for AvramDividend.Classical.renewal_measure_positive_interval_cumulative_eq_series_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:08:44.612948+00:00
-- url     : https://prove2.me/submissions/eb8f3be7-a1cf-4194-a52f-2feeb89bafee

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_renewal_measure_atom_plus_real_density
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_density_Ioc_toReal_eq_intervalIntegral
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped ENNReal NNReal
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
  rw [AvramDividend.Classical.renewal_measure_atom_plus_real_density F m hFpos hFmeas hFsummable
    hmzero hmsucc, Measure.add_apply, Measure.dirac_apply' _ measurableSet_Ioc,
    Set.indicator_of_notMem (by simp), zero_add]
  refine AvramDividend.Classical.nonnegative_real_density_Ioc_toReal_eq_intervalIntegral _ ?_ x hx hint
  intro y
  refine tsum_nonneg fun n => ?_
  split_ifs
  · exact le_refl 0
  · exact hFpos _ _
