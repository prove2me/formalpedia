-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_unweighted_atom_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:56:28.574294+00:00
-- url     : https://prove2.me/submissions/23b4a058-8b88-455d-9590-0c518433b1e1

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_unweighted_atom_area
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution (z : ℝ) (hz : 0 ≤ z) :
    (∫⁻ t in Ioc (0 : ℝ) z, ENNReal.ofReal (z - t) ∂volume) =
      ENNReal.ofReal (z ^ 2 / 2) := by
  have hc : Continuous (fun t : ℝ => z - t) :=
    continuous_const.sub continuous_id
  have hint : IntegrableOn (fun t : ℝ => z - t) (Ioc (0 : ℝ) z) volume :=
    hc.integrableOn_Ioc
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) z)]
        (fun t : ℝ => z - t) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    exact sub_nonneg.mpr ht.2
  calc
    (∫⁻ t in Ioc (0 : ℝ) z, ENNReal.ofReal (z - t) ∂volume) =
        ENNReal.ofReal (∫ t in Ioc (0 : ℝ) z, z - t ∂volume) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
    _ = ENNReal.ofReal (∫ t in (0 : ℝ)..z, z - t) := by
      rw [intervalIntegral.integral_of_le hz]
    _ = ENNReal.ofReal (z ^ 2 / 2) := by
      rw [gaussian_double_tail_unweighted_atom_area z]
