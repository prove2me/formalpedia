-- Prove2me | solution 1 for FourierJacobi.Valuations.localField_matrix_minima_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:13.789821+00:00
-- url     : https://prove2.me/submissions/a411a169-f680-4eac-868b-8a0d40d1f0d5

import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Theorems.Thm_FourierJacobi_Measure_localField_coordinates_determinant_ae
import Theorems.Thm_FourierJacobi_Valuations_actual_cancellation_depth_nonnegative
import Theorems.Thm_FourierJacobi_Valuations_actual_minima_integer_nonzero
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_ne_top
import Theorems.Thm_FourierJacobi_Valuations_nonzero_of_integer_valuation


set_option autoImplicit false
noncomputable section
open MeasureTheory Filter FourierJacobi.LocalMatrix
open FourierJacobi FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]
namespace FourierJacobi.Valuations
theorem _root_.solution (a z : K) (ha : a ≠ 0)
    (r : ℤ) (hr : r ≠ 0) (hz : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ)) :
    ∀ᵐ p : K × K ∂μ.prod μ, ∃ k j h c : ℤ,
      0 ≤ c ∧ localFieldValuation K a = (k : WithTop ℤ) ∧
      localFieldValuation K p.1 = (j : WithTop ℤ) ∧
      localFieldValuation K p.2 = (h : WithTop ℤ) ∧
      (2 * h = j - r → localFieldValuation K (p.2 ^ 2 / (p.1 * z) - 1) =
        (c : WithTop ℤ)) ∧
      matrixMinimum (localFieldValuation K) (g a p.1 p.2 z) =
        (entryMinimum r k j h : WithTop ℤ) ∧
      matrixMinimum (localFieldValuation K) (secondCompound (g a p.1 p.2 z)) =
        (minorMinimum r k j h c : WithTop ℤ) := by
  let v := localFieldValuation K
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((localFieldValuation_ne_top K a).mpr ha)
  have hk' : v a = (k : WithTop ℤ) := hk.symm
  filter_upwards [Measure.localField_coordinates_determinant_ae K μ z] with p hp
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp ((localFieldValuation_ne_top K p.1).mpr hp.1)
  obtain ⟨h, hh⟩ := WithTop.ne_top_iff_exists.mp ((localFieldValuation_ne_top K p.2).mpr hp.2.1)
  have hj' : v p.1 = (j : WithTop ℤ) := hj.symm
  have hh' : v p.2 = (h : WithTop ℤ) := hh.symm
  have hz0 : z ≠ 0 := nonzero_of_integer_valuation v z (-r) hz
  have hratio : p.2 ^ 2 / (p.1 * z) - 1 ≠ 0 := by
    intro he
    apply hp.2.2
    apply sub_eq_zero.mpr
    exact (div_eq_one_iff_eq (mul_ne_zero hp.1 hz0)).mp (sub_eq_zero.mp he)
  by_cases heq : 2 * h = j - r
  · obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hratio)
    have hc' : v (p.2 ^ 2 / (p.1 * z) - 1) = (c : WithTop ℤ) := hc.symm
    have hn := actual_cancellation_depth_nonnegative v p.1 p.2 z r j h c
      hj' hh' hz heq hc'
    obtain ⟨he, hm⟩ := actual_minima_integer_nonzero v a p.1 p.2 z r k j h c hr
      hk' hj' hh' hz (fun _ => hc')
    exact ⟨k, j, h, c, hn, hk', hj', hh', (fun _ => hc'), he, hm⟩
  · obtain ⟨he, hm⟩ := actual_minima_integer_nonzero v a p.1 p.2 z r k j h 0 hr
      hk' hj' hh' hz (fun h => (heq h).elim)
    exact ⟨k, j, h, 0, le_rfl, hk', hj', hh', (fun h => (heq h).elim), he, hm⟩
end FourierJacobi.Valuations
