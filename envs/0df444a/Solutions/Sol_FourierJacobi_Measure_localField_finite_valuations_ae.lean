-- Prove2me | solution 1 for FourierJacobi.Measure.localField_finite_valuations_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:48.081422+00:00
-- url     : https://prove2.me/submissions/f8ad309a-3356-452f-a0d9-956a9b902122

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Measure_NullSets
import Theorems.Thm_FourierJacobi_Measure_localField_coordinates_determinant_ae
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_ne_top


set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]
namespace FourierJacobi.Measure
theorem _root_.solution (z : K) :
    ∀ᵐ p : K × K ∂μ.prod μ, ∃ j h c : ℤ,
      Valuations.localFieldValuation K p.1 = (j : WithTop ℤ) ∧
      Valuations.localFieldValuation K p.2 = (h : WithTop ℤ) ∧
      Valuations.localFieldValuation K (p.2 ^ 2 - p.1 * z) = (c : WithTop ℤ) := by
  filter_upwards [localField_coordinates_determinant_ae K μ z] with p hp
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp
    ((Valuations.localFieldValuation_ne_top K p.1).mpr hp.1)
  obtain ⟨h, hh⟩ := WithTop.ne_top_iff_exists.mp
    ((Valuations.localFieldValuation_ne_top K p.2).mpr hp.2.1)
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp
    ((Valuations.localFieldValuation_ne_top K _).mpr hp.2.2)
  exact ⟨j, h, c, hj.symm, hh.symm, hc.symm⟩
end FourierJacobi.Measure
