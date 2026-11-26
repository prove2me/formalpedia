-- Prove2me | solution 1 for FourierJacobi.Measure.determinant_zero_section
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:34.40421+00:00
-- url     : https://prove2.me/submissions/744bc615-7e6e-4200-a6f7-c40ab8e97f58

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Measure_NullSets
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open FourierJacobi FourierJacobi.Measure
variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [SecondCountableTopology K]
  [T2Space K] [MeasurableSpace K] [BorelSpace K]
  (μ ν : MeasureTheory.Measure K) [NullSingletonClass ν]
omit [TopologicalSpace K] [IsTopologicalRing K] [SecondCountableTopology K]
  [T2Space K] [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Measure
theorem _root_.solution (y z : K) (hz : z ≠ 0) :
    {x : K | y ^ 2 - x * z = 0} = {y ^ 2 / z} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff, sub_eq_zero]
  exact ⟨fun h => (eq_div_iff hz).mpr h.symm, fun h => ((eq_div_iff hz).mp h).symm⟩
end FourierJacobi.Measure
