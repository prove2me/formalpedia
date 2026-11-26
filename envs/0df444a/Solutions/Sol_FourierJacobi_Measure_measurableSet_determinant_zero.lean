-- Prove2me | solution 1 for FourierJacobi.Measure.measurableSet_determinant_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:59.14274+00:00
-- url     : https://prove2.me/submissions/0d857a8b-9caf-4173-a991-ae2b78bd3fff

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Measure_NullSets

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open FourierJacobi FourierJacobi.Measure
variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [SecondCountableTopology K]
  [T2Space K] [MeasurableSpace K] [BorelSpace K]
  (μ ν : MeasureTheory.Measure K) [NullSingletonClass ν]
namespace FourierJacobi.Measure
theorem _root_.solution (z : K) :
    MeasurableSet {p : K × K | p.2 ^ 2 - p.1 * z = 0} := by
  exact (isClosed_eq (by fun_prop) continuous_const).measurableSet
end FourierJacobi.Measure
