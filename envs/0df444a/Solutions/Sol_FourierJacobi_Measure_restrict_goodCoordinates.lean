-- Prove2me | solution 1 for FourierJacobi.Measure.restrict_goodCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:38.215807+00:00
-- url     : https://prove2.me/submissions/ee8ff778-abfb-4bb8-b577-a5af85662956

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Measure_NullSets
import Theorems.Thm_FourierJacobi_Measure_coordinates_determinant_ae

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open FourierJacobi FourierJacobi.Measure
variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [SecondCountableTopology K]
  [T2Space K] [MeasurableSpace K] [BorelSpace K]
  (μ ν : MeasureTheory.Measure K) [NullSingletonClass ν]
variable [NullSingletonClass μ]
namespace FourierJacobi.Measure
theorem _root_.solution (z : K) :
    (μ.prod ν).restrict {p : K × K |
      p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ^ 2 - p.1 * z ≠ 0} = μ.prod ν :=
  MeasureTheory.Measure.restrict_eq_self_of_ae_mem (coordinates_determinant_ae μ ν z)
end FourierJacobi.Measure
