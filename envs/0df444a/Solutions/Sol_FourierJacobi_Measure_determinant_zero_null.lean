-- Prove2me | solution 1 for FourierJacobi.Measure.determinant_zero_null
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:34.036085+00:00
-- url     : https://prove2.me/submissions/faf707db-caf3-4025-bd14-d19dc3ecae20

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Measure_NullSets
import Theorems.Thm_FourierJacobi_Measure_measurableSet_determinant_zero
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
namespace FourierJacobi.Measure
theorem _root_.solution (z : K) :
    (μ.prod ν) {p : K × K | p.2 ^ 2 - p.1 * z = 0} = 0 := by
  apply MeasureTheory.Measure.measure_prod_null_of_ae_null (measurableSet_determinant_zero z)
  filter_upwards [] with x
  change ν {y : K | y ^ 2 - x * z = 0} = 0
  have hfinite : Set.Finite {y : K | y ^ 2 - x * z = 0} := by
    have hpoly : (Polynomial.X ^ 2 - Polynomial.C (x * z) : Polynomial K) ≠ 0 := by
      intro h
      have hc := congrArg (fun p : Polynomial K => p.coeff 2) h
      norm_num at hc
    convert Polynomial.finite_setOfPred_isRoot hpoly using 1
    ext y
    simp [Polynomial.IsRoot]
  exact hfinite.measure_zero ν
end FourierJacobi.Measure
