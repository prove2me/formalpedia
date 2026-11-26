-- Prove2me | solution 1 for FourierJacobi.Measure.residueCardinality_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:06.243706+00:00
-- url     : https://prove2.me/submissions/d6fe735c-72a9-4ebe-b3e2-c4f89bff0373

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_residueCardinality_isPrimePow

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped ENNReal NNReal
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.localField_t2Space
variable [MeasurableSpace K] [BorelSpace K]
omit [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Measure
theorem _root_.solution : 1 < residueCardinality K := by
  have h := (residueCardinality_isPrimePow K).two_le
  omega
end FourierJacobi.Measure
