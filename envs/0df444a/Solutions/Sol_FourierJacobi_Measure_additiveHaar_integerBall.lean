-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_integerBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:29.236745+00:00
-- url     : https://prove2.me/submissions/b8d95883-7a2d-4c18-a8e3-003d151daa76

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_exists_integral_canonical_uniformizer
import Theorems.Thm_FourierJacobi_Measure_integerBall_eq_uniformizer_smul
import Theorems.Thm_FourierJacobi_Measure_canonicalUniformizer_distribHaarChar

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero
open FourierJacobi FourierJacobi.Measure
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.integerShells_t2Space
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.integerShells_additiveHaar_regular
namespace FourierJacobi.Measure
theorem _root_.solution (n : ℤ) :
    additiveHaar K (integerBall K n) =
      (((residueCardinality K : ℝ≥0)⁻¹) ^ n : ℝ≥0) := by
  obtain ⟨π, hπ⟩ := exists_integral_canonical_uniformizer K
  rw [integerBall_eq_uniformizer_smul K π hπ n, ← distribHaarChar_mul,
    additiveHaar_integers, mul_one, map_zpow, canonicalUniformizer_distribHaarChar K π hπ]
end FourierJacobi.Measure
