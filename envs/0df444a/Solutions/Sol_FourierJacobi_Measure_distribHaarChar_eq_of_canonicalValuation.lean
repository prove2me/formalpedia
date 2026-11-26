-- Prove2me | solution 1 for FourierJacobi.Measure.distribHaarChar_eq_of_canonicalValuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:13.829024+00:00
-- url     : https://prove2.me/submissions/a11e630a-f12d-467a-b605-528f78a1bfe4

import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Definitions.Def_FourierJacobi_Measure_UnitScaling
import Theorems.Thm_FourierJacobi_Measure_distribHaarChar_valuationRingUnits
import Theorems.Thm_FourierJacobi_Measure_canonicalUniformizer_distribHaarChar
import Theorems.Thm_FourierJacobi_Measure_exists_integral_canonical_uniformizer
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.unitScaling_t2Space
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.unitScaling_additiveHaar_regular
namespace FourierJacobi.Measure
theorem _root_.solution (u : Kˣ) (n : ℤ)
    (hu : localFieldValuation K (u : K) = (n : WithTop ℤ)) :
    distribHaarChar K u = ((residueCardinality K : ℝ≥0)⁻¹) ^ n := by
  obtain ⟨π, hπ⟩ := exists_integral_canonical_uniformizer K
  have hs : u ∈ unitValuationShell K n := hu
  rw [unitValuationShell_eq_uniformizer_smul K π hπ n] at hs
  obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hs
  simp only [smul_eq_mul, map_mul, map_zpow,
    canonicalUniformizer_distribHaarChar K π hπ,
    distribHaarChar_valuationRingUnits K v hv, mul_one]
end FourierJacobi.Measure
