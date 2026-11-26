-- Prove2me | solution 1 for FourierJacobi.Measure.canonicalUniformizer_distribHaarChar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:07.244262+00:00
-- url     : https://prove2.me/submissions/d0781f2f-72e6-412f-8653-85dfbaa4491f

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_canonical_uniformizer_generates
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_uniformizer_pow
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



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
theorem _root_.solution (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) :
    distribHaarChar K (canonicalUniformizerUnit K π hπ) =
      (residueCardinality K : ℝ≥0)⁻¹ := by
  have heq : canonicalUniformizerUnit K π hπ • (𝒪[K] : Set K) =
      (fun u : 𝒪[K] => (π : K) ^ 1 * (u : K)) '' Set.univ := by
    ext x
    constructor
    · rintro ⟨a, ha, hax⟩
      refine ⟨⟨a, ha⟩, Set.mem_univ _, ?_⟩
      simpa only [canonicalUniformizerUnit, Units.smul_def, Units.val_mk0, pow_one, smul_eq_mul] using hax
    · rintro ⟨a, _, hax⟩
      refine ⟨(a : K), a.property, ?_⟩
      simpa only [canonicalUniformizerUnit, Units.smul_def, Units.val_mk0, pow_one, smul_eq_mul] using hax
  have hm := additiveHaar_uniformizer_pow K π (canonical_uniformizer_generates K π hπ) 1
  have hc := distribHaarChar_mul (additiveHaar K) (canonicalUniformizerUnit K π hπ)
    (𝒪[K] : Set K)
  rw [additiveHaar_integers, mul_one, heq, hm, pow_one] at hc
  apply ENNReal.coe_injective
  rw [ENNReal.coe_inv (by exact_mod_cast (residueCardinality_pos K).ne')]
  simpa only [ENNReal.coe_natCast] using hc
end FourierJacobi.Measure
