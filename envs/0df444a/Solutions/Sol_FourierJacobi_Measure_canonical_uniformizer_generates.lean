-- Prove2me | solution 1 for FourierJacobi.Measure.canonical_uniformizer_generates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:14.057039+00:00
-- url     : https://prove2.me/submissions/1908a9d7-5bf7-4066-a927-b3b33e7d5ccb

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_intValue_lt_one_iff_le_exp_neg_one
import Theorems.Thm_FourierJacobi_Measure_canonicalValuation_eq_coe_iff

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero
open FourierJacobi FourierJacobi.Measure
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.integerShells_t2Space
namespace FourierJacobi.Measure
theorem _root_.solution (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) : 𝓂[K] = Ideal.span {π} := by
  have hdπ : discreteValuation K (π : K) = WithZero.exp (-1 : ℤ) :=
    (canonicalValuation_eq_coe_iff K (π : K) 1).mp hπ
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change valuation K (x : K) < 1 ↔ x ∈ (Ideal.span {π} : Set 𝒪[K])
  rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
  change valuation K (x : K) < 1 ↔ valuation K (x : K) ≤ valuation K (π : K)
  have hlt : valuation K (x : K) < 1 ↔ discreteValuation K (x : K) < 1 := by
    change valuation K (x : K) < 1 ↔
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (x : K)) < 1
    rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)]
    exact (map_lt_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).symm
  have hle : valuation K (x : K) ≤ valuation K (π : K) ↔
      discreteValuation K (x : K) ≤ discreteValuation K (π : K) :=
    (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).symm
  rw [hlt, hle, hdπ]
  exact intValue_lt_one_iff_le_exp_neg_one _
end FourierJacobi.Measure
