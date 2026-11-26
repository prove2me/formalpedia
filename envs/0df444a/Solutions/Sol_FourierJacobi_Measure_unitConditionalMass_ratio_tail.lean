-- Prove2me | solution 1 for FourierJacobi.Measure.unitConditionalMass_ratio_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:12.947545+00:00
-- url     : https://prove2.me/submissions/085ba833-b379-4dea-8b81-93e85957bb93

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_mem_maximalIdeal_pow_iff_valuation_le
import Theorems.Thm_FourierJacobi_Measure_mem_integralUnits_iff
import Theorems.Thm_FourierJacobi_Measure_unitCenteredTail_subset_units
import Theorems.Thm_FourierJacobi_Measure_unitConditionalMass_unitCenteredTail
import Theorems.Thm_FourierJacobi_Measure_valuation_ratio_sub_one

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped ENNReal NNReal
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.localField_t2Space
variable [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Measure
theorem _root_.solution (π : 𝒪[K]) (hπ : 𝓂[K] = Ideal.span {π})
    (a : 𝒪[K]ˣ) (n : ℕ) :
    unitConditionalMass K {x : 𝒪[K] | x ∈ integralUnits K ∧
      valuation K (((a : 𝒪[K]) : K) / (x : K) - 1) ≤
        valuation K (π : K) ^ (n + 1)} =
      (residueCardinality K : ℝ)⁻¹ ^ n / (residueCardinality K - 1) := by
  have heq : {x : 𝒪[K] | x ∈ integralUnits K ∧
      valuation K (((a : 𝒪[K]) : K) / (x : K) - 1) ≤
        valuation K (π : K) ^ (n + 1)} = unitCenteredTail K a (n + 1) := by
    ext x
    constructor
    · rintro ⟨hx, hv⟩
      rw [valuation_ratio_sub_one K _ _ ((mem_integralUnits_iff K _).mp hx)] at hv
      exact (mem_maximalIdeal_pow_iff_valuation_le K π hπ _ (x - a)).mpr hv
    · intro hx
      have hu := unitCenteredTail_subset_units K a (Nat.succ_pos n) hx
      refine ⟨hu, ?_⟩
      rw [valuation_ratio_sub_one K _ _ ((mem_integralUnits_iff K _).mp hu)]
      exact (mem_maximalIdeal_pow_iff_valuation_le K π hπ _ (x - a)).mp hx
  rw [heq, unitConditionalMass_unitCenteredTail]
end FourierJacobi.Measure
