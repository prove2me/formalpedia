-- Prove2me | solution 1 for FourierJacobi.Measure.valuationRingUnits_smul_integers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:47.868061+00:00
-- url     : https://prove2.me/submissions/4aa3a09f-f0c2-4df2-ae9a-21a6ce702b14

import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Definitions.Def_FourierJacobi_Measure_UnitScaling
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
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Measure
theorem _root_.solution (u : Kˣ) (hu : u ∈ valuationRingUnits K) :
    u • (𝒪[K] : Set K) = (𝒪[K] : Set K) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro hx
    have h := (𝒪[K]).mul_mem hu.1 hx
    change (u : K) * (((u⁻¹ : Kˣ) : K) * x) ∈ 𝒪[K] at h
    simpa only [SetLike.mem_coe, ← mul_assoc, Units.mul_inv, one_mul] using h
  · intro hx
    exact (𝒪[K]).mul_mem hu.2 hx
end FourierJacobi.Measure
