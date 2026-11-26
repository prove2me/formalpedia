-- Prove2me | solution 1 for FourierJacobi.Measure.exists_integral_canonical_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:49.332418+00:00
-- url     : https://prove2.me/submissions/f16f3948-b7ee-44a4-876a-6de79b88fd03

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_nonnegative_iff
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_surjective


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
theorem _root_.solution :
    ∃ π : 𝒪[K], localFieldValuation K (π : K) = 1 := by
  obtain ⟨x, hx⟩ := localFieldValuation_surjective K (1 : WithTop ℤ)
  have hint : x ∈ 𝒪[K] := (localFieldValuation_nonnegative_iff K x).mp (by rw [hx]; norm_num)
  exact ⟨⟨x, hint⟩, hx⟩
end FourierJacobi.Measure
