-- Prove2me | solution 1 for FourierJacobi.Measure.canonical_uniformizer_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:12.911234+00:00
-- url     : https://prove2.me/submissions/6fee6996-a954-43a3-920d-9abb01241b51

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_canonicalValuation_eq_coe_iff
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
namespace FourierJacobi.Measure
theorem _root_.solution (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) (n : ℤ) :
    localFieldValuation K ((π : K) ^ n) = (n : WithTop ℤ) := by
  rw [canonicalValuation_eq_coe_iff, map_zpow₀,
    (canonicalValuation_eq_coe_iff K (π : K) 1).mp hπ, ← WithZero.exp_zsmul]
  congr 1
  simp
end FourierJacobi.Measure
