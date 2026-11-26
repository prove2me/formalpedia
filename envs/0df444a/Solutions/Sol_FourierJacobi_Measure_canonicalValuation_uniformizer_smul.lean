-- Prove2me | solution 1 for FourierJacobi.Measure.canonicalValuation_uniformizer_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:05.836891+00:00
-- url     : https://prove2.me/submissions/6cf9a5db-a6fc-4763-b965-fe7a03981e23

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_canonical_uniformizer_zpow

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
    (hπ : localFieldValuation K (π : K) = 1) (n : ℤ) (x : K) :
    localFieldValuation K ((canonicalUniformizerUnit K π hπ ^ n) • x) =
      (n : WithTop ℤ) + localFieldValuation K x := by
  change localFieldValuation K (((canonicalUniformizerUnit K π hπ ^ n : Kˣ) : K) * x) = _
  rw [Units.val_zpow_eq_zpow_val]
  change localFieldValuation K ((π : K) ^ n * x) = _
  rw [(localFieldValuation K).map_mul, canonical_uniformizer_zpow K π hπ n]
end FourierJacobi.Measure
