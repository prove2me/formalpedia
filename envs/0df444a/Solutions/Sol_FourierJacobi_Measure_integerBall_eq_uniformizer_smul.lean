-- Prove2me | solution 1 for FourierJacobi.Measure.integerBall_eq_uniformizer_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:46.838021+00:00
-- url     : https://prove2.me/submissions/42d78791-82d0-4f77-87d9-11f417b6348f

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Theorems.Thm_FourierJacobi_Measure_canonicalValuation_uniformizer_smul
import Theorems.Thm_FourierJacobi_Measure_coe_le_iff_neg_add_nonnegative
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_nonnegative_iff


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
    integerBall K n = (canonicalUniformizerUnit K π hπ ^ n) • (𝒪[K] : Set K) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change (n : WithTop ℤ) ≤ localFieldValuation K x ↔
    (canonicalUniformizerUnit K π hπ ^ n)⁻¹ • x ∈ (valuation K).integer
  rw [← localFieldValuation_nonnegative_iff, ← zpow_neg,
    canonicalValuation_uniformizer_smul]
  exact coe_le_iff_neg_add_nonnegative n _
end FourierJacobi.Measure
