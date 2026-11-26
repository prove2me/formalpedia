-- Prove2me | solution 1 for FourierJacobi.Valuations.localFieldValuation_nonnegative_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:13.003361+00:00
-- url     : https://prove2.me/submissions/3a3fe3be-3f58-4a99-a0e6-1fbd9f20ba8c

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Lean.Elab.Tactic.Omega
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Theorems.Thm_FourierJacobi_Valuations_extendedNegLog_nonnegative

set_option autoImplicit false
noncomputable section
open scoped WithZero
open FourierJacobi FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Valuations
theorem _root_.solution (x : K) :
    0 ≤ localFieldValuation K x ↔ x ∈ (ValuativeRel.valuation K).integer := by
  change 0 ≤ extendedNegLog (discreteValuation K x) ↔ ValuativeRel.valuation K x ≤ 1
  rw [extendedNegLog_nonnegative]
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
    (ValuativeRel.valuation K x) ≤ 1 ↔ _
  rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)]
  exact map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
end FourierJacobi.Valuations
