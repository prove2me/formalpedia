-- Prove2me | solution 1 for FourierJacobi.Valuations.localFieldValuation_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:28.94823+00:00
-- url     : https://prove2.me/submissions/569bedb9-1737-41ca-9b84-30fd8b673cfa

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Lean.Elab.Tactic.Omega
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Theorems.Thm_FourierJacobi_Valuations_discreteValuation_surjective
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero

set_option autoImplicit false
noncomputable section
open scoped WithZero
open FourierJacobi FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Valuations
theorem _root_.solution : Function.Surjective (localFieldValuation K) := by
  intro n
  induction n using WithTop.recTopCoe with
  | top => exact ⟨0, localFieldValuation_zero K⟩
  | coe n =>
    obtain ⟨x, hx⟩ := discreteValuation_surjective K (WithZero.exp (-n))
    refine ⟨x, ?_⟩
    change extendedNegLog (discreteValuation K x) = (n : WithTop ℤ)
    rw [hx]
    change ((-(-n) : ℤ) : WithTop ℤ) = (n : WithTop ℤ)
    rw [neg_neg]
end FourierJacobi.Valuations
