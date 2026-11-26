-- Prove2me | solution 1 for FourierJacobi.Valuations.localFieldValuation_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:48.158255+00:00
-- url     : https://prove2.me/submissions/de54dbe8-3389-45da-ba00-8373d7bef70f

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Lean.Elab.Tactic.Omega
import Definitions.Def_FourierJacobi_Valuations_LocalField

set_option autoImplicit false
noncomputable section
open scoped WithZero
open FourierJacobi FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Valuations
theorem _root_.solution : localFieldValuation K 0 = ⊤ :=
  (localFieldValuation K).map_zero
end FourierJacobi.Valuations
