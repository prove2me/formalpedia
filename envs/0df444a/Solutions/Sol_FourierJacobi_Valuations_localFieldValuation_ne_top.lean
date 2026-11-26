-- Prove2me | solution 1 for FourierJacobi.Valuations.localFieldValuation_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:53.909828+00:00
-- url     : https://prove2.me/submissions/582b9085-4b89-4467-9544-cd9cd7bfe5f4

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
theorem _root_.solution (x : K) :
    localFieldValuation K x ≠ ⊤ ↔ x ≠ 0 :=
  (localFieldValuation K).ne_top_iff
end FourierJacobi.Valuations
