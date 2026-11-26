-- Prove2me | solution 1 for FourierJacobi.Valuations.discreteValuation_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:51.391278+00:00
-- url     : https://prove2.me/submissions/2898da53-f86f-4409-8396-a27d55f29eb8

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
theorem _root_.solution : Function.Surjective (discreteValuation K) :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).surjective.comp
    ValuativeRel.valuation_surjective
end FourierJacobi.Valuations
