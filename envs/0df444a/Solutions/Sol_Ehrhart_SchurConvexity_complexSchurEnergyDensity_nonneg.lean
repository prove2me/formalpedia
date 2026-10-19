-- Prove2me | solution 1 for Ehrhart.SchurConvexity.complexSchurEnergyDensity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/4a7f097a-a1a1-442f-a4c5-cdd7b15e079a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.SchurConvexity
open Set Matrix
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ComplexConjugate ComplexOrder
namespace Ehrhart.SchurConvexity
theorem _root_.solution {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (b : Fin n → ℂ) :
    0 ≤ complexSchurEnergyDensity A b := by
  exact hA.inv.posSemidef.re_dotProduct_nonneg b
end Ehrhart.SchurConvexity
