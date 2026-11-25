-- Prove2me | solution 1 for DinitzGargGoemans.fractionalCostValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:54:56.367872+00:00
-- url     : https://prove2.me/submissions/1af01e1d-8f0c-4403-930b-c9bc6448d85d

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_univCommodity
import Theorems.Thm_DinitzGargGoemans_univRouteChoice
import Theorems.Thm_DinitzGargGoemans_univArc
import Theorems.Thm_DinitzGargGoemans_fractionalLoadEqCapacity
attribute [local simp] DinitzGargGoemans.univCommodity
attribute [local simp] DinitzGargGoemans.univRouteChoice
attribute [local simp] DinitzGargGoemans.univArc

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution :
    fractionalCost counterexampleInstance splitFlow = 58 := by
  rw [fractionalCost]
  simp_rw [fractionalLoadEqCapacity]
  simp [counterexampleInstance, arcCost, arcCapacity, Finset.sum_insert]
  norm_num
end DinitzGargGoemans
