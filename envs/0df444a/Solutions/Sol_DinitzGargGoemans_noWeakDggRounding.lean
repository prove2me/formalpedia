-- Prove2me | solution 1 for DinitzGargGoemans.noWeakDggRounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:05:46.201182+00:00
-- url     : https://prove2.me/submissions/c53b74a2-7ebb-42a4-9c92-a3704cb65fa7

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_fractionalCostValue
import Theorems.Thm_DinitzGargGoemans_boundedUnsplittableCost

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution :
    ¬ weakDggProperty counterexampleInstance splitFlow := by
  intro h
  rcases h with ⟨q, hq⟩
  rcases hq with ⟨routing, bound, cost⟩
  have lower := boundedUnsplittableCost q bound
  have upper := cost
  have fractional := fractionalCostValue
  linarith
end DinitzGargGoemans
