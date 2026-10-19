-- Prove2me | solution 1 for CompactnessConjecture.extremalScale_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/dc91420f-3e35-4e0e-8aa0-421be599e5d5

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Topology
namespace CompactnessConjecture
theorem _root_.solution (n : ℕ) :
    0 ≤ extremalScale n := by
  unfold extremalScale
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _
end CompactnessConjecture
