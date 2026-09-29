-- Prove2me | solution 1 for Erdos180.symplecticPoint_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:36:50.417556+00:00
-- url     : https://prove2.me/submissions/68131cb5-694f-4102-bb14-da7c7dc83396

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution [Finite K] :
    Nat.card (SymplecticPoint K) =
      (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  calc
    Nat.card (SymplecticPoint K) =
        Nat.card (Projectivization K (SymplecticVector K)) :=
      Nat.card_congr
        (Projectivization.equivSubmodule K (SymplecticVector K)).symm
    _ = ∑ i ∈ Finset.range 4, (Nat.card K) ^ i :=
      Projectivization.card_of_finrank K (SymplecticVector K) (by simp)
    _ = (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
      simp [Finset.sum_range_succ]
      ring
