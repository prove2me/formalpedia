-- Prove2me | solution 1 for FiniteStraightLineComplexCarrierCompact
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T22:11:47.515326+00:00
-- url     : https://prove2.me/submissions/33322ecf-af89-42bf-bb1e-d21e0e77693a

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

theorem solution
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hA :
      A =
        (V : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2) :
    IsCompact A := by
  rw [hA]
  refine (V.finite_toSet.isCompact).union ?_
  apply isCompact_iUnion
  intro e
  rw [segment_eq_image_lineMap]
  exact (isCompact_Icc.image AffineMap.lineMap_continuous)
