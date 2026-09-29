-- Prove2me | solution 1 for Erdos146.hammingBall_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:33:49.201501+00:00
-- url     : https://prove2.me/submissions/269eed0d-d9c7-4dad-8e95-268235bcf434

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem boundedDifferenceSets_card (dimension radius : ℕ) :
    (boundedDifferenceSets dimension radius).card =
      ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by
  classical
  have hmaps :
      ((boundedDifferenceSets dimension radius :
        Finset (Finset (Fin dimension))) : Set (Finset (Fin dimension))).MapsTo
        Finset.card (Finset.range (radius + 1)) := by
    intro S hS
    have hmembership : S ∈
        (((Finset.univ : Finset (Fin dimension)).powerset).filter
          (fun coordinates => coordinates.card ≤ radius)) := by
      exact Finset.mem_coe.mp hS
    have hcard := (Finset.mem_filter.mp hmembership).2
    exact Finset.mem_range.mpr (by omega)
  calc
    (boundedDifferenceSets dimension radius).card =
        ∑ d ∈ Finset.range (radius + 1),
          ((boundedDifferenceSets dimension radius).filter
            (fun coordinates => coordinates.card = d)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdle : d ≤ radius := by
        have := Finset.mem_range.mp hd
        omega
      have hfiber :
          (boundedDifferenceSets dimension radius).filter
            (fun coordinates => coordinates.card = d) =
          (Finset.univ : Finset (Fin dimension)).powersetCard d := by
        ext coordinates
        simp only [boundedDifferenceSets, Finset.mem_filter,
          Finset.mem_powerset, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨hsubset, _⟩, hcard⟩
          exact ⟨hsubset, hcard⟩
        · rintro ⟨hsubset, hcard⟩
          exact ⟨⟨hsubset, by omega⟩, hcard⟩
      rw [hfiber, Finset.card_powersetCard]
      simp

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution (dimension radius : ℕ)
    (u : HammingWord dimension) :
    (hammingBall dimension radius u).card =
      ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by
  calc
    (hammingBall dimension radius u).card =
        Fintype.card ↥(hammingBall dimension radius u) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card ↥(boundedDifferenceSets dimension radius) :=
      Fintype.card_congr (hammingBallEquiv dimension radius u)
    _ = (boundedDifferenceSets dimension radius).card :=
      Fintype.card_coe _
    _ = ∑ d ∈ Finset.range (radius + 1), dimension.choose d :=
      boundedDifferenceSets_card dimension radius
