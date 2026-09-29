-- Prove2me | solution 1 for CubicP3Partition.R03SP01ConnectedFin3HasTwoNeighbors
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:46:05.637174+00:00
-- url     : https://prove2.me/submissions/862b0a7e-bb82-48d0-a700-4dfd59e97ac3

import Mathlib

namespace CubicP3Partition


end CubicP3Partition

open CubicP3Partition
theorem solution
    (H : SimpleGraph (Fin 3))
    (hconn : H.Connected) :
    ∃ c a b : Fin 3, a ≠ b ∧ H.Adj c a ∧ H.Adj c b := by
  classical
  by_cases h01 : H.Adj 0 1
  · by_cases h02 : H.Adj 0 2
    · exact ⟨0, 1, 2, by decide, h01, h02⟩
    · by_cases h12 : H.Adj 1 2
      · exact ⟨1, 0, 2, by decide, h01.symm, h12⟩
      · have h20 : ¬ H.Adj 2 0 := by
          intro h
          exact h02 h.symm
        have h21 : ¬ H.Adj 2 1 := by
          intro h
          exact h12 h.symm
        have hiso : H.neighborSet 2 = ∅ := by
          ext x
          fin_cases x <;> simp [SimpleGraph.mem_neighborSet, h20, h21]
        exact False.elim <|
          (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
            (G := H) (u := 2) (v := 0) (by decide) hiso) (hconn 2 0)
  · by_cases h02 : H.Adj 0 2
    · by_cases h12 : H.Adj 1 2
      · exact ⟨2, 0, 1, by decide, h02.symm, h12.symm⟩
      · have h10 : ¬ H.Adj 1 0 := by
          intro h
          exact h01 h.symm
        have hiso : H.neighborSet 1 = ∅ := by
          ext x
          fin_cases x <;> simp [SimpleGraph.mem_neighborSet, h10, h12]
        exact False.elim <|
          (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
            (G := H) (u := 1) (v := 0) (by decide) hiso) (hconn 1 0)
    · by_cases h12 : H.Adj 1 2
      · have hiso : H.neighborSet 0 = ∅ := by
          ext x
          fin_cases x <;> simp [SimpleGraph.mem_neighborSet, h01, h02, h12]
        exact False.elim <|
          (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
            (G := H) (u := 0) (v := 1) (by decide) hiso) (hconn 0 1)
      · have hiso : H.neighborSet 0 = ∅ := by
          ext x
          fin_cases x <;> simp [SimpleGraph.mem_neighborSet, h01, h02, h12]
        exact False.elim <|
          (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
            (G := H) (u := 0) (v := 1) (by decide) hiso) (hconn 0 1)

