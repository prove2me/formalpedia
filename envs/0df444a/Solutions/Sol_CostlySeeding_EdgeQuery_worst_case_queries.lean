-- Prove2me | solution 1 for CostlySeeding.EdgeQuery.worst_case_queries
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:15:38.61229+00:00
-- url     : https://prove2.me/submissions/68ce3c43-3ccc-458d-8795-ab6161b74010

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

namespace D24ProbeQueries
open CostlySeeding.EdgeQuery

lemma neighbors_bound {n : ℕ} (v : Fin n) (tau : ℕ) (X : Finset (Fin n))
    (xs : List (Fin n)) (st : ProbeState n) :
    (probeNeighbors v tau X xs st).queries ≤ st.queries + xs.length := by
  classical
  induction xs generalizing st with
  | nil => simp [probeNeighbors]
  | cons w ws ih =>
    simp only [probeNeighbors]
    split
    · let next := if w ∈ X then { st with queries := st.queries + 1 }
        else { st with vertices := insert w st.vertices, edges := insert s(v, w) st.edges, queries := st.queries + 1 }
      have hn : next.queries = st.queries + 1 := by dsimp [next]; split <;> rfl
      have hi := ih next
      change (probeNeighbors v tau X ws next).queries ≤ st.queries + (w :: ws).length
      simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega

lemma length_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : ProbeSeed n) (X : Finset (Fin n)) (v : Fin n) :
    (orderedNeighbors G s X v).length ≤ n := by
  classical
  unfold orderedNeighbors
  rw [List.length_mergeSort, Finset.length_toList]
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma loop_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tau : ℕ) (s : ProbeSeed n) (fuel : ℕ) (st : ProbeState n) :
    (probeLoop G tau s fuel st).queries ≤ st.queries + fuel * n := by
  classical
  induction fuel generalizing st with
  | zero => simp [probeLoop]
  | succ fuel ih =>
    simp only [probeLoop]
    split
    · rename_i h
      let v := chooseRank (s.pick (Fin.ofNat (n + 1) (n - (fuel + 1))))
        (st.vertices \ st.explored) h
      let X := insert v st.explored
      let start := { st with explored := X }
      let next := probeNeighbors v tau X (orderedNeighbors G s X v) start
      have hne := neighbors_bound v tau X (orderedNeighbors G s X v) start
      have hlen := length_bound G s X v
      have hi := ih next
      change (probeLoop G tau s fuel next).queries ≤ st.queries + (fuel + 1) * n
      change next.queries ≤ st.queries + (orderedNeighbors G s X v).length at hne
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · omega

lemma copy_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Vrho : Finset (Fin n)) (tau : ℕ) (s : ProbeSeed n) :
    (probeCopy G Vrho tau s).2 ≤ n ^ 2 := by
  simpa only [probeCopy, Nat.zero_add, pow_two] using
    loop_bound G tau s n ⟨Vrho, ∅, ∅, 0⟩

end D24ProbeQueries

open CostlySeeding.EdgeQuery
theorem solution (n T tau : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Vrho : Finset (Fin n)) (ss : Fin T → ProbeSeed n) :
    queries G Vrho tau ss ≤ 2 * T * n ^ 2 := by
  classical
  calc
    queries G Vrho tau ss ≤ ∑ _ : Fin T, n ^ 2 :=
      Finset.sum_le_sum fun i _ => D24ProbeQueries.copy_bound G Vrho tau (ss i)
    _ = T * n ^ 2 := by simp
    _ ≤ 2 * T * n ^ 2 := Nat.mul_le_mul_right _ (by omega)

#print axioms solution
