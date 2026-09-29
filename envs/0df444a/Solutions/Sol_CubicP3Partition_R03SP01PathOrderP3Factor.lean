-- Prove2me | solution 1 for CubicP3Partition.R03SP01PathOrderP3Factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:30:40.7061+00:00
-- url     : https://prove2.me/submissions/bbfe6d67-eb65-43a7-a4b4-d0a6e6f2f35b

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

set_option maxHeartbeats 1000000


end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : Nat)
    (place : Fin (k * 3) ≃ V)
    (pathEdge : ∀ i : Fin (k * 3 - 1),
      G.Adj (place ⟨i.1, by omega⟩)
        (place ⟨i.1 + 1, by omega⟩)) :
    Nonempty (P3Factor G) := by
  refine ⟨{
    blockCount := k
    place := finProdFinEquiv.trans place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    have hi : 3 * (i : Nat) < k * 3 - 1 := by omega
    have hadj := pathEdge ⟨3 * (i : Nat), hi⟩
    simpa [finProdFinEquiv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hadj
  · intro i
    have hi : 1 + 3 * (i : Nat) < k * 3 - 1 := by omega
    have hadj := pathEdge ⟨1 + 3 * (i : Nat), hi⟩
    simpa [finProdFinEquiv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      show (1 + 3 * (i : Nat)) + 1 = 2 + 3 * (i : Nat) by omega] using hadj

