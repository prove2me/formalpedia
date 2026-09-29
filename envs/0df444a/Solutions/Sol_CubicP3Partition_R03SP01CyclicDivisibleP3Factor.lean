-- Prove2me | solution 1 for CubicP3Partition.R03SP01CyclicDivisibleP3Factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:30:30.919027+00:00
-- url     : https://prove2.me/submissions/76ff0364-5565-40fa-afe0-10163c2220f0

import Definitions.Def_cubic_p3_partition_models
namespace CubicP3Partition
universe u
set_option maxHeartbeats 1000000


end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {A : Type u} [Fintype A]
    (G : SimpleGraph A) (k : Nat) (hpos : 0 < k * 3)
    (e : Fin (k * 3) ≃ A)
    (cycle : ∀ i : Fin (k * 3),
      G.Adj (e i)
        (e ⟨(i.val + 1) % (k * 3), Nat.mod_lt _ hpos⟩)) :
    Nonempty (P3Factor G) := by
  refine ⟨{
    blockCount := k
    place := finProdFinEquiv.trans e
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    have h := cycle (finProdFinEquiv (i, (0 : Fin 3)))
    have hn : (k * 3) ≠ 0 := by omega
    have hidx : (⟨((finProdFinEquiv (i, (0 : Fin 3))).val + 1) % (k * 3),
        Nat.mod_lt _ hpos⟩ : Fin (k * 3)) = finProdFinEquiv (i, (1 : Fin 3)) := by
      apply Fin.ext
      dsimp [finProdFinEquiv]
      simp only [zero_add]
      have hlt : 3 * i.val + 1 < k * 3 := by omega
      calc
        (3 * i.val + 1) % (k * 3) = 3 * i.val + 1 := Nat.mod_eq_of_lt hlt
        _ = 1 + 3 * i.val := by omega
    rw [hidx] at h
    exact h
  · intro i
    have h := cycle (finProdFinEquiv (i, (1 : Fin 3)))
    have hn : (k * 3) ≠ 0 := by omega
    have hidx : (⟨((finProdFinEquiv (i, (1 : Fin 3))).val + 1) % (k * 3),
        Nat.mod_lt _ hpos⟩ : Fin (k * 3)) = finProdFinEquiv (i, (2 : Fin 3)) := by
      apply Fin.ext
      dsimp [finProdFinEquiv]
      have hlt : 1 + 3 * i.val + 1 < k * 3 := by omega
      calc
        (1 + 3 * i.val + 1) % (k * 3) = 1 + 3 * i.val + 1 := Nat.mod_eq_of_lt hlt
        _ = 2 + 3 * i.val := by omega
    rw [hidx] at h
    exact h

