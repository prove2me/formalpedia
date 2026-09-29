-- Prove2me | solution 1 for CubicP3Partition.hamiltonian_path_p3Factor_candidate
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:13:23.489225+00:00
-- url     : https://prove2.me/submissions/cdf8677c-6072-4e9f-80ab-c6db01b58706

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

noncomputable section


end
end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsHamiltonian)
    (hOrder : 3 ∣ Fintype.card V) : Nonempty (P3Factor G) := by
  classical
  let k : Nat := Classical.choose hOrder
  have hk : Fintype.card V = 3 * k := Classical.choose_spec hOrder
  have hlen : p.support.length = k * 3 := by
    calc
      p.support.length = Fintype.card V := hp.length_support
      _ = 3 * k := hk
      _ = k * 3 := Nat.mul_comm _ _
  let place : (Fin k × Fin 3) ≃ V :=
    finProdFinEquiv.trans ((finCongr hlen.symm).trans hp.getVertEquiv)
  refine ⟨{ blockCount := k, place := place, edge01 := ?_, edge12 := ?_ }⟩
  · intro i
    have hi : 3 * (i : Nat) < p.length := by
      rw [hp.length_eq, hk]
      omega
    have hadj := p.adj_getVert_succ hi
    simpa [place, finProdFinEquiv, finCongr,
      SimpleGraph.Walk.IsHamiltonian.getVertEquiv, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hadj
  · intro i
    have hi : 1 + 3 * (i : Nat) < p.length := by
      rw [hp.length_eq, hk]
      omega
    have hadj := p.adj_getVert_succ hi
    have hidx : 1 + 3 * (i : Nat) + 1 = 2 + 3 * (i : Nat) := by
      omega
    have hadj' : G.Adj (p.getVert (1 + 3 * (i : Nat)))
        (p.getVert (2 + 3 * (i : Nat))) := by
      rw [← hidx]
      exact hadj
    simpa [place, finProdFinEquiv, finCongr,
      SimpleGraph.Walk.IsHamiltonian.getVertEquiv, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hadj'

