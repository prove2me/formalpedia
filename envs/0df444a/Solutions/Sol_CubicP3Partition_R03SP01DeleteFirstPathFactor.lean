-- Prove2me | solution 1 for CubicP3Partition.R03SP01DeleteFirstPathFactor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:30:36.749458+00:00
-- url     : https://prove2.me/submissions/7bbbc1b1-5ff1-4e01-8319-766073b1c4c4

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

set_option maxHeartbeats 1000000

/--
Candidate path-residue tiling bridge for the frozen non-induced P3 semantics.
An ordered finite path of order 3*k is split into consecutive triples.  The
next two declarations apply this bridge after deleting one vertex from an
order 3*k+1 path order, or two initial vertices from an order 3*k+2 path order.
They are local ingredients for cycle-residue constructions; they do not assert
that a frozen root graph has any particular cycle ordering.
-/
theorem R03SP01PathOrderP3Factor
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


end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : Nat)
    (place : Fin (k * 3 + 1) ≃ V)
    (pathEdge : ∀ i : Fin (k * 3),
      G.Adj (place ⟨i.1, by omega⟩)
        (place ⟨i.1 + 1, by omega⟩)) :
    Nonempty (P3Factor
      (G.induce {v : V | v ≠ place 0})) := by
  letI : Fintype {v : V // v ≠ place 0} := Fintype.ofFinite _
  let f : Fin (k * 3) → {v : V // v ≠ place 0} := fun i =>
    ⟨place ⟨i.1 + 1, Nat.succ_lt_succ i.isLt⟩, by
      intro h
      have hi := place.injective
        (show place ⟨i.1 + 1, Nat.succ_lt_succ i.isLt⟩ = place 0 from h)
      have hi' : i.1 + 1 = 0 := by simpa using congrArg Fin.val hi
      omega⟩
  have hf_inj : Function.Injective f := by
    intro i j h
    apply Fin.ext
    have hplace : place ⟨i.1 + 1, Nat.succ_lt_succ i.isLt⟩ =
        place ⟨j.1 + 1, Nat.succ_lt_succ j.isLt⟩ :=
      congrArg (fun x => x.1) h
    have hfin := place.injective hplace
    have hval : i.1 + 1 = j.1 + 1 := by
      simpa using congrArg Fin.val hfin
    omega
  have hf_surj : Function.Surjective f := by
    intro x
    let i := place.symm x.1
    have hi0 : i.val ≠ 0 := by
      intro hz
      apply x.property
      have hi_eq : i = 0 := Fin.ext hz
      calc
        x.1 = place i := by simp [i]
        _ = place 0 := by rw [hi_eq]
    refine ⟨⟨i.val - 1, by dsimp [i]; omega⟩, ?_⟩
    apply Subtype.ext
    calc
      (f ⟨i.val - 1, by dsimp [i]; omega⟩).1 = place i := by
        apply congrArg place
        apply Fin.ext
        dsimp [f]
        omega
      _ = x.1 := by simp [i]
  let e : Fin (k * 3) ≃ {v : V // v ≠ place 0} :=
    Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  letI : Fintype (↥({v : V | v ≠ place 0} : Set V)) := Fintype.ofFinite _
  apply R03SP01PathOrderP3Factor (G.induce {v : V | v ≠ place 0}) k e
  intro i
  have hadj := pathEdge ⟨i.1 + 1, by omega⟩
  change (G.induce {v : V | v ≠ place 0}).Adj
    (f ⟨i.1, by omega⟩) (f ⟨i.1 + 1, by omega⟩)
  simpa [f, SimpleGraph.induce_adj] using hadj

