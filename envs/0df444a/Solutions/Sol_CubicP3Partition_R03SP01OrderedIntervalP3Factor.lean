-- Prove2me | solution 1 for CubicP3Partition.R03SP01OrderedIntervalP3Factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:30:53.643851+00:00
-- url     : https://prove2.me/submissions/8b1f8d05-d5c2-4bd1-82a8-b1a72def4782

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

set_option maxHeartbeats 1000000


end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (n k lo : Nat)
    (e : Fin n ≃ V)
    (hinterval : ∀ i : Fin (k * 3), lo + i.val < n)
    (cycleEdge : ∀ (i : Fin n) (h : i.val + 1 < n),
      G.Adj (e i) (e ⟨i.val + 1, h⟩)) :
    Nonempty (P3Factor (G.induce
      {v : V | ∃ i : Fin (k * 3),
        v = e ⟨lo + i.val, hinterval i⟩})) := by
  classical
  let W : Set V := {v : V | ∃ i : Fin (k * 3),
    v = e ⟨lo + i.val, hinterval i⟩}
  letI : Fintype W := Fintype.ofFinite _
  let f : Fin (k * 3) → W := fun i =>
    ⟨e ⟨lo + i.val, hinterval i⟩, ⟨i, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have he : e ⟨lo + i.val, hinterval i⟩ =
        e ⟨lo + j.val, hinterval j⟩ := congrArg (fun x => x.1) hij
    have hidx := e.injective he
    have hval : lo + i.val = lo + j.val := by
      simpa using congrArg Fin.val hidx
    omega
  have hf_surj : Function.Surjective f := by
    intro x
    rcases x.property with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hi.symm
  let ef : Fin (k * 3) ≃ W := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨{
    blockCount := k
    place := finProdFinEquiv.trans ef
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro b
    let q : Fin (k * 3) := finProdFinEquiv (b, (0 : Fin 3))
    let q1 : Fin (k * 3) := finProdFinEquiv (b, (1 : Fin 3))
    have hq : q.val + 1 < k * 3 := by
      dsimp [q]
      simp [finProdFinEquiv]
      omega
    let qnext : Fin (k * 3) := ⟨q.val + 1, hq⟩
    have hqnext : lo + q.val + 1 < n := by
      have h := hinterval qnext
      dsimp [qnext] at h
      omega
    have hcycle := cycleEdge ⟨lo + q.val, by omega⟩ hqnext
    change (G.induce W).Adj (f q) (f q1)
    rw [show f q = ⟨e ⟨lo + q.val, hinterval q⟩, by
      exact ⟨q, rfl⟩⟩ by rfl]
    rw [show f q1 = ⟨e ⟨lo + q1.val, hinterval q1⟩, by
      exact ⟨q1, rfl⟩⟩ by rfl]
    have hqval : q.val + 1 = q1.val := by
      simp [q, q1, finProdFinEquiv]
      omega
    have hqidx : (⟨lo + q.val + 1, hqnext⟩ : Fin n) =
        ⟨lo + q1.val, hinterval q1⟩ := by
      apply Fin.ext
      simpa [Nat.add_assoc] using congrArg (fun x => lo + x) hqval
    rw [hqidx] at hcycle
    simpa [SimpleGraph.induce_adj] using hcycle
  · intro b
    let q : Fin (k * 3) := finProdFinEquiv (b, (1 : Fin 3))
    let q2 : Fin (k * 3) := finProdFinEquiv (b, (2 : Fin 3))
    have hq : q.val + 1 < k * 3 := by
      dsimp [q]
      simp [finProdFinEquiv]
      omega
    let qnext : Fin (k * 3) := ⟨q.val + 1, hq⟩
    have hqnext : lo + q.val + 1 < n := by
      have h := hinterval qnext
      dsimp [qnext] at h
      omega
    have hcycle := cycleEdge ⟨lo + q.val, by omega⟩ hqnext
    change (G.induce W).Adj (f q) (f q2)
    rw [show f q = ⟨e ⟨lo + q.val, hinterval q⟩, by
      exact ⟨q, rfl⟩⟩ by rfl]
    rw [show f q2 = ⟨e ⟨lo + q2.val, hinterval q2⟩, by
      exact ⟨q2, rfl⟩⟩ by rfl]
    have hqval : q.val + 1 = q2.val := by
      simp [q, q2, finProdFinEquiv]
      omega
    have hqidx : (⟨lo + q.val + 1, hqnext⟩ : Fin n) =
        ⟨lo + q2.val, hinterval q2⟩ := by
      apply Fin.ext
      simpa [Nat.add_assoc] using congrArg (fun x => lo + x) hqval
    rw [hqidx] at hcycle
    simpa [SimpleGraph.induce_adj] using hcycle

