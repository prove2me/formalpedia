-- Prove2me | solution 1 for CubicP3Partition.R03SP01V2P3FactorFiniteSigma
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:13:11.294328+00:00
-- url     : https://prove2.me/submissions/6e6b557a-9091-4e3c-8a37-879febef4359

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_de73be8e06_r03_sp01_cyclic_residual_assembly_candidate_v1

/-!
# Cyclic residue suffix and residual assembly bridge

Candidate-only formalization for `problem:opg-46613-p3-partition`.
A cyclic component of order `3*k+r` is reduced to its suffix of order
`3*k`, leaving a prefix of `r` exceptional vertices.  If a supplied factor
covers the exceptional vertices across all components, the suffix factors and
that residual factor assemble into an ambient factor.

This source deliberately treats the residual factor, the component
presentation, and all ambient edge inclusions as hypotheses.  It does not
prove that a cubic 3-connected graph supplies them.
-/

namespace CubicP3Partition

universe u v
set_option maxHeartbeats 1000000

theorem R03SP01V2OrderedSuffixP3Factor
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (n k lo : Nat)
    (e : Fin n ≃ V)
    (hinterval : ∀ i : Fin (k * 3), lo + i.val < n)
    (successorEdge : ∀ (i : Fin n) (h : i.val + 1 < n),
      G.Adj (e i) (e ⟨i.val + 1, h⟩)) :
    Nonempty (P3Factor (G.induce (R03SP01V2SuffixSet n k lo e))) := by
  classical
  let W : Set V := R03SP01V2SuffixSet n k lo e
  letI : Fintype W := Fintype.ofFinite _
  let f : Fin (k * 3) → W := fun i =>
    ⟨e ⟨lo + i.val, hinterval i⟩, ⟨i, hinterval i, rfl⟩⟩
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
    rcases x.property with ⟨i, h, hi⟩
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
    have hadj := successorEdge ⟨lo + q.val, by omega⟩ hqnext
    change (G.induce W).Adj (f q) (f q1)
    rw [show f q = ⟨e ⟨lo + q.val, hinterval q⟩, by
      exact ⟨q, hinterval q, rfl⟩⟩ by rfl]
    rw [show f q1 = ⟨e ⟨lo + q1.val, hinterval q1⟩, by
      exact ⟨q1, hinterval q1, rfl⟩⟩ by rfl]
    have hqval : q.val + 1 = q1.val := by
      simp [q, q1, finProdFinEquiv]
      omega
    have hqidx : (⟨lo + q.val + 1, hqnext⟩ : Fin n) =
        ⟨lo + q1.val, hinterval q1⟩ := by
      apply Fin.ext
      simpa [Nat.add_assoc] using congrArg (fun x => lo + x) hqval
    rw [hqidx] at hadj
    simpa [SimpleGraph.induce_adj] using hadj
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
    have hadj := successorEdge ⟨lo + q.val, by omega⟩ hqnext
    change (G.induce W).Adj (f q) (f q2)
    rw [show f q = ⟨e ⟨lo + q.val, hinterval q⟩, by
      exact ⟨q, hinterval q, rfl⟩⟩ by rfl]
    rw [show f q2 = ⟨e ⟨lo + q2.val, hinterval q2⟩, by
      exact ⟨q2, hinterval q2, rfl⟩⟩ by rfl]
    have hqval : q.val + 1 = q2.val := by
      simp [q, q2, finProdFinEquiv]
      omega
    have hqidx : (⟨lo + q.val + 1, hqnext⟩ : Fin n) =
        ⟨lo + q2.val, hinterval q2⟩ := by
      apply Fin.ext
      simpa [Nat.add_assoc] using congrArg (fun x => lo + x) hqval
    rw [hqidx] at hadj
    simpa [SimpleGraph.induce_adj] using hadj

/-- The cyclic suffix bridge with the component order written as `3*k+r`.
Only non-wrapping successor edges are used, so the prefix of length `r` is
precisely the residual interface. -/
theorem R03SP01V2CyclicSuffixP3Factor
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (n k r : Nat)
    (e : Fin n ≃ V)
    (hsize : n = k * 3 + r)
    (successorEdge : ∀ (i : Fin n) (h : i.val + 1 < n),
      G.Adj (e i) (e ⟨i.val + 1, h⟩)) :
    Nonempty (P3Factor (G.induce (R03SP01V2SuffixSet n k r e))) := by
  apply R03SP01V2OrderedSuffixP3Factor G n k r e
  · intro i
    rw [hsize]
    omega
  · exact successorEdge

end CubicP3Partition

open CubicP3Partition
universe u v
theorem solution
    {ι : Type u} [Fintype ι]
    {V : ι → Type v} [∀ i, Fintype (V i)]
    (Gi : ∀ i, SimpleGraph (V i))
    (G : SimpleGraph (Σ i, V i))
    (p : ∀ i, P3Factor (Gi i))
    (hAdj : ∀ (i : ι) {x y : V i}, (Gi i).Adj x y →
      G.Adj ⟨i, x⟩ ⟨i, y⟩) :
    Nonempty (P3Factor G) := by
  let total : Nat := ∑ i, (p i).blockCount
  let cardEq : Fintype.card (Σ i, Fin (p i).blockCount) = total := by
    simp [total, Fintype.card_sigma]
  let blockEquiv : Fin total ≃ (Σ i, Fin (p i).blockCount) :=
    (Equiv.cast (congrArg Fin cardEq.symm)).trans
      (Fintype.equivFin (Σ i, Fin (p i).blockCount)).symm
  let sourceEquiv : (Fin total × Fin 3) ≃
      (Σ i, (Fin (p i).blockCount × Fin 3)) :=
    (blockEquiv.prodCongr (Equiv.refl (Fin 3))).trans
      R03SP01V2SigmaProdDistrib
  let placeEquiv : (Σ i, (Fin (p i).blockCount × Fin 3)) ≃
      (Σ i, V i) :=
    Equiv.sigmaCongrRight (fun i => (p i).place)
  let place : (Fin total × Fin 3) ≃ (Σ i, V i) :=
    sourceEquiv.trans placeEquiv
  refine ⟨{
    blockCount := total
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro j
    let z : (Σ i, Fin (p i).blockCount) := blockEquiv j
    have hlocal : (Gi z.1).Adj
        ((p z.1).place (z.2, (0 : Fin 3)))
        ((p z.1).place (z.2, (1 : Fin 3))) :=
      (p z.1).edge01 z.2
    have hamb := hAdj z.1 hlocal
    simpa [place, placeEquiv, sourceEquiv, R03SP01V2SigmaProdDistrib, z] using hamb
  · intro j
    let z : (Σ i, Fin (p i).blockCount) := blockEquiv j
    have hlocal : (Gi z.1).Adj
        ((p z.1).place (z.2, (1 : Fin 3)))
        ((p z.1).place (z.2, (2 : Fin 3))) :=
      (p z.1).edge12 z.2
    have hamb := hAdj z.1 hlocal
    simpa [place, placeEquiv, sourceEquiv, R03SP01V2SigmaProdDistrib, z] using hamb
