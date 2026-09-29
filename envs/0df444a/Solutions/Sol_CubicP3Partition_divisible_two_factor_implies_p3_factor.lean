-- Prove2me | solution 1 for CubicP3Partition.divisible_two_factor_implies_p3_factor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-07T06:14:53.109124+00:00
-- url     : https://prove2.me/submissions/15bc22c7-5902-4189-9919-975c3b77955a

import Mathlib
import Definitions.Def_cubic_p3_partition_models

universe u

namespace CubicP3Partition

open SimpleGraph

/-! ### Triples of vertices -/

section ListInfra

variable {V : Type u}

/-- The three vertices of an ordered triple, as a list. -/
private def tri (t : V × V × V) : List V := [t.1, t.2.1, t.2.2]

/-- The three vertices of an ordered triple, as a map out of `Fin 3`. -/
private def triF (t : V × V × V) : Fin 3 → V := ![t.1, t.2.1, t.2.2]

@[simp] private lemma tri_length (t : V × V × V) : (tri t).length = 3 := rfl

private lemma triF_mem (t : V × V × V) (j : Fin 3) : triF t j ∈ tri t := by
  fin_cases j <;> simp [triF, tri]

private lemma mem_tri (t : V × V × V) (w : V) (hw : w ∈ tri t) : ∃ j : Fin 3, triF t j = w := by
  simp only [tri, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

private lemma triF_injective (t : V × V × V) (h : (tri t).Nodup) :
    Function.Injective (triF t) := by
  simp only [tri, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at h
  intro j j' hjj'
  fin_cases j <;> fin_cases j' <;> simp_all [triF]

/-- Cut a chain of length divisible by three into consecutive triples. -/
private lemma exists_chop {R : V → V → Prop} :
    ∀ (n : ℕ) (L : List V), L.length = n → L.IsChain R → 3 ∣ n →
      ∃ T : List (V × V × V), T.flatMap tri = L ∧
        ∀ t ∈ T, R t.1 t.2.1 ∧ R t.2.1 t.2.2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hlen hch hdvd
    match L with
    | [] => exact ⟨[], rfl, by simp⟩
    | [a] => exfalso; simp at hlen; omega
    | [a, b] => exfalso; simp at hlen; omega
    | a :: b :: c :: r =>
        have hr : r.length = n - 3 := by simp at hlen; omega
        have hlt : n - 3 < n := by simp at hlen; omega
        have hd3 : 3 ∣ (n - 3) := by
          have : n ≥ 3 := by simp at hlen; omega
          omega
        rw [List.isChain_cons_cons, List.isChain_cons_cons] at hch
        obtain ⟨hab, hbc, hrest⟩ := hch
        obtain ⟨T, hT, hTa⟩ := ih (n - 3) hlt r hr hrest.tail hd3
        refine ⟨(a, b, c) :: T, ?_, ?_⟩
        · simp [tri, hT]
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact ⟨hab, hbc⟩
          · exact hTa t ht

end ListInfra



section Graph

variable {V : Type u} [Fintype V] {F : SimpleGraph V}

private lemma neighborSet_ncard (v : V) : (F.neighborSet v).ncard = degree F v := by
  rw [degree, ← Nat.card_coe_set_eq]
  rfl

private lemma isCycles_of_two_regular (hreg : ∀ v, degree F v = 2) : F.IsCycles := by
  intro v _
  rw [neighborSet_ncard, hreg v]

private lemma end_mem_support_tail {x : V} (p : F.Walk x x) (h : 0 < p.length) :
    x ∈ p.support.tail := by
  cases p with
  | nil => simp at h
  | cons hadj q => simp

/-- Each connected component of a 2-regular graph is a cycle, listed as a nodup chain. -/
private lemma component_list (hreg : ∀ v, degree F v = 2) (v : V) :
    ∃ L : List V, L.Nodup ∧ (∀ w, w ∈ L ↔ F.Reachable v w) ∧ L.IsChain F.Adj ∧
      L.length = componentOrder F v := by
  classical
  have hcyc : F.IsCycles := isCycles_of_two_regular hreg
  have hn : (F.neighborSet v).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have h2 := neighborSet_ncard (F := F) v
    rw [hcon, hreg v] at h2
    simp at h2
  have hv : v ∈ (F.connectedComponentMk v).supp := (ConnectedComponent.mem_supp_iff _ _).mpr rfl
  obtain ⟨p, hpc, hpv⟩ :=
    hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hn
  have h3 : 3 ≤ p.length := hpc.three_le_length
  have hsupp : p.support = v :: p.support.tail := p.support_eq_cons
  have hvmem : v ∈ p.support.tail := end_mem_support_tail p (by omega)
  have hsupp_mem : ∀ w, w ∈ p.support ↔ F.Reachable v w := by
    intro w
    rw [← p.mem_verts_toSubgraph, hpv, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hmem : ∀ w, w ∈ p.support.tail ↔ F.Reachable v w := by
    intro w
    rw [← hsupp_mem w]
    constructor
    · intro hw; rw [hsupp]; exact List.mem_cons_of_mem _ hw
    · intro hw
      rw [hsupp] at hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hvmem
      · exact hw
  refine ⟨p.support.tail, hpc.support_nodup, hmem, p.isChain_adj_support.tail, ?_⟩
  rw [← List.toFinset_card_of_nodup hpc.support_nodup, componentOrder,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext w
  simp [List.mem_toFinset, hmem w]

end Graph

section Assemble

variable {V : Type u} [Fintype V] {F : SimpleGraph V}

private lemma exists_triples (hreg : ∀ v, degree F v = 2)
    (hdvd : ∀ v, 3 ∣ componentOrder F v) :
    ∀ (cs : List F.ConnectedComponent), cs.Nodup →
      ∃ T : List (V × V × V),
        (T.flatMap tri).Nodup ∧
        (∀ w, w ∈ T.flatMap tri ↔ F.connectedComponentMk w ∈ cs) ∧
        (∀ t ∈ T, F.Adj t.1 t.2.1 ∧ F.Adj t.2.1 t.2.2) := by
  intro cs
  induction cs with
  | nil => intro _; exact ⟨[], by simp, by simp, by simp⟩
  | cons c cs ih =>
      intro hnd
      obtain ⟨hcnotin, hndcs⟩ := List.nodup_cons.mp hnd
      obtain ⟨T, hTnd, hTmem, hTadj⟩ := ih hndcs
      obtain ⟨v, hv0⟩ := c.exists_rep
      have hv : F.connectedComponentMk v = c := hv0
      obtain ⟨L, hLnd, hLmem, hLch, hLlen⟩ := component_list hreg v
      obtain ⟨T0, hT0, hT0adj⟩ :=
        exists_chop L.length L rfl hLch (by rw [hLlen]; exact hdvd v)
      have key : ∀ w, w ∈ L ↔ F.connectedComponentMk w = c := by
        intro w
        rw [hLmem w, ← hv, ConnectedComponent.eq]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
      refine ⟨T0 ++ T, ?_, ?_, ?_⟩
      · rw [List.flatMap_append, hT0]
        refine hLnd.append hTnd ?_
        intro w hw hw'
        have h1 := (key w).mp hw
        have h2 := (hTmem w).mp hw'
        rw [h1] at h2
        exact hcnotin h2
      · intro w
        rw [List.flatMap_append, hT0, List.mem_append, key w, hTmem w, List.mem_cons]
      · intro t ht
        rcases List.mem_append.mp ht with h | h
        · exact hT0adj t h
        · exact hTadj t h

end Assemble

end CubicP3Partition

open CubicP3Partition

/-- Split every component of a divisible 2-factor into three-vertex paths. -/
theorem solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (h : HasDivisibleTwoFactor G) : Nonempty (P3Factor G) := by
  classical
  obtain ⟨F, ⟨hFle, hFdeg⟩, hdvd⟩ := h
  obtain ⟨T, hnd, hmem, hadj⟩ :=
    exists_triples hFdeg hdvd (Finset.univ : Finset F.ConnectedComponent).toList
      (Finset.nodup_toList _)
  have hcov : ∀ w : V, w ∈ T.flatMap tri := fun w => (hmem w).mpr (by simp)
  obtain ⟨hnd1, hnd2⟩ := List.nodup_flatMap.mp hnd
  have hdisj : ∀ (i j : ℕ) (hi : i < T.length) (hj : j < T.length), i < j →
      (tri (T[i]'hi)).Disjoint (tri (T[j]'hj)) := by
    have := List.pairwise_iff_getElem.mp hnd2
    simpa [Function.onFun] using this
  set f : Fin T.length × Fin 3 → V := fun q => triF (T[q.1.val]'q.1.isLt) q.2 with hf
  have hinj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hq
    simp only [hf] at hq
    have hmi : triF (T[i.val]'i.isLt) j ∈ tri (T[i.val]'i.isLt) := triF_mem _ _
    have hmi' : triF (T[i'.val]'i'.isLt) j' ∈ tri (T[i'.val]'i'.isLt) := triF_mem _ _
    have hA : triF (T[i.val]'i.isLt) j ∈ tri (T[i'.val]'i'.isLt) := by rw [hq]; exact hmi'
    have hB : triF (T[i'.val]'i'.isLt) j' ∈ tri (T[i.val]'i.isLt) := by rw [← hq]; exact hmi
    have hii : i.val = i'.val := by
      by_contra hne
      rcases Nat.lt_or_ge i.val i'.val with hlt | hge
      · exact hdisj i.val i'.val i.isLt i'.isLt hlt hmi hA
      · have hlt' : i'.val < i.val := by omega
        exact hdisj i'.val i.val i'.isLt i.isLt hlt' hmi' hB
    have hie : i = i' := Fin.ext hii
    subst hie
    have hjj := triF_injective _ (hnd1 _ (List.getElem_mem i.isLt)) hq
    simp [hjj]
  have hsurj : Function.Surjective f := by
    intro w
    have hw := hcov w
    rw [List.mem_flatMap] at hw
    obtain ⟨t, htT, hwt⟩ := hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem htT
    obtain ⟨j, hj⟩ := mem_tri _ w hwt
    exact ⟨(⟨i, hi⟩, j), hj⟩
  have e0 : ∀ i : Fin T.length,
      (Equiv.ofBijective f ⟨hinj, hsurj⟩) (i, 0) = (T[i.val]'i.isLt).1 := by
    intro i; simp [hf, triF]
  have e1 : ∀ i : Fin T.length,
      (Equiv.ofBijective f ⟨hinj, hsurj⟩) (i, 1) = (T[i.val]'i.isLt).2.1 := by
    intro i; simp [hf, triF]
  have e2 : ∀ i : Fin T.length,
      (Equiv.ofBijective f ⟨hinj, hsurj⟩) (i, 2) = (T[i.val]'i.isLt).2.2 := by
    intro i; simp [hf, triF]
  refine ⟨{ blockCount := T.length
            place := Equiv.ofBijective f ⟨hinj, hsurj⟩
            edge01 := fun i => ?_
            edge12 := fun i => ?_ }⟩
  · rw [e0 i, e1 i]
    exact hFle (hadj _ (List.getElem_mem i.isLt)).1
  · rw [e1 i, e2 i]
    exact hFle (hadj _ (List.getElem_mem i.isLt)).2

