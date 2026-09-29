-- Prove2me | solution 1 for CubicP3Partition.cubic_triangle_residual_two_connected
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-16T09:23:50.253094+00:00
-- url     : https://prove2.me/submissions/bd5d5ca6-1b75-4110-9089-d83fe83a849b

import Mathlib
import Definitions.Def_cubic_p3_partition_models

/-!
Candidate-only formalization of a q=3 structural reduction.
Here T is a three-vertex deleted set.  The theorem isolates the graph-specific
fact needed for a triangle deletion: every t in T has at most one neighbor
outside T.  Under the project's two-vertex-deletion connectivity axiom, the
residual after additionally deleting any residual vertex is connected.
No P3-factor conclusion is asserted.
-/

namespace R03SP06

open CubicP3Partition

variable {V : Type} [Fintype V] [DecidableEq V]

lemma closed_side_induced_not_connected
    {G : SimpleGraph V} {A B S : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hAS : Disjoint A S) (hBS : Disjoint B S)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ S) :
    ¬ (G.induce {v : V | v ∉ S}).Connected := by
  intro hconn
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have haS : a ∉ S := by
    intro ha'
    exact (Finset.disjoint_left.1 hAS) ha ha'
  have hbS : b ∉ S := by
    intro hb'
    exact (Finset.disjoint_left.1 hBS) hb hb'
  let H : SimpleGraph {v : V // v ∉ S} := G.induce {v : V | v ∉ S}
  have hreach : H.Reachable ⟨a, haS⟩ ⟨b, hbS⟩ := by
    exact (by assumption : (G.induce {v : V | v ∉ S}).Connected).preconnected
      ⟨a, haS⟩ ⟨b, hbS⟩
  have stay : ∀ {u v : {v : V // v ∉ S}}, H.Walk u v → u.1 ∈ A → v.1 ∈ A := by
    intro u v p
    induction p with
    | nil =>
        intro hu
        exact hu
    | @cons u w v hadj tail ih =>
        intro hu
        have hwAS : w.1 ∈ A ∪ S := hclosed hu hadj
        have hwAorS : w.1 ∈ A ∨ w.1 ∈ S := by
          simpa [Finset.mem_union] using hwAS
        have hwA : w.1 ∈ A := by
          rcases hwAorS with hwA | hwS
          · exact hwA
          · exact False.elim (w.2 hwS)
        exact ih hwA
  have hbA : b ∈ A := stay hreach.some ha
  exact (Finset.disjoint_left.1 hAB) hbA hb

lemma two_vertex_connectivity_forbids_closed_side
    {G : SimpleGraph V}
    (h2 : ∀ S : Finset V, S.card ≤ 2 →
      (G.induce {v : V | v ∉ S}).Connected)
    {A B S : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hAS : Disjoint A S) (hBS : Disjoint B S)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ S)
    (hScard : S.card ≤ 2) : False := by
  exact (closed_side_induced_not_connected hA hB hAB hAS hBS hclosed)
    (h2 S hScard)

/-- Every side of a residual cut must use at least two vertices of the
three-vertex deleted set.  A side is closed after the residual cut vertex x
and the deleted set T are removed. -/
lemma q3_side_port_card_at_least_two
    {G : SimpleGraph V} [DecidableRel G.Adj] {A B T : Finset V} {x : V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B)
    (hAT : Disjoint A T) (hBT : Disjoint B T)
    (hxA : x ∉ A) (hxB : x ∉ B) (hxT : x ∉ T)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ T ∪ {x})
    (hT : T.card = 3)
    (h2 : ∀ S : Finset V, S.card ≤ 2 →
      (G.induce {v : V | v ∉ S}).Connected) :
    2 ≤ (T.filter (fun t => ∃ u ∈ A, G.Adj u t)).card := by
  classical
  by_contra hgood
  let P : Finset V := T.filter (fun t => ∃ u ∈ A, G.Adj u t)
  have hP : P.card ≤ 1 := by
    simpa [P] using (show (T.filter (fun t => ∃ u ∈ A, G.Adj u t)).card < 2 by omega)
  obtain ⟨t0, ht0⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  letI : Nonempty V := ⟨t0⟩
  have hex : ∃ t, t ∈ T ∧ P ⊆ ({t} : Finset V) := by
    by_cases hPne : P.Nonempty
    · obtain ⟨u, huP⟩ := hPne
      obtain ⟨t, htP⟩ := Finset.card_le_one_iff_subset_singleton.mp hP
      have hut : u = t := Finset.mem_singleton.mp (htP huP)
      subst u
      refine ⟨t, ?_, htP⟩
      have htP' : t ∈ T.filter (fun z => ∃ y ∈ A, G.Adj y z) := by
        simpa [P] using huP
      exact (Finset.mem_filter.mp htP').1
    · have hPempty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPne
      refine ⟨t0, ht0, ?_⟩
      simp [hPempty]
  obtain ⟨t, htT, htP⟩ := hex
  let S : Finset V := {x, t}
  have hAS : Disjoint A S := by
    refine Finset.disjoint_left.mpr ?_
    intro u huA huS
    have huS' : u = x ∨ u = t := by simpa [S] using huS
    rcases huS' with rfl | rfl
    · exact hxA huA
    · exact (Finset.disjoint_left.1 hAT) huA htT
  have hBS : Disjoint B S := by
    refine Finset.disjoint_left.mpr ?_
    intro u huB huS
    have huS' : u = x ∨ u = t := by simpa [S] using huS
    rcases huS' with rfl | rfl
    · exact hxB huB
    · exact (Finset.disjoint_left.1 hBT) huB htT
  have hclosedS : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ S := by
    intro u v hu huv
    have huvAT : v ∈ A ∪ T ∪ {x} := hclosed hu huv
    rcases (by simpa [Finset.mem_union] using huvAT :
        v = x ∨ v ∈ A ∨ v ∈ T) with hvx | hvA | hvT
    · simp [S, hvx]
    · exact Finset.mem_union_left S hvA
    · by_cases hvP : v ∈ P
      · have hvt : v = t := by
          have := htP hvP
          simpa using this
        subst v
        exact Finset.mem_union_right A
          (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
      · have hno : ¬ ∃ z ∈ A, G.Adj z v := by
          intro hz
          apply hvP
          have hvP' : v ∈ T.filter (fun z => ∃ y ∈ A, G.Adj y z) :=
            Finset.mem_filter.mpr ⟨hvT, hz⟩
          simpa [P] using hvP'
        exact False.elim (hno ⟨u, hu, huv⟩)
  have hScard : S.card ≤ 2 := by
    change ({x, t} : Finset V).card ≤ 2
    simpa using (Finset.card_insert_le x ({t} : Finset V))
  exact two_vertex_connectivity_forbids_closed_side h2 hA hB hAB hAS hBS hclosedS hScard

/-- Two disjoint port sets of size at least two cannot fit in a
three-vertex deleted set. -/
lemma q3_two_side_port_budget_impossible
    {S P Q : Finset V}
    (hS : S.card = 3)
    (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card)
    (hPQ : Disjoint P Q) (hsubset : P ∪ Q ⊆ S) : False := by
  have hunion : (P ∪ Q).card = P.card + Q.card :=
    Finset.card_union_of_disjoint hPQ
  have hle : (P ∪ Q).card ≤ S.card := Finset.card_le_card hsubset
  rw [hS, hunion] at hle
  omega

/-- Conditional q=3 cut-free theorem.  The `hport` premise is the one-external
neighbor property of a triangle in a cubic simple graph. -/
theorem triangle_residual_no_cut_vertex
    {G : SimpleGraph V}
    {T : Finset V} {x : V}
    (hT : T.card = 3)
    (hxT : x ∉ T)
    (hres : ∃ v : V, v ∉ T ∧ v ≠ x)
    (h2 : ∀ S : Finset V, S.card ≤ 2 →
      (G.induce {v : V | v ∉ S}).Connected)
    (hport : ∀ ⦃t u v : V⦄, t ∈ T → u ∉ T → v ∉ T →
      G.Adj t u → G.Adj t v → u = v) :
    (G.induce {v : V | v ∉ T ∧ v ≠ x}).Connected := by
  classical
  let K : SimpleGraph {v : V // v ∉ T ∧ v ≠ x} :=
    G.induce {v : V | v ∉ T ∧ v ≠ x}
  have hnonempty : Nonempty {v : V // v ∉ T ∧ v ≠ x} := by
    obtain ⟨v, hvT, hvx⟩ := hres
    exact ⟨⟨v, hvT, hvx⟩⟩
  have hpre : K.Preconnected := by
    intro p q
    by_contra hpq
    let A : Finset V := Finset.univ.filter
      (fun z : V => ∃ hz : z ∉ T ∧ z ≠ x,
        K.Reachable p ⟨z, hz⟩)
    let B : Finset V := Finset.univ.filter
      (fun z : V => ∃ hz : z ∉ T ∧ z ≠ x,
        K.Reachable q ⟨z, hz⟩)
    have hpA : p.1 ∈ A := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact ⟨p.2, SimpleGraph.Reachable.refl p⟩
    have hqB : q.1 ∈ B := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact ⟨q.2, SimpleGraph.Reachable.refl q⟩
    have hA : A.Nonempty := ⟨p.1, hpA⟩
    have hB : B.Nonempty := ⟨q.1, hqB⟩
    have hAB : Disjoint A B := by
      refine Finset.disjoint_left.mpr ?_
      intro z hzA hzB
      obtain ⟨hzA', hpz⟩ := (Finset.mem_filter.mp hzA).2
      obtain ⟨hzB', hqz⟩ := (Finset.mem_filter.mp hzB).2
      have hpq' : K.Reachable p q := hpz.trans hqz.symm
      exact hpq hpq'
    have hAT : Disjoint A T := by
      refine Finset.disjoint_left.mpr ?_
      intro z hzA hzT
      exact (Finset.mem_filter.mp hzA).2.choose.1 hzT
    have hBT : Disjoint B T := by
      refine Finset.disjoint_left.mpr ?_
      intro z hzB hzT
      exact (Finset.mem_filter.mp hzB).2.choose.1 hzT
    have hxA : x ∉ A := by
      intro hxA'
      exact (Finset.mem_filter.mp hxA').2.choose.2 rfl
    have hxB : x ∉ B := by
      intro hxB'
      exact (Finset.mem_filter.mp hxB').2.choose.2 rfl
    have hclosedA : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v →
        v ∈ A ∪ T ∪ {x} := by
      intro u v hu huv
      obtain ⟨hu', hpu⟩ := (Finset.mem_filter.mp hu).2
      by_cases hvT : v ∈ T
      · exact Finset.mem_union_left {x} (Finset.mem_union_right A hvT)
      by_cases hvx : v = x
      · exact Finset.mem_union_right (A ∪ T) (Finset.mem_singleton.mpr hvx)
      have hv' : v ∉ T ∧ v ≠ x := ⟨hvT, hvx⟩
      have huvK : K.Adj ⟨u, hu'⟩ ⟨v, hv'⟩ := huv
      have hpv : K.Reachable p ⟨v, hv'⟩ := hpu.trans huvK.reachable
      exact Finset.mem_union_left {x} (Finset.mem_union_left T
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hv', hpv⟩⟩))
    have hclosedB : ∀ ⦃u v : V⦄, u ∈ B → G.Adj u v →
        v ∈ B ∪ T ∪ {x} := by
      intro u v hu huv
      obtain ⟨hu', hqu⟩ := (Finset.mem_filter.mp hu).2
      by_cases hvT : v ∈ T
      · exact Finset.mem_union_left {x} (Finset.mem_union_right B hvT)
      by_cases hvx : v = x
      · exact Finset.mem_union_right (B ∪ T) (Finset.mem_singleton.mpr hvx)
      have hv' : v ∉ T ∧ v ≠ x := ⟨hvT, hvx⟩
      have huvK : K.Adj ⟨u, hu'⟩ ⟨v, hv'⟩ := huv
      have hqv : K.Reachable q ⟨v, hv'⟩ := hqu.trans huvK.reachable
      exact Finset.mem_union_left {x} (Finset.mem_union_left T
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hv', hqv⟩⟩))
    let P : Finset V := T.filter (fun t => ∃ u ∈ A, G.Adj u t)
    let Q : Finset V := T.filter (fun t => ∃ u ∈ B, G.Adj u t)
    have hPA : 2 ≤ P.card := by
      simpa [P] using q3_side_port_card_at_least_two hA hB hAB hAT hBT hxA hxB hxT hclosedA hT h2
    have hQB : 2 ≤ Q.card := by
      simpa [Q] using q3_side_port_card_at_least_two hB hA hAB.symm hBT hAT hxB hxA hxT hclosedB hT h2
    have hPQ : Disjoint P Q := by
      refine Finset.disjoint_left.mpr ?_
      intro t htP htQ
      obtain ⟨u, huA, hut⟩ := (Finset.mem_filter.mp htP).2
      obtain ⟨v, hvB, hvt⟩ := (Finset.mem_filter.mp htQ).2
      have huv : u = v := hport (Finset.mem_filter.mp htP).1
        (Finset.mem_filter.mp huA).2.choose.1
        (Finset.mem_filter.mp hvB).2.choose.1 hut.symm hvt.symm
      exact (Finset.disjoint_left.1 hAB) huA (huv ▸ hvB)
    have hPQsub : P ∪ Q ⊆ T := by
      intro t ht
      rcases (by simpa [Finset.mem_union] using ht) with htP | htQ
      · exact (Finset.mem_filter.mp htP).1
      · exact (Finset.mem_filter.mp htQ).1
    exact q3_two_side_port_budget_impossible hT hPA hQB hPQ hPQsub
  have hKconn : K.Connected := { preconnected := hpre, nonempty := hnonempty }
  simpa [K] using hKconn


end R03SP06

namespace R03SP06

open CubicP3Partition

variable {V : Type} [Fintype V] [DecidableEq V]

lemma cubic_neighbor_filter_card_three
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) (v : V) :
    (Finset.univ.filter (fun w : V => G.Adj v w)).card = 3 := by
  have hdegree : Nat.card {w : V // G.Adj v w} = 3 := hC v
  have hcard : (G.neighborFinset v).card =
      Nat.card {w : V // G.Adj v w} := by
    change (G.neighborFinset v).card = Nat.card (G.neighborSet v)
    rw [Nat.card_coe_set_eq]
    symm
    simpa [SimpleGraph.neighborFinset] using
      (Set.ncard_eq_toFinset_card' (G.neighborSet v))
  have hdegN : (G.neighborFinset v).card = 3 := hcard.trans hdegree
  simpa [SimpleGraph.neighborFinset_eq_filter] using hdegN

lemma cubic_center_no_two_external_neighbors'
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b c x y : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c)
    (hbx : G.Adj b x) (hby : G.Adj b y) (hxy : x ≠ y)
    (hxa : x ≠ a) (hxc : x ≠ c) (hya : y ≠ a) (hyc : y ≠ c)
    (hdeg : (Finset.univ.filter (fun w : V => G.Adj b w)).card = 3) :
    False := by
  let N : Finset V := Finset.univ.filter (fun w : V => G.Adj b w)
  have hsub : {a, c} ⊆ N := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simpa [N] using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩)
    · simpa [N] using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbc⟩)
  have hone : (N \ {a, c}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]
    have hN : N.card = 3 := by simpa [N] using hdeg
    rw [hN]
    simp [hac]
  have hxy_sub : ({x, y} : Finset V) ⊆ N \ {a, c} := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · simpa [N] using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx⟩)
      · simp [hxa, hxc]
    · refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · simpa [N] using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hby⟩)
      · simp [hya, hyc]
  have hcard := Finset.card_le_card hxy_sub
  rw [hone] at hcard
  simp [hxy] at hcard

/-- The one-external-neighbor condition for each vertex of a triangle. -/
theorem cubic_triangle_external_port_unique
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G)
    {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    ∀ ⦃t u v : V⦄, t ∈ ({a, b, c} : Finset V) →
      u ∉ ({a, b, c} : Finset V) → v ∉ ({a, b, c} : Finset V) →
      G.Adj t u → G.Adj t v → u = v := by
  have habne : a ≠ b := by
    intro heq
    subst b
    exact G.loopless.irrefl a hab
  have hbcne : b ≠ c := by
    intro heq
    subst c
    exact G.loopless.irrefl b hbc
  have hcane : c ≠ a := by
    intro heq
    subst a
    exact G.loopless.irrefl c hca
  have hacne : a ≠ c := hcane.symm
  have hdeg_a := cubic_neighbor_filter_card_three hC a
  have hdeg_b := cubic_neighbor_filter_card_three hC b
  have hdeg_c := cubic_neighbor_filter_card_three hC c
  intro t u v ht hu hv htu htv
  have huT : u ≠ a ∧ u ≠ b ∧ u ≠ c := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hu
  have hvT : v ≠ a ∧ v ≠ b ∧ v ≠ c := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · by_contra huv
    exact cubic_center_no_two_external_neighbors'
      hab.symm hca.symm hbcne htu htv huv
      huT.2.1 huT.2.2 hvT.2.1 hvT.2.2 hdeg_a
  · by_contra huv
    exact cubic_center_no_two_external_neighbors'
      hab hbc hacne htu htv huv
      huT.1 huT.2.2 hvT.1 hvT.2.2 hdeg_b
  · by_contra huv
    exact cubic_center_no_two_external_neighbors'
      hca.symm hbc.symm habne htu htv huv
      huT.1 huT.2.1 hvT.1 hvT.2.1 hdeg_c


end R03SP06



namespace R03SP06
open CubicP3Partition
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Integrated conditional q=3 reduction for a triangle deletion in a cubic
3-vertex-connected graph.  The residual after also deleting any vertex is
connected once at least six root vertices are present. -/
theorem cubic_triangle_residual_no_cut_vertex
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G)
    (hcard : 6 ≤ Fintype.card V)
    {a b c x : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hx : x ≠ a ∧ x ≠ b ∧ x ≠ c) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x}).Connected := by
  classical
  have habne : a ≠ b := by
    intro heq
    subst b
    exact G.loopless.irrefl a hab
  have hbcne : b ≠ c := by
    intro heq
    subst c
    exact G.loopless.irrefl b hbc
  have hcane : c ≠ a := by
    intro heq
    subst a
    exact G.loopless.irrefl c hca
  have hacne : a ≠ c := hcane.symm
  let T : Finset V := {a, b, c}
  have hT : T.card = 3 := by
    simp [T, habne, hbcne, hacne]
  have hxT : x ∉ T := by
    simpa [T] using hx
  have hUcard : (T ∪ {x}).card = 4 := by
    have hdis : Disjoint T ({x} : Finset V) :=
      Finset.disjoint_singleton_right.mpr hxT
    rw [Finset.card_union_of_disjoint hdis, hT]
    simp
  have hrestcard : (Finset.univ \ (T ∪ {x})).card =
      Fintype.card V - (T ∪ {x}).card :=
    Finset.card_sdiff_of_subset (Finset.subset_univ _)
  have hrestpos : 0 < (Finset.univ \ (T ∪ {x})).card := by
    rw [hrestcard, hUcard]
    omega
  have hres : ∃ v : V, v ∉ T ∧ v ≠ x := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hrestpos
    have hvU : v ∉ T ∪ {x} := (Finset.mem_sdiff.mp hv).2
    refine ⟨v, ?_, ?_⟩
    · intro hvT
      exact hvU (Finset.mem_union_left _ hvT)
    · intro hvx
      exact hvU (Finset.mem_union_right _ (Finset.mem_singleton.mpr hvx))
  have hport := cubic_triangle_external_port_unique hC hab hbc hca
  have hcut := triangle_residual_no_cut_vertex hT hxT hres h3.2 hport
  have hseteq : {v : V | v ∉ T ∧ v ≠ x} =
      {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x} := by
    ext v
    simp [T, and_assoc, and_left_comm, and_comm]
  rw [hseteq] at hcut
  exact hcut


/-- Connectedness of the triangle residual itself.  After deleting two
triangle vertices, the third vertex has at most one residual neighbor, so it
cannot join two distinct residual components. -/
theorem cubic_triangle_residual_connected
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G)
    (hcard : 6 ≤ Fintype.card V)
    {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}).Connected := by
  classical
  have habne : a ≠ b := by
    intro heq
    subst b
    exact G.loopless.irrefl a hab
  have hbcne : b ≠ c := by
    intro heq
    subst c
    exact G.loopless.irrefl b hbc
  have hcane : c ≠ a := by
    intro heq
    subst a
    exact G.loopless.irrefl c hca
  have hacne : a ≠ c := hcane.symm
  let T : Finset V := {a, b, c}
  have hT : T.card = 3 := by
    simp [T, habne, hbcne, hacne]
  have hrestcard : (Finset.univ \ T).card =
      Fintype.card V - T.card := Finset.card_sdiff_of_subset (Finset.subset_univ _)
  have hrestpos : 0 < (Finset.univ \ T).card := by
    rw [hrestcard, hT]
    omega
  have hres : ∃ v : V, v ∉ T := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hrestpos
    exact ⟨v, (Finset.mem_sdiff.mp hv).2⟩
  have hxT : c ∉ ({a, b} : Finset V) := by simp [habne, hbcne.symm, hcane]
  have hport := cubic_triangle_external_port_unique hC hab hbc hca
  let K : SimpleGraph {v : V // v ∉ T} := G.induce {v : V | v ∉ T}
  have hnonempty : Nonempty {v : V // v ∉ T} := by
    obtain ⟨v, hv⟩ := hres
    exact ⟨⟨v, hv⟩⟩
  have hpre : K.Preconnected := by
    intro p q
    by_contra hpq
    let A : Finset V := Finset.univ.filter
      (fun z : V => ∃ hz : z ∉ T, K.Reachable p ⟨z, hz⟩)
    let B : Finset V := Finset.univ.filter
      (fun z : V => ∃ hz : z ∉ T, K.Reachable q ⟨z, hz⟩)
    have hpA : p.1 ∈ A := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact ⟨p.2, SimpleGraph.Reachable.refl p⟩
    have hqB : q.1 ∈ B := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact ⟨q.2, SimpleGraph.Reachable.refl q⟩
    have hA : A.Nonempty := ⟨p.1, hpA⟩
    have hB : B.Nonempty := ⟨q.1, hqB⟩
    have hAB : Disjoint A B := by
      refine Finset.disjoint_left.mpr ?_
      intro z hzA hzB
      obtain ⟨hzA', hpz⟩ := (Finset.mem_filter.mp hzA).2
      obtain ⟨hzB', hqz⟩ := (Finset.mem_filter.mp hzB).2
      exact hpq (hpz.trans hqz.symm)
    have hAT : Disjoint A T := by
      refine Finset.disjoint_left.mpr ?_
      intro z hzA hzT
      exact (Finset.mem_filter.mp hzA).2.choose hzT
    have hBT : Disjoint B T := by
      refine Finset.disjoint_left.mpr ?_
      intro z hzB hzT
      exact (Finset.mem_filter.mp hzB).2.choose hzT
    have hclosedA : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v →
        v ∈ A ∪ T := by
      intro u v hu huv
      obtain ⟨hu', hpu⟩ := (Finset.mem_filter.mp hu).2
      by_cases hvT : v ∈ T
      · exact Finset.mem_union_right A hvT
      have hv' : v ∉ T := hvT
      have huvK : K.Adj ⟨u, hu'⟩ ⟨v, hv'⟩ := huv
      have hpv : K.Reachable p ⟨v, hv'⟩ := hpu.trans huvK.reachable
      exact Finset.mem_union_left T
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hv', hpv⟩⟩)
    have hclosedB : ∀ ⦃u v : V⦄, u ∈ B → G.Adj u v →
        v ∈ B ∪ T := by
      intro u v hu huv
      obtain ⟨hu', hqu⟩ := (Finset.mem_filter.mp hu).2
      by_cases hvT : v ∈ T
      · exact Finset.mem_union_right B hvT
      have hv' : v ∉ T := hvT
      have huvK : K.Adj ⟨u, hu'⟩ ⟨v, hv'⟩ := huv
      have hqv : K.Reachable q ⟨v, hv'⟩ := hqu.trans huvK.reachable
      exact Finset.mem_union_left T
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hv', hqv⟩⟩)
    let S : Finset V := {a, b}
    have hScard : S.card ≤ 2 := by
      change ({a, b} : Finset V).card ≤ 2
      simpa using (Finset.card_insert_le a ({b} : Finset V))
    by_cases hAc : ∃ u ∈ A, G.Adj u c
    · have hclosedB' : ∀ ⦃u v : V⦄, u ∈ B → G.Adj u v → v ∈ B ∪ S := by
        intro u v hu huv
        have huvBT : v ∈ B ∪ T := hclosedB hu huv
        rcases (by simpa [Finset.mem_union] using huvBT :
            v ∈ B ∨ v ∈ T) with hvB | hvT
        · exact Finset.mem_union_left S hvB
        · by_cases hvc : v = c
          · exfalso
            obtain ⟨uA, huA, huAc⟩ := hAc
            have huBc : G.Adj c u := by simpa [hvc] using huv.symm
            have huAc' : G.Adj c uA := huAc.symm
            have heq : u = uA := hport (by simpa [T])
              (Finset.mem_filter.mp hu).2.choose
              (Finset.mem_filter.mp huA).2.choose huBc huAc'
            exact (Finset.disjoint_left.1 hAB) huA (heq ▸ hu)
          · have hvab : v = a ∨ v = b := by
              simpa [T, hvc] using hvT
            rcases hvab with rfl | rfl
            · exact Finset.mem_union_right B (Finset.mem_insert.mpr (Or.inl rfl))
            · exact Finset.mem_union_right B (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
      exact two_vertex_connectivity_forbids_closed_side h3.2 hB hA hAB.symm
        (by
          refine Finset.disjoint_left.mpr ?_
          intro u hu huS
          rcases (by simpa [S] using huS : u = a ∨ u = b) with rfl | rfl
          · exact (Finset.disjoint_left.1 hBT) hu (by simp [T, habne, hbcne, hcane])
          · exact (Finset.disjoint_left.1 hBT) hu (by simp [T, habne, hbcne, hcane]))
        (by
          refine Finset.disjoint_left.mpr ?_
          intro u hu huS
          rcases (by simpa [S] using huS : u = a ∨ u = b) with rfl | rfl
          · exact (Finset.disjoint_left.1 hAT) hu (by simp [T, habne, hbcne, hcane])
          · exact (Finset.disjoint_left.1 hAT) hu (by simp [T, habne, hbcne, hcane]))
        hclosedB' hScard
    · have hclosedA' : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ S := by
        intro u v hu huv
        have huvAT : v ∈ A ∪ T := hclosedA hu huv
        rcases (by simpa [Finset.mem_union] using huvAT :
            v ∈ A ∨ v ∈ T) with hvA | hvT
        · exact Finset.mem_union_left S hvA
        · by_cases hvc : v = c
          · exfalso
            exact hAc ⟨u, hu, by simpa [hvc] using huv⟩
          · have hvab : v = a ∨ v = b := by
              simpa [T, hvc] using hvT
            rcases hvab with rfl | rfl
            · exact Finset.mem_union_right A (Finset.mem_insert.mpr (Or.inl rfl))
            · exact Finset.mem_union_right A (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
      exact two_vertex_connectivity_forbids_closed_side h3.2 hA hB hAB
        (by
          refine Finset.disjoint_left.mpr ?_
          intro u hu huS
          rcases (by simpa [S] using huS : u = a ∨ u = b) with rfl | rfl
          · exact (Finset.disjoint_left.1 hAT) hu (by simp [T, habne, hbcne, hcane])
          · exact (Finset.disjoint_left.1 hAT) hu (by simp [T, habne, hbcne, hcane]))
        (by
          refine Finset.disjoint_left.mpr ?_
          intro u hu huS
          rcases (by simpa [S] using huS : u = a ∨ u = b) with rfl | rfl
          · exact (Finset.disjoint_left.1 hBT) hu (by simp [T, habne, hbcne, hcane])
          · exact (Finset.disjoint_left.1 hBT) hu (by simp [T, habne, hbcne, hcane]))
        hclosedA' hScard
  have hKconn : K.Connected := { preconnected := hpre, nonempty := hnonempty }
  have hseteq : {v : V | v ∉ T} =
      {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c} := by
    ext v
    simp [T, and_assoc, and_left_comm, and_comm]
  have hKconn' : (G.induce {v : V | v ∉ T}).Connected := by
    simpa [K] using hKconn
  rw [hseteq] at hKconn'
  exact hKconn'


/-- Package the preceding two statements as the standard 2-connectivity
condition needed by the q=3 factor reduction. -/
theorem cubic_triangle_residual_two_connected
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G)
    (hcard : 6 ≤ Fintype.card V)
    {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}).Connected ∧
      ∀ x : V, x ≠ a ∧ x ≠ b ∧ x ≠ c →
        (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x}).Connected := by
  classical
  have hconn := cubic_triangle_residual_connected hC h3 hcard hab hbc hca
  refine ⟨hconn, ?_⟩
  intro x hx
  exact cubic_triangle_residual_no_cut_vertex hC h3 hcard hab hbc hca hx


/-- Cubicity supplies the missing order lower bound when combined with the
root's 3-divisibility. -/
theorem cubic_order_even_bridge
    {G : SimpleGraph V} (hC : Cubic G) :
    2 ∣ Fintype.card V := by
  classical
  have hdegree : ∀ v : V, G.degree v = 3 := by
    intro v
    change (G.neighborFinset v).card = 3
    have hcard : (G.neighborFinset v).card =
        Nat.card {w : V // G.Adj v w} := by
      change (G.neighborFinset v).card = Nat.card (G.neighborSet v)
      rw [Nat.card_coe_set_eq]
      symm
      simpa [SimpleGraph.neighborFinset] using
        (Set.ncard_eq_toFinset_card' (G.neighborSet v))
    exact hcard.trans (hC v)
  have hsum : ∑ v, G.degree v = 3 * Fintype.card V := by
    calc
      ∑ v, G.degree v = ∑ v : V, 3 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hdegree v
      _ = 3 * Fintype.card V := by simp [Nat.mul_comm]
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hparity : (3 * Fintype.card V) % 2 = 0 := by
    calc
      (3 * Fintype.card V) % 2 = (∑ v, G.degree v) % 2 := by
        rw [hsum]
      _ = (2 * G.edgeFinset.card) % 2 := by
        exact congrArg (fun n : Nat => n % 2) hhand
      _ = 0 := by omega
  omega

/-- Direct root-domain structural corollary for triangle deletions.  This is
still only a connectivity reduction: it does not provide a P3-factor for the
residual. -/
theorem cubic_three_vertex_connected_triangle_residual_no_cut_vertex_of_three_dvd
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G)
    (hdiv : 3 ∣ Fintype.card V)
    {a b c x : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hx : x ≠ a ∧ x ≠ b ∧ x ≠ c) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x}).Connected := by
  have h2 : 2 ∣ Fintype.card V := cubic_order_even_bridge hC
  obtain ⟨a2, ha2⟩ := h2
  obtain ⟨a3, ha3⟩ := hdiv
  have h6 : 6 ∣ Fintype.card V := by
    have h3a : 3 ∣ a2 := by
      apply (Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 3 2)).mp
      rw [← ha2, ha3]
      exact ⟨a3, by omega⟩
    obtain ⟨k, hk⟩ := h3a
    refine ⟨k, ?_⟩
    omega
  obtain ⟨k, hk⟩ := h6
  have hbase : 4 ≤ Fintype.card V := h3.1
  have hcard : 6 ≤ Fintype.card V := by omega
  exact cubic_triangle_residual_no_cut_vertex hC h3 hcard hab hbc hca hx


/-- Direct root-domain 2-connectivity corollary for the triangle residual. -/
theorem cubic_three_vertex_connected_triangle_residual_two_connected_of_three_dvd
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G)
    (hdiv : 3 ∣ Fintype.card V)
    {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}).Connected ∧
      ∀ x : V, x ≠ a ∧ x ≠ b ∧ x ≠ c →
        (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x}).Connected := by
  have h2 : 2 ∣ Fintype.card V := cubic_order_even_bridge hC
  obtain ⟨a2, ha2⟩ := h2
  obtain ⟨a3, ha3⟩ := hdiv
  have h6 : 6 ∣ Fintype.card V := by
    have h3a : 3 ∣ a2 := by
      apply (Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 3 2)).mp
      rw [← ha2, ha3]
      exact ⟨a3, by omega⟩
    obtain ⟨k, hk⟩ := h3a
    refine ⟨k, ?_⟩
    omega
  obtain ⟨k, hk⟩ := h6
  have hbase : 4 ≤ Fintype.card V := h3.1
  have hcard : 6 ≤ Fintype.card V := by omega
  exact cubic_triangle_residual_two_connected hC h3 hcard hab hbc hca


end R03SP06

open CubicP3Partition

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G)
    (hdiv : 3 ∣ Fintype.card V)
    {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}).Connected ∧
      ∀ x : V, x ≠ a ∧ x ≠ b ∧ x ≠ c →
        (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x}).Connected :=
  R03SP06.cubic_three_vertex_connected_triangle_residual_two_connected_of_three_dvd
    hC h3 hdiv hab hbc hca
