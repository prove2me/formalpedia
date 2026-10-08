-- Prove2me | solution 1 for Conway99Delta858.delta_add_three_prismCount
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T06:15:58.031633+00:00
-- url     : https://prove2.me/submissions/66e1508c-29e2-41e3-8abc-4a05a1a5089f

import Definitions.Def_Conway99_Delta858_20261003


set_option autoImplicit false

/-! Literal graph counts for the universal triangle and prism claim. -/

namespace Conway99Formal.TriangleBound

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]





/-- Reversing the two triangle sets preserves their joining-edge count. -/
theorem crossEdgeCount_comm (t u : Finset V) :
    crossEdgeCount G t u = crossEdgeCount G u t := by
  have := G.symm
  exact Rel.card_interedges_comm (r := G.Adj) t u

/-- A symmetric relation counts each qualifying two-element subset twice. -/
theorem unordered_pair_double_count {A : Type*} [Fintype A] [DecidableEq A]
    (s : Finset A) (R : A → A → Prop) [DecidableRel R]
    (hsym : ∀ a b, R a b → R b a) :
    (∑ a ∈ s, (s.filter fun b => a ≠ b ∧ R a b).card) =
      2 * ((s.powersetCard 2).filter fun p =>
        ∃ a b, a ∈ p ∧ b ∈ p ∧ a ≠ b ∧ R a b).card := by
  classical
  let ordered := (s ×ˢ s).filter fun ab => ab.1 ≠ ab.2 ∧ R ab.1 ab.2
  let pairs := (s.powersetCard 2).filter fun p =>
    ∃ a b, a ∈ p ∧ b ∈ p ∧ a ≠ b ∧ R a b
  have hmap : ∀ ab ∈ ordered, ({ab.1, ab.2} : Finset A) ∈ pairs := by
    intro ab hab
    have hmem := Finset.mem_filter.mp hab
    have hprod := hmem.1
    have hne := hmem.2.1
    have hR := hmem.2.2
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hprod
    simp only [pairs, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, ⟨ab.1, ab.2, by simp, by simp, hne, hR⟩⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    · simp [hne]
  have hfiber : ∀ p ∈ pairs,
      ({ab ∈ ordered | ({ab.1, ab.2} : Finset A) = p}).card = 2 := by
    intro p hp
    have hpbase : p ∈ s.powersetCard 2 := (Finset.mem_filter.mp hp).1
    have hpcard : p.card = 2 := (Finset.mem_powersetCard.mp hpbase).2
    obtain ⟨a, b, hab, hpe⟩ := Finset.card_eq_two.mp hpcard
    have hpsub : p ⊆ s := (Finset.mem_powersetCard.mp hpbase).1
    have ha : a ∈ s := hpsub (hpe.symm ▸ (by simp : a ∈ ({a, b} : Finset A)))
    have hb : b ∈ s := hpsub (hpe.symm ▸ (by simp : b ∈ ({a, b} : Finset A)))
    have hR : R a b := by
      obtain ⟨x, y, hx, hy, hxy, hxyR⟩ := (Finset.mem_filter.mp hp).2
      rw [hpe] at hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact False.elim (hxy rfl)
      · exact hxyR
      · exact hsym _ _ hxyR
      · exact False.elim (hxy rfl)
    have hset : ({ab ∈ ordered | ({ab.1, ab.2} : Finset A) = p}) =
        {(a, b), (b, a)} := by
      ext ab
      constructor
      · intro h
        have hordered : ab ∈ ordered := (Finset.mem_filter.mp h).1
        have heq : ({ab.1, ab.2} : Finset A) = p := (Finset.mem_filter.mp h).2
        have hne : ab.1 ≠ ab.2 := (Finset.mem_filter.mp hordered).2.1
        have hx : ab.1 = a ∨ ab.1 = b := by
          have : ab.1 ∈ ({a, b} : Finset A) := by rw [← hpe, ← heq]; simp
          simpa using this
        have hy : ab.2 = a ∨ ab.2 = b := by
          have : ab.2 ∈ ({a, b} : Finset A) := by rw [← hpe, ← heq]; simp
          simpa using this
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact False.elim (hne (hx.trans hy.symm))
        · exact Finset.mem_insert.mpr (Or.inl (Prod.ext hx hy))
        · exact Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr (Prod.ext hx hy)))
        · exact False.elim (hne (hx.trans hy.symm))
      · intro h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · subst ab
          apply Finset.mem_filter.mpr
          constructor
          · simp [ordered, hab, ha, hb, hR]
          · exact hpe.symm
        · subst ab
          apply Finset.mem_filter.mpr
          constructor
          · simp [ordered, hab.symm, ha, hb, hsym a b hR]
          · exact (Finset.pair_comm b a).trans hpe.symm
    rw [hset]
    simp [hab]
  have hordered :
      (∑ a ∈ s, (s.filter fun b => a ≠ b ∧ R a b).card) = ordered.card := by
    simp only [ordered, Finset.card_eq_sum_ones, Finset.sum_product, Finset.sum_filter]
  rw [hordered]
  calc
    ordered.card = ∑ p ∈ pairs,
        ({ab ∈ ordered | ({ab.1, ab.2} : Finset A) = p}).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun ab hab => hmap ab hab)
    _ = ∑ _p ∈ pairs, 2 := Finset.sum_congr rfl hfiber
    _ = 2 * pairs.card := by simp [mul_comm]

/-- The adjacent-pair parameter gives a unique third point for each edge. -/
theorem adjacent_common_unique (h : G.IsSRGWith 99 14 1 2)
    {x y : V} (hxy : G.Adj x y) :
    ∃! z : V, G.Adj x z ∧ G.Adj y z := by
  obtain ⟨z, hz⟩ := Fintype.card_eq_one_iff.mp (h.of_adj x y hxy)
  refine ⟨z.1, G.mem_commonNeighbors.mp z.2, ?_⟩
  intro w hw
  have hw' : (⟨w, G.mem_commonNeighbors.mpr hw⟩ : G.commonNeighbors x y) = z := hz _
  exact congrArg Subtype.val hw'

/-- The unique common neighbor of an edge completes every triangle containing it. -/
theorem triangle_eq_of_edge (h : G.IsSRGWith 99 14 1 2)
    (t : Finset V) (ht : t ∈ triangles G) {x y : V}
    (hxy : G.Adj x y) (hx : x ∈ t) (hy : y ∈ t) :
    ∃ z, G.Adj x z ∧ G.Adj y z ∧ t = {x, y, z} := by
  obtain ⟨z, hz, hz_unique⟩ := adjacent_common_unique G h hxy
  refine ⟨z, hz.1, hz.2, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    by_cases hwx : w = x
    · simp [hwx]
    by_cases hwy : w = y
    · simp [hwy]
    have hclique := (G.mem_cliqueFinset_iff.mp ht).isClique
    have hxw : G.Adj x w := hclique hx hw (Ne.symm hwx)
    have hyw : G.Adj y w := hclique hy hw (Ne.symm hwy)
    have hwz := hz_unique w ⟨hxw, hyw⟩
    simp [hwz]
  · have hxy' : x ≠ y := hxy.ne
    have hxz : x ≠ z := hz.1.ne
    have hyz : y ≠ z := hz.2.ne
    simpa [hxy', hxz, hyz] using (G.mem_cliqueFinset_iff.mp ht).card_eq.ge

/-- An outside point has at most one neighbor in a graph triangle. -/
theorem outside_triangle_neighbor_le_one (h : G.IsSRGWith 99 14 1 2)
    (t : Finset V) (ht : t ∈ triangles G) (v : V) (hv : v ∉ t) :
    (t.filter fun x => G.Adj v x).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  have hxT : x ∈ t := (Finset.mem_filter.mp hx).1
  have hyT : y ∈ t := (Finset.mem_filter.mp hy).1
  have hxyAdj : G.Adj x y :=
    (G.mem_cliqueFinset_iff.mp ht).isClique hxT hyT hxy
  obtain ⟨z, hxz, hyz, hT⟩ := triangle_eq_of_edge G h t ht hxyAdj hxT hyT
  have hzT : z ∈ t := hT.symm ▸ (by simp : z ∈ ({x, y, z} : Finset V))
  obtain ⟨_, _, huniq⟩ := adjacent_common_unique G h hxyAdj
  have hvz : v = z :=
    (huniq v ⟨(Finset.mem_filter.mp hx).2.symm,
      (Finset.mem_filter.mp hy).2.symm⟩).trans
      (huniq z ⟨hxz, hyz⟩).symm
  exact hv (hvz ▸ hzT)

/-- The one-common-neighbor parameter makes the graph locally linear. -/
theorem locally_linear (h : G.IsSRGWith 99 14 1 2) : G.LocallyLinear := by
  refine ⟨?_, ?_⟩
  · intro s hs t ht hst
    intro x hx y hy
    by_contra hxy
    have hs' : G.IsNClique 3 s := G.mem_cliqueSet_iff.mp hs
    have ht' : G.IsNClique 3 t := G.mem_cliqueSet_iff.mp ht
    have hsxy : G.Adj x y := hs'.isClique hx.1 hy.1 hxy
    have hS : s ∈ triangles G := G.mem_cliqueFinset_iff.mpr hs'
    have hT : t ∈ triangles G := G.mem_cliqueFinset_iff.mpr ht'
    obtain ⟨z, hxz, hyz, hseq⟩ := triangle_eq_of_edge G h s hS hsxy hx.1 hy.1
    obtain ⟨z', hxz', hyz', hteq⟩ := triangle_eq_of_edge G h t hT hsxy hx.2 hy.2
    obtain ⟨_, _, hz_unique⟩ := adjacent_common_unique G h hsxy
    have hzz : z' = z := (hz_unique z' ⟨hxz', hyz'⟩).trans
      (hz_unique z ⟨hxz, hyz⟩).symm
    exact hst (hseq.trans (by simpa [hzz] using hteq.symm))
  · intro x y hxy
    obtain ⟨z, hz, _⟩ := adjacent_common_unique G h hxy
    exact ⟨{x, y, z}, G.is3Clique_triple_iff.mpr ⟨hxy, hz.1, hz.2⟩,
      by simp, by simp⟩

/-- Every SRG(99,14,1,2), on any finite vertex type, has 231 triangles. -/
theorem triangle_count (h : G.IsSRGWith 99 14 1 2) : (triangles G).card = 231 := by
  have hdegree : ∀ v : V, G.degree v = 14 := fun v => h.regular.degree_eq v
  have hedges : G.edgeFinset.card = 693 := by
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp [hdegree, h.card] at hsum
    omega
  have hlinear := (locally_linear G h).card_edgeFinset
  dsimp [triangles]
  omega

/-- At most three edges join two disjoint graph triangles. -/
theorem disjoint_triangle_cross_edges_le_three (h : G.IsSRGWith 99 14 1 2)
    (t u : Finset V) (ht : t ∈ triangles G) (hu : u ∈ triangles G)
    (hdisj : Disjoint t u) : crossEdgeCount G t u ≤ 3 := by
  classical
  have hlocal : ∀ v ∈ t, (u.filter fun w => G.Adj v w).card ≤ 1 := by
    intro v hv
    exact outside_triangle_neighbor_le_one G h u hu v (Finset.disjoint_left.mp hdisj hv)
  calc
    crossEdgeCount G t u = (G.interedges t u).card := rfl
    _ = (t.biUnion fun v =>
        (u.filter fun w => G.Adj v w).map ⟨(v, ·), Prod.mk_right_injective v⟩).card := by
          rw [SimpleGraph.interedges, Rel.interedges_eq_biUnion]
    _ ≤ ∑ v ∈ t,
        ((u.filter fun w => G.Adj v w).map ⟨(v, ·), Prod.mk_right_injective v⟩).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ t, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro v hv
      simpa using hlocal v hv
    _ = 3 := by simp [(G.mem_cliqueFinset_iff.mp ht).card_eq]





/-- Each literal unordered disjoint triangle pair has two ordered orientations. -/
theorem sum_disjointTrianglePartnerCount (j : ℕ) :
    (∑ t ∈ triangles G, disjointTrianglePartnerCount G j t) =
      2 * disjointTrianglePairCount G j := by
  classical
  let R : Finset V → Finset V → Prop := fun t u =>
    Disjoint t u ∧ crossEdgeCount G t u = j
  have hsym : ∀ t u, R t u → R u t := by
    intro t u h
    exact ⟨h.1.symm, by rw [crossEdgeCount_comm G u t]; exact h.2⟩
  have h := unordered_pair_double_count (triangles G) R hsym
  simpa only [R, disjointTrianglePartnerCount, disjointTrianglePairCount,
    and_assoc] using h





/-- The local partner census yields the graph's literal delta/prism identity. -/
theorem graph_partner_census (h : G.IsSRGWith 99 14 1 2)
    (hlocal : ∀ t ∈ triangles G,
      disjointTrianglePartnerCount G 2 t +
        3 * disjointTrianglePartnerCount G 3 t = 36) :
    delta G + 3 * prismCount G = 4158 := by
  have hsum : (∑ t ∈ triangles G,
      (disjointTrianglePartnerCount G 2 t +
        3 * disjointTrianglePartnerCount G 3 t)) =
      (triangles G).card * 36 := by
    calc
      _ = ∑ _t ∈ triangles G, (36 : ℕ) :=
        Finset.sum_congr rfl (fun t ht => hlocal t ht)
      _ = (triangles G).card * 36 := by simp
  have htwo := sum_disjointTrianglePartnerCount G 2
  have hthree := sum_disjointTrianglePartnerCount G 3
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [htwo, hthree, triangle_count G h] at hsum
  dsimp [delta, prismCount]
  omega

#print axioms Conway99Formal.TriangleBound.crossEdgeCount_comm
#print axioms Conway99Formal.TriangleBound.adjacent_common_unique
#print axioms Conway99Formal.TriangleBound.triangle_eq_of_edge
#print axioms Conway99Formal.TriangleBound.outside_triangle_neighbor_le_one
#print axioms Conway99Formal.TriangleBound.locally_linear
#print axioms Conway99Formal.TriangleBound.triangle_count
#print axioms Conway99Formal.TriangleBound.disjoint_triangle_cross_edges_le_three
#print axioms Conway99Formal.TriangleBound.unordered_pair_double_count
#print axioms Conway99Formal.TriangleBound.sum_disjointTrianglePartnerCount
#print axioms Conway99Formal.TriangleBound.graph_partner_census

end Conway99Formal.TriangleBound


/-!
Graph-owned triangle incidence for the Conway parameter set.

The source statements are `Conway99/Conway99/Core.lean` (Line and Obligation
namespaces) and `proofs/FOUNDATIONS.md` in the September proof library. All
objects below use one literal finite graph. The SRG hypothesis forces its vertex count to 99.
-/

namespace Conway99Formal.TriangleIncidence

open Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]









theorem overlap_symm : (Bblk G)ᵀ = Bblk G := by
  simp [Bblk, Matrix.transpose_sub, Matrix.transpose_mul]

theorem overlap_identity :
    (Ninc G)ᵀ * Ninc G = 3 • (1 : Matrix (Triangle G) (Triangle G) ℤ) + Bblk G := by
  rw [Bblk]
  abel



/-- Every line of the incidence carrier has three points. -/
theorem triangle_card_three (T : Triangle G) : T.1.card = 3 :=
  (G.mem_cliqueFinset_iff.mp T.2).card_eq

/-- Every column of the incidence matrix has sum three. -/
theorem incidence_column_sum (T : Triangle G) :
    ∑ v : V, Ninc G v T = 3 := by
  simp [Ninc, ← Finset.sum_ite, triangle_card_three G T]

/-- An adjacent pair has exactly one common neighbor. -/
theorem adjacent_common_unique (h : G.IsSRGWith 99 14 1 2)
    {x y : V} (hxy : G.Adj x y) :
    ∃! z : V, G.Adj x z ∧ G.Adj y z := by
  obtain ⟨z, hz⟩ := Fintype.card_eq_one_iff.mp (h.of_adj x y hxy)
  refine ⟨z.1, (G.mem_commonNeighbors.mp z.2), ?_⟩
  intro w hw
  have hw' : (⟨w, G.mem_commonNeighbors.mpr hw⟩ : G.commonNeighbors x y) = z :=
    hz _
  exact congrArg Subtype.val hw'

/-- Every edge extends to a triangle in the same graph. -/
theorem edge_triangle (h : G.IsSRGWith 99 14 1 2)
    {x y : V} (hxy : G.Adj x y) :
    ∃ T : Triangle G, x ∈ T.1 ∧ y ∈ T.1 := by
  obtain ⟨z, hz, _⟩ := adjacent_common_unique G h hxy
  refine ⟨⟨{x, y, z}, G.mem_cliqueFinset_iff.mpr ?_⟩, by simp, by simp⟩
  exact G.is3Clique_triple_iff.mpr ⟨hxy, hz.1, hz.2⟩

/-- An edge determines every triangle containing it by its unique third point. -/
theorem triangle_eq_of_edge (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) {x y : V} (hxy : G.Adj x y)
    (hx : x ∈ T.1) (hy : y ∈ T.1) :
    ∃ z, G.Adj x z ∧ G.Adj y z ∧ T.1 = {x, y, z} := by
  obtain ⟨z, hz, hz_unique⟩ := adjacent_common_unique G h hxy
  refine ⟨z, hz.1, hz.2, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    by_cases hwx : w = x
    · simp [hwx]
    by_cases hwy : w = y
    · simp [hwy]
    have hclique := (G.mem_cliqueFinset_iff.mp T.2).isClique
    have hxw : G.Adj x w := hclique hx hw (Ne.symm hwx)
    have hyw : G.Adj y w := hclique hy hw (Ne.symm hwy)
    have hwz := hz_unique w ⟨hxw, hyw⟩
    simp [hwz]
  · have hxy' : x ≠ y := hxy.ne
    have hxz : x ≠ z := hz.1.ne
    have hyz : y ≠ z := hz.2.ne
    simpa [hxy', hxz, hyz, triangle_card_three G T]

/-- Exactly one member of the actual triangle carrier contains each edge. -/
theorem edge_triangle_unique (h : G.IsSRGWith 99 14 1 2)
    {x y : V} (hxy : G.Adj x y) :
    ∃! T : Triangle G, x ∈ T.1 ∧ y ∈ T.1 := by
  obtain ⟨T, hx, hy⟩ := edge_triangle G h hxy
  refine ⟨T, ⟨hx, hy⟩, ?_⟩
  intro U hU
  obtain ⟨z, hxz, hyz, hT⟩ := triangle_eq_of_edge G h T hxy hx hy
  obtain ⟨z', hxz', hyz', hU⟩ := triangle_eq_of_edge G h U hxy hU.1 hU.2
  obtain ⟨_, _, hz_unique⟩ := adjacent_common_unique G h hxy
  have hzz : z' = z := (hz_unique z' ⟨hxz', hyz'⟩).trans
    (hz_unique z ⟨hxz, hyz⟩).symm
  apply Subtype.ext
  exact hU.trans (by simpa [hzz] using hT.symm)

/-- A distinct point pair lies in one triangle exactly when it is an edge. -/
theorem edge_triangle_count (h : G.IsSRGWith 99 14 1 2)
    (x y : V) (hne : x ≠ y) :
    (edgeTriangles G x y).card = if G.Adj x y then 1 else 0 := by
  split_ifs with hxy
  · obtain ⟨T, hT, huniq⟩ := edge_triangle_unique G h hxy
    have hsingle : edgeTriangles G x y = {T} := by
      ext U
      constructor
      · intro hU
        have hUT : x ∈ U.1 ∧ y ∈ U.1 := (Finset.mem_filter.mp hU).2
        exact Finset.mem_singleton.mpr (huniq U hUT)
      · intro hU
        have hUT : U = T := Finset.mem_singleton.mp hU
        subst U
        simp [edgeTriangles, hT]
    simp [hsingle]
  · have hempty : edgeTriangles G x y = ∅ := by
      ext T
      constructor
      · intro hT
        have hxy' : x ∈ T.1 ∧ y ∈ T.1 := (Finset.mem_filter.mp hT).2
        have hclique := (G.mem_cliqueFinset_iff.mp T.2).isClique
        exact False.elim (hxy (hclique hxy'.1 hxy'.2 hne))
      · intro hT
        simp at hT
    simp [hempty]

/-- The SRG adjacent-pair condition makes the graph locally linear. -/
theorem locally_linear (h : G.IsSRGWith 99 14 1 2) : G.LocallyLinear := by
  refine ⟨?_, ?_⟩
  · intro s hs t ht hst
    intro x hx y hy
    by_contra hxy
    have hs' : G.IsNClique 3 s := G.mem_cliqueSet_iff.mp hs
    have ht' : G.IsNClique 3 t := G.mem_cliqueSet_iff.mp ht
    have hsxy : G.Adj x y := hs'.isClique hx.1 hy.1 hxy
    let S : Triangle G := ⟨s, G.mem_cliqueFinset_iff.mpr hs'⟩
    let T : Triangle G := ⟨t, G.mem_cliqueFinset_iff.mpr ht'⟩
    obtain ⟨z, hxz, hyz, hS⟩ := triangle_eq_of_edge G h S hsxy hx.1 hy.1
    obtain ⟨z', hxz', hyz', hT⟩ := triangle_eq_of_edge G h T hsxy hx.2 hy.2
    obtain ⟨_, _, hz_unique⟩ := adjacent_common_unique G h hsxy
    have hzz : z' = z := (hz_unique z' ⟨hxz', hyz'⟩).trans
      (hz_unique z ⟨hxz, hyz⟩).symm
    exact hst (hS.trans (by simpa [hzz] using hT.symm))
  · intro x y hxy
    obtain ⟨T, hx, hy⟩ := edge_triangle G h hxy
    exact ⟨T.1, G.mem_cliqueFinset_iff.mp T.2, hx, hy⟩

/-- The actual graph has 231 three-cliques. -/
theorem triangle_count (h : G.IsSRGWith 99 14 1 2) :
    (G.cliqueFinset 3).card = 231 := by
  have hdegree : ∀ v : V, G.degree v = 14 := fun v => h.regular.degree_eq v
  have hedges : G.edgeFinset.card = 693 := by
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp [hdegree, h.card] at hsum
    omega
  have hlinear := (locally_linear G h).card_edgeFinset
  omega

/-- Exactly seven actual triangles pass through each point. -/
theorem triangles_through_vertex (h : G.IsSRGWith 99 14 1 2) (v : V) :
    (Finset.univ.filter fun T : Triangle G => v ∈ T.1).card = 7 := by
  classical
  have hleft :
      (∑ u : V, if u ≠ v then (edgeTriangles G v u).card else 0) = 14 := by
    calc
      _ = ∑ u : V, if G.Adj v u then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases huv : u = v
        · subst u
          simp
        · simp [huv, edge_triangle_count G h v u (Ne.symm huv)]
      _ = G.degree v := by
        simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
      _ = 14 := h.regular.degree_eq v
  have hright :
      (∑ u : V, if u ≠ v then (edgeTriangles G v u).card else 0) =
        2 * (Finset.univ.filter fun T : Triangle G => v ∈ T.1).card := by
    calc
      _ = ∑ u : V, ∑ T : Triangle G,
          if u ≠ v ∧ v ∈ T.1 ∧ u ∈ T.1 then (1 : ℕ) else 0 := by
            apply Finset.sum_congr rfl
            intro u _
            by_cases huv : u = v
            · subst u
              simp
            · rw [if_pos huv]
              calc
                (edgeTriangles G v u).card =
                    ∑ T : Triangle G, if v ∈ T.1 ∧ u ∈ T.1 then (1 : ℕ) else 0 := by
                  simpa only [edgeTriangles, Nat.cast_id] using
                    (Finset.sum_boole (p := fun T : Triangle G => v ∈ T.1 ∧ u ∈ T.1)
                      (s := Finset.univ) (R := ℕ)).symm
                _ = _ := by
                  apply Finset.sum_congr rfl
                  intro T _
                  simp [huv]
      _ = ∑ T : Triangle G, ∑ u : V,
          if u ≠ v ∧ v ∈ T.1 ∧ u ∈ T.1 then (1 : ℕ) else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ T : Triangle G, if v ∈ T.1 then 2 else 0 := by
            apply Finset.sum_congr rfl
            intro T _
            by_cases hvT : v ∈ T.1
            · have hcard : (T.1.erase v).card = 2 := by
                rw [Finset.card_erase_of_mem hvT, triangle_card_three G T]
              calc
                (∑ u : V,
                    if u ≠ v ∧ v ∈ T.1 ∧ u ∈ T.1 then (1 : ℕ) else 0) =
                    (Finset.univ.filter fun u => u ≠ v ∧ u ∈ T.1).card := by
                      simp [hvT]
                _ = (T.1.erase v).card := by
                  have hset : (Finset.univ.filter fun u : V => u ≠ v ∧ u ∈ T.1) =
                      T.1.erase v := by
                    ext u
                    simp [Finset.mem_erase, and_comm]
                  exact congrArg Finset.card hset
                _ = 2 := hcard
              simp [hvT] at *
            · simp [hvT]
      _ = _ := by
        simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul, mul_comm]
        simp only [Nat.cast_id]
  omega

/-- A point outside a triangle is adjacent to at most one of its points. -/
theorem outside_triangle_neighbor_le_one (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) (v : V) (hv : v ∉ T.1) :
    (T.1.filter fun x => G.Adj v x).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  have hxT : x ∈ T.1 := (Finset.mem_filter.mp hx).1
  have hyT : y ∈ T.1 := (Finset.mem_filter.mp hy).1
  have hxyAdj : G.Adj x y :=
    (G.mem_cliqueFinset_iff.mp T.2).isClique hxT hyT hxy
  obtain ⟨z, hxz, hyz, hT⟩ := triangle_eq_of_edge G h T hxyAdj hxT hyT
  have hzT : z ∈ T.1 := hT.symm ▸ (by simp : z ∈ ({x, y, z} : Finset V))
  obtain ⟨_, _, huniq⟩ := adjacent_common_unique G h hxyAdj
  have hvz : v = z :=
    (huniq v ⟨(Finset.mem_filter.mp hx).2.symm,
      (Finset.mem_filter.mp hy).2.symm⟩).trans
      (huniq z ⟨hxz, hyz⟩).symm
  exact hv (hvz ▸ hzT)

/-- Cross edges between disjoint triangles form a matching on both sides. -/
theorem disjoint_cross_matching (h : G.IsSRGWith 99 14 1 2)
    (S T : Triangle G) (hd : Disjoint S.1 T.1) :
    (∀ v ∈ S.1, (T.1.filter fun w => G.Adj v w).card ≤ 1) ∧
      (∀ w ∈ T.1, (S.1.filter fun v => G.Adj w v).card ≤ 1) := by
  constructor
  · intro v hv
    exact outside_triangle_neighbor_le_one G h T v
      (Finset.disjoint_left.mp hd hv)
  · intro w hw
    exact outside_triangle_neighbor_le_one G h S w
      (Finset.disjoint_left.mp hd.symm hw)

/-- At most three edges join two disjoint actual triangles. -/
theorem disjoint_cross_card_le_three (h : G.IsSRGWith 99 14 1 2)
    (S T : Triangle G) (hd : Disjoint S.1 T.1) :
    (G.interedges S.1 T.1).card ≤ 3 := by
  have hmatch := (disjoint_cross_matching G h S T hd).1
  calc
    (G.interedges S.1 T.1).card ≤ S.1.card := by
      apply Finset.card_le_card_of_injOn (fun p : V × V => p.1)
      · intro p hp
        exact (G.mem_interedges_iff.mp hp).1
      · intro p hp q hq heq
        obtain ⟨hps, hpt, hpa⟩ := G.mem_interedges_iff.mp hp
        obtain ⟨hqs, hqt, hqa⟩ := G.mem_interedges_iff.mp hq
        have heq' : p.1 = q.1 := heq
        have hqa' : G.Adj p.1 q.2 := heq'.symm ▸ hqa
        have hbd : p.2 = q.2 :=
          (Finset.card_le_one_iff_subsingleton.mp (hmatch p.1 hps))
            (Finset.mem_filter.mpr ⟨hpt, hpa⟩)
            (Finset.mem_filter.mpr ⟨hqt, hqa'⟩)
        exact Prod.ext heq' hbd
    _ = 3 := triangle_card_three G S

/-- Each entry of `N Nᵀ` counts triangles through its two point indices. -/
theorem incidence_entry (x y : V) :
    ∑ T : Triangle G, Ninc G x T * (Ninc G)ᵀ T y =
      ((edgeTriangles G x y).card : ℤ) := by
  classical
  calc
    _ = ∑ T : Triangle G, if x ∈ T.1 ∧ y ∈ T.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      by_cases hx : x ∈ T.1 <;> by_cases hy : y ∈ T.1 <;>
        simp [Ninc, hx, hy, Matrix.transpose_apply]
    _ = _ := by
      simpa only [edgeTriangles] using
        (Finset.sum_boole (p := fun T : Triangle G => x ∈ T.1 ∧ y ∈ T.1)
          (s := Finset.univ) (R := ℤ))

/-- The point Gram identity on one actual graph's incidence coordinates. -/
theorem incidence_square (h : G.IsSRGWith 99 14 1 2) :
    Ninc G * (Ninc G)ᵀ =
      7 • (1 : Matrix V V ℤ) + G.adjMatrix ℤ := by
  ext x y
  rw [Matrix.mul_apply, incidence_entry G x y]
  by_cases heq : x = y
  · subst y
    have hdiag : edgeTriangles G x x =
        Finset.univ.filter (fun T : Triangle G => x ∈ T.1) := by
      ext T
      simp [edgeTriangles]
    rw [hdiag, triangles_through_vertex G h x]
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply]
  · rw [edge_triangle_count G h x y heq]
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply, heq]

private theorem incidence_entry_real (x y : V) :
    ∑ T : Triangle G, NincReal G x T * (NincReal G)ᵀ T y =
      ((edgeTriangles G x y).card : ℝ) := by
  classical
  calc
    _ = ∑ T : Triangle G, if x ∈ T.1 ∧ y ∈ T.1 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      by_cases hx : x ∈ T.1 <;> by_cases hy : y ∈ T.1 <;>
        simp [NincReal, hx, hy, Matrix.transpose_apply]
    _ = _ := by
      simpa only [edgeTriangles] using
        (Finset.sum_boole (p := fun T : Triangle G => x ∈ T.1 ∧ y ∈ T.1)
          (s := Finset.univ) (R := ℝ))

/-- The real point Gram identity for the same literal triangle incidence. -/
theorem incidence_square_real (h : G.IsSRGWith 99 14 1 2) :
    NincReal G * (NincReal G)ᵀ =
      (7 : ℝ) • (1 : Matrix V V ℝ) + G.adjMatrix ℝ := by
  ext x y
  rw [Matrix.mul_apply, incidence_entry_real G x y]
  by_cases heq : x = y
  · subst y
    have hdiag : edgeTriangles G x x =
        Finset.univ.filter (fun T : Triangle G => x ∈ T.1) := by
      ext T
      simp [edgeTriangles]
    rw [hdiag, triangles_through_vertex G h x]
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply]
  · rw [edge_triangle_count G h x y heq]
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply, heq]

/-- The triangle incidence row sum is seven. -/
theorem incidence_row_sum (h : G.IsSRGWith 99 14 1 2) (v : V) :
    ∑ T : Triangle G, Ninc G v T = 7 := by
  calc
    _ = ((Finset.univ.filter fun T : Triangle G => v ∈ T.1).card : ℤ) := by
      simpa only [Ninc] using
        (Finset.sum_boole (p := fun T : Triangle G => v ∈ T.1)
          (s := Finset.univ) (R := ℤ))
    _ = 7 := by exact_mod_cast triangles_through_vertex G h v

/-- The overlap matrix is 18-regular on the actual triangle carrier. -/
theorem overlap_degree_eighteen (h : G.IsSRGWith 99 14 1 2) (T : Triangle G) :
    ∑ S : Triangle G, Bblk G S T = 18 := by
  classical
  calc
    (∑ S : Triangle G, Bblk G S T) =
        (∑ S : Triangle G, ∑ v : V, Ninc G v S * Ninc G v T) - 3 := by
      simp [Bblk, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_sub_distrib,
        Matrix.ofNat_apply]
    _ = (∑ v : V, (∑ S : Triangle G, Ninc G v S) * Ninc G v T) - 3 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ = (∑ v : V, 7 * Ninc G v T) - 3 := by
      simp_rw [incidence_row_sum G h]
    _ = 7 * (∑ v : V, Ninc G v T) - 3 := by rw [Finset.mul_sum]
    _ = 18 := by rw [incidence_column_sum G T]; norm_num

/-- Distinct three-cliques of an SRG with `λ = 1` share at most one point. -/
theorem distinct_triangles_inter_le_one (h : G.IsSRGWith 99 14 1 2)
    (S T : Triangle G) (hne : S ≠ T) : (S.1 ∩ T.1).card ≤ 1 := by
  have hs : S.1 ∈ G.cliqueSet 3 :=
    G.mem_cliqueSet_iff.mpr (G.mem_cliqueFinset_iff.mp S.2)
  have ht : T.1 ∈ G.cliqueSet 3 :=
    G.mem_cliqueSet_iff.mpr (G.mem_cliqueFinset_iff.mp T.2)
  have hst : S.1 ≠ T.1 := by
    intro heq
    exact hne (Subtype.ext heq)
  have hpair := (locally_linear G h).edgeDisjointTriangles hs ht hst
  exact Finset.card_le_one_iff_subsingleton.mpr (by
    simpa only [Finset.coe_inter] using hpair)

/-- An overlap-matrix entry is the number of common points of two triangles. -/
theorem overlap_entry (S T : Triangle G) :
    ((Ninc G)ᵀ * Ninc G) S T = ((S.1 ∩ T.1).card : ℤ) := by
  classical
  rw [Matrix.mul_apply]
  calc
    _ = ∑ v : V, if v ∈ S.1 ∩ T.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hs : v ∈ S.1 <;> by_cases ht : v ∈ T.1 <;>
        simp [Ninc, hs, ht, Matrix.transpose_apply]
    _ = ((Finset.univ.filter fun v : V => v ∈ S.1 ∩ T.1).card : ℤ) := by
      exact Finset.sum_boole (p := fun v : V => v ∈ S.1 ∩ T.1)
        (s := Finset.univ) (R := ℤ)
    _ = _ := by
      have heq : (Finset.univ.filter fun v : V => v ∈ S.1 ∩ T.1) =
          S.1 ∩ T.1 := by
        ext v
        simp
      rw [heq]

/-- The derived overlap matrix is a loopless zero-one adjacency matrix. -/
theorem overlap_zero_one (h : G.IsSRGWith 99 14 1 2) (S T : Triangle G) :
    (Bblk G S T = 0 ∨ Bblk G S T = 1) ∧ (S = T → Bblk G S T = 0) := by
  have hdiag (U : Triangle G) : Bblk G U U = 0 := by
    simp [Bblk, overlap_entry G U U, triangle_card_three G U, Matrix.ofNat_apply]
  constructor
  · by_cases heq : S = T
    · subst T
      exact Or.inl (hdiag S)
    · have hle := distinct_triangles_inter_le_one G h S T heq
      have hc : (S.1 ∩ T.1).card = 0 ∨ (S.1 ∩ T.1).card = 1 := by omega
      rcases hc with hc | hc
      · left
        simp [Bblk, overlap_entry G S T, Matrix.ofNat_apply, heq, hc]
      · right
        simp [Bblk, overlap_entry G S T, Matrix.ofNat_apply, heq, hc]
  · intro heq
    subst T
    exact hdiag S

/-- Each triangle has eighteen distinct neighbors in the overlap graph. -/
theorem overlap_neighbor_count (h : G.IsSRGWith 99 14 1 2) (T : Triangle G) :
    (Finset.univ.filter fun S : Triangle G => Bblk G S T = 1).card = 18 := by
  have hsum :
      (∑ S : Triangle G, Bblk G S T) =
        ((Finset.univ.filter fun S : Triangle G => Bblk G S T = 1).card : ℤ) := by
    calc
      _ = ∑ S : Triangle G, if Bblk G S T = 1 then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro S _
        rcases (overlap_zero_one G h S T).1 with hzero | hone
        · simp [hzero]
        · simp [hone]
      _ = _ := Finset.sum_boole
        (p := fun S : Triangle G => Bblk G S T = 1) (s := Finset.univ) (R := ℤ)
  rw [overlap_degree_eighteen G h T] at hsum
  exact_mod_cast hsum.symm



theorem triangle_star_card_six (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) (v : V) (hv : v ∈ T.1) :
    (triangleStar G T v).card = 6 := by
  have hmem : T ∈ (Finset.univ.filter fun S : Triangle G => v ∈ S.1) := by
    simp [hv]
  have hstar : triangleStar G T v =
      (Finset.univ.filter fun S : Triangle G => v ∈ S.1).erase T := by
    ext S
    simp [triangleStar, and_comm]
  rw [hstar, Finset.card_erase_of_mem hmem, triangles_through_vertex G h v]

theorem overlap_one_iff (h : G.IsSRGWith 99 14 1 2) (S T : Triangle G) :
    Bblk G S T = 1 ↔ S ≠ T ∧ (S.1 ∩ T.1).card = 1 := by
  constructor
  · intro hB
    have hne : S ≠ T := by
      intro heq
      have hzero := (overlap_zero_one G h S T).2 heq
      omega
    have hle := distinct_triangles_inter_le_one G h S T hne
    have hpos : 0 < (S.1 ∩ T.1).card := by
      by_contra hnot
      have hc : (S.1 ∩ T.1).card = 0 := by omega
      have hzero : Bblk G S T = 0 := by
        simp [Bblk, overlap_entry G S T, Matrix.ofNat_apply, hne, hc]
      omega
    exact ⟨hne, by omega⟩
  · rintro ⟨hne, hc⟩
    simp [Bblk, overlap_entry G S T, Matrix.ofNat_apply, hne, hc]

/-- Distinct actual triangles are disjoint or meet in the overlap graph. -/
theorem distinct_triangle_disjoint_or_overlap (h : G.IsSRGWith 99 14 1 2)
    (S T : Triangle G) (hne : S ≠ T) :
    Disjoint S.1 T.1 ∨ Bblk G S T = 1 := by
  rcases (overlap_zero_one G h S T).1 with hz | ho
  · left
    have hentry : Bblk G S T = ((S.1 ∩ T.1).card : ℤ) := by
      simp [Bblk, overlap_entry G S T, Matrix.ofNat_apply, hne]
    rw [hentry] at hz
    have hcard : (S.1 ∩ T.1).card = 0 := by
      exact_mod_cast hz
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hcard)
  · exact Or.inr ho

theorem triangle_star_clique (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) (v : V) (S U : Triangle G)
    (hS : S ∈ triangleStar G T v) (hU : U ∈ triangleStar G T v)
    (hne : S ≠ U) : Bblk G S U = 1 := by
  have hvS : v ∈ S.1 := (Finset.mem_filter.mp hS).2.2
  have hvU : v ∈ U.1 := (Finset.mem_filter.mp hU).2.2
  have hpos : 0 < (S.1 ∩ U.1).card :=
    Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨hvS, hvU⟩⟩
  have hle := distinct_triangles_inter_le_one G h S U hne
  apply (overlap_one_iff G h S U).2
  exact ⟨hne, by omega⟩

theorem triangle_star_disjoint (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) (v w : V) (hv : v ∈ T.1) (hw : w ∈ T.1)
    (hvw : v ≠ w) : Disjoint (triangleStar G T v) (triangleStar G T w) := by
  apply Finset.disjoint_left.mpr
  intro S hS hW
  have hne : S ≠ T := (Finset.mem_filter.mp hS).2.1
  have hvS : v ∈ S.1 := (Finset.mem_filter.mp hS).2.2
  have hwS : w ∈ S.1 := (Finset.mem_filter.mp hW).2.2
  have hvwAdj : G.Adj v w :=
    (G.mem_cliqueFinset_iff.mp T.2).isClique hv hw hvw
  obtain ⟨U, _, huniq⟩ := edge_triangle_unique G h hvwAdj
  have hSU : S = U := huniq S ⟨hvS, hwS⟩
  have hTU : T = U := huniq T ⟨hv, hw⟩
  exact hne (hSU.trans hTU.symm)

theorem overlap_neighbors_eq_star_union (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) :
    (Finset.univ.filter fun S : Triangle G => Bblk G S T = 1) =
      T.1.biUnion (triangleStar G T) := by
  ext S
  constructor
  · intro hS
    obtain ⟨hne, hcard⟩ := (overlap_one_iff G h S T).1 (Finset.mem_filter.mp hS).2
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (S.1 ∩ T.1).card)
    obtain ⟨hvS, hvT⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_biUnion.mpr ⟨v, hvT, Finset.mem_filter.mpr
      ⟨Finset.mem_univ S, ⟨hne, hvS⟩⟩⟩
  · intro hS
    obtain ⟨v, hvT, hvStar⟩ := Finset.mem_biUnion.mp hS
    have hne : S ≠ T := (Finset.mem_filter.mp hvStar).2.1
    have hvS : v ∈ S.1 := (Finset.mem_filter.mp hvStar).2.2
    have hpos : 0 < (S.1 ∩ T.1).card :=
      Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨hvS, hvT⟩⟩
    have hle := distinct_triangles_inter_le_one G h S T hne
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ S,
      (overlap_one_iff G h S T).2 ⟨hne, by omega⟩⟩

theorem triangle_star_cross_nonadjacent (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) (v w : V) (hv : v ∈ T.1) (hw : w ∈ T.1)
    (hvw : v ≠ w) (S U : Triangle G)
    (hS : S ∈ triangleStar G T v) (hU : U ∈ triangleStar G T w) :
    Bblk G S U = 0 := by
  rcases (overlap_zero_one G h S U).1 with hzero | hone
  · exact hzero
  have hneST : S ≠ T := (Finset.mem_filter.mp hS).2.1
  have hneUT : U ≠ T := (Finset.mem_filter.mp hU).2.1
  have hvS : v ∈ S.1 := (Finset.mem_filter.mp hS).2.2
  have hwU : w ∈ U.1 := (Finset.mem_filter.mp hU).2.2
  have hcard : (S.1 ∩ U.1).card = 1 :=
    ((overlap_one_iff G h S U).1 hone).2
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (S.1 ∩ U.1).card)
  obtain ⟨hxS, hxU⟩ := Finset.mem_inter.mp hx
  have hxnotT : x ∉ T.1 := by
    intro hxT
    have hsubS := Finset.card_le_one_iff_subsingleton.mp
      (distinct_triangles_inter_le_one G h S T hneST)
    have hsubU := Finset.card_le_one_iff_subsingleton.mp
      (distinct_triangles_inter_le_one G h U T hneUT)
    have hxv : x = v := hsubS (Finset.mem_inter.mpr ⟨hxS, hxT⟩)
      (Finset.mem_inter.mpr ⟨hvS, hv⟩)
    have hxw : x = w := hsubU (Finset.mem_inter.mpr ⟨hxU, hxT⟩)
      (Finset.mem_inter.mpr ⟨hwU, hw⟩)
    exact hvw (hxv.symm.trans hxw)
  have hxv : x ≠ v := by
    intro heq
    exact hxnotT (heq ▸ hv)
  have hxw : x ≠ w := by
    intro heq
    exact hxnotT (heq ▸ hw)
  have hAdjV : G.Adj x v :=
    (G.mem_cliqueFinset_iff.mp S.2).isClique hxS hvS hxv
  have hAdjW : G.Adj x w :=
    (G.mem_cliqueFinset_iff.mp U.2).isClique hxU hwU hxw
  have hbound := outside_triangle_neighbor_le_one G h T x hxnotT
  have hsub := Finset.card_le_one_iff_subsingleton.mp hbound
  exact False.elim (hvw (hsub (Finset.mem_filter.mpr ⟨hv, hAdjV⟩)
    (Finset.mem_filter.mpr ⟨hw, hAdjW⟩)))

/-- The overlap neighbors of a triangle induce three disjoint six-cliques. -/
theorem overlap_locally_three_six_cliques (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) :
    ∃ part : Fin 3 → Finset (Triangle G),
      (∀ i, (part i).card = 6) ∧
      (∀ i j, i ≠ j → Disjoint (part i) (part j)) ∧
      (Finset.univ.filter fun S : Triangle G => Bblk G T S = 1) =
        (Finset.univ : Finset (Fin 3)).biUnion part ∧
      (∀ i, ∀ S ∈ part i, ∀ U ∈ part i, S ≠ U → Bblk G S U = 1) ∧
      (∀ i j, i ≠ j → ∀ S ∈ part i, ∀ U ∈ part j, Bblk G S U = 0) := by
  let e : Fin 3 ≃ T.1 :=
    (Finset.equivFinOfCardEq (triangle_card_three G T)).symm
  let part : Fin 3 → Finset (Triangle G) := fun i => triangleStar G T (e i).1
  refine ⟨part, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact triangle_star_card_six G h T (e i).1 (e i).2
  · intro i j hij
    have hpoints : (e i).1 ≠ (e j).1 := by
      intro heq
      exact hij (e.injective (Subtype.ext heq))
    exact triangle_star_disjoint G h T (e i).1 (e j).1
      (e i).2 (e j).2 hpoints
  · have hBS (S : Triangle G) : Bblk G T S = Bblk G S T := by
      have hsymm := congrArg
        (fun M : Matrix (Triangle G) (Triangle G) ℤ => M S T) (overlap_symm G)
      simpa [Matrix.transpose_apply] using hsymm
    calc
      (Finset.univ.filter fun S : Triangle G => Bblk G T S = 1) =
          (Finset.univ.filter fun S : Triangle G => Bblk G S T = 1) := by
            ext S
            simp [hBS]
      _ = T.1.biUnion (triangleStar G T) := overlap_neighbors_eq_star_union G h T
      _ = (Finset.univ : Finset (Fin 3)).biUnion part := by
        ext S
        constructor
        · intro hS
          obtain ⟨v, hvT, hvStar⟩ := Finset.mem_biUnion.mp hS
          obtain ⟨i, hi⟩ := e.surjective ⟨v, hvT⟩
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by
            simpa [part, hi] using hvStar⟩
        · intro hS
          obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hS
          exact Finset.mem_biUnion.mpr ⟨(e i).1, (e i).2, hi⟩
  · intro i S hS U hU hne
    exact triangle_star_clique G h T (e i).1 S U hS hU hne
  · intro i j hij S hS U hU
    have hpoints : (e i).1 ≠ (e j).1 := by
      intro heq
      exact hij (e.injective (Subtype.ext heq))
    exact triangle_star_cross_nonadjacent G h T (e i).1 (e j).1
      (e i).2 (e j).2 hpoints S U hS hU

/-- Two overlapping triangles have five common neighbors in the overlap graph. -/
theorem overlap_square_adjacent_five (h : G.IsSRGWith 99 14 1 2)
    (S T : Triangle G) (hST : Bblk G S T = 1) :
    ((Bblk G) ^ 2) S T = 5 := by
  obtain ⟨part, hcard, hdis, hunion, hwithin, hcross⟩ :=
    overlap_locally_three_six_cliques G h S
  have hT : T ∈ (Finset.univ : Finset (Fin 3)).biUnion part := by
    rw [← hunion]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ T, hST⟩
  obtain ⟨i, _, hiT⟩ := Finset.mem_biUnion.mp hT
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 3))) part := by
    intro j _ k _ hjk
    exact hdis j k hjk
  have hsumPart (j : Fin 3) :
      (∑ U ∈ part j, Bblk G U T) = if j = i then (5 : ℤ) else 0 := by
    by_cases hji : j = i
    · subst j
      simp only [if_pos rfl]
      have hdiag : Bblk G T T = 0 := (overlap_zero_one G h T T).2 rfl
      have hremove := Finset.add_sum_erase (part i) (fun U => Bblk G U T) hiT
      rw [hdiag, zero_add] at hremove
      rw [← hremove]
      calc
        (∑ U ∈ (part i).erase T, Bblk G U T) =
            ∑ U ∈ (part i).erase T, (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro U hU
          exact hwithin i U (Finset.mem_of_mem_erase hU) T hiT
            (Finset.ne_of_mem_erase hU)
        _ = 5 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem hiT, hcard i]
          norm_num
    · simp only [if_neg hji]
      apply Finset.sum_eq_zero
      intro U hU
      exact hcross j i hji U hU T hiT
  calc
    ((Bblk G) ^ 2) S T =
        ∑ U ∈ (Finset.univ.filter fun U : Triangle G => Bblk G S U = 1),
          Bblk G U T := by
      rw [sq, Matrix.mul_apply]
      calc
        (∑ U : Triangle G, Bblk G S U * Bblk G U T) =
            ∑ U : Triangle G, if Bblk G S U = 1 then Bblk G U T else 0 := by
          apply Finset.sum_congr rfl
          intro U _
          rcases (overlap_zero_one G h S U).1 with hz | ho
          · simp [hz]
          · simp [ho]
        _ = _ := by simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    _ = ∑ j : Fin 3, ∑ U ∈ part j, Bblk G U T := by
      rw [hunion]
      exact Finset.sum_biUnion hpair
    _ = ∑ j : Fin 3, if j = i then (5 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact hsumPart j
    _ = 5 := by simp

/-- The point adjacency relation supplies the quadratic identity used by the triangle Gram. -/
theorem point_adjacency_square (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix ℤ) ^ 2 =
      12 • (1 : Matrix V V ℤ) - G.adjMatrix ℤ +
        2 • (of 1 : Matrix V V ℤ) := by
  have hC : Gᶜ.adjMatrix ℤ =
      (of 1 : Matrix V V ℤ) - 1 - G.adjMatrix ℤ := by
    have heq := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := ℤ)
    rw [G.compl_adjMatrix_eq_adjMatrix_compl ℤ] at heq
    linear_combination (norm := module) heq
  have hm := h.matrix_eq (α := ℤ)
  rw [hC] at hm
  rw [hm]
  module

theorem point_adjacency_polynomial (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix ℤ - 3 • (1 : Matrix V V ℤ)) *
      (G.adjMatrix ℤ + 4 • (1 : Matrix V V ℤ)) =
        2 • (of 1 : Matrix V V ℤ) := by
  have hA := point_adjacency_square G h
  have h2 :
      (G.adjMatrix ℤ - 3 • (1 : Matrix V V ℤ)) *
        (G.adjMatrix ℤ + 4 • (1 : Matrix V V ℤ)) =
          (G.adjMatrix ℤ) ^ 2 + G.adjMatrix ℤ -
            12 • (1 : Matrix V V ℤ) := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, sq]
    noncomm_ring
  rw [h2, hA]
  module

theorem point_adjacency_times_ones (h : G.IsSRGWith 99 14 1 2) :
    G.adjMatrix ℤ * (of 1 : Matrix V V ℤ) =
      14 • (of 1 : Matrix V V ℤ) := by
  ext i j
  have key := G.adjMatrix_mulVec_const_apply_of_regular (α := ℤ) (a := 1)
    h.regular (v := i)
  simp only [Matrix.mulVec, dotProduct, Function.const, mul_one] at key
  simp only [Matrix.mul_apply, Matrix.of_apply, Pi.one_apply, mul_one,
    Matrix.smul_apply]
  simpa using key

theorem pointGram_cubic (h : G.IsSRGWith 99 14 1 2) :
    (Ninc G * (Ninc G)ᵀ - 21 • (1 : Matrix V V ℤ)) *
      (Ninc G * (Ninc G)ᵀ - 10 • (1 : Matrix V V ℤ)) *
      (Ninc G * (Ninc G)ᵀ - 3 • (1 : Matrix V V ℤ)) = 0 := by
  let A := G.adjMatrix ℤ
  let J : Matrix V V ℤ := of 1
  have hrewrite :
      (Ninc G * (Ninc G)ᵀ - 21 • (1 : Matrix V V ℤ)) *
        (Ninc G * (Ninc G)ᵀ - 10 • (1 : Matrix V V ℤ)) *
        (Ninc G * (Ninc G)ᵀ - 3 • (1 : Matrix V V ℤ)) =
          (A - 14 • 1) * ((A - 3 • 1) * (A + 4 • 1)) := by
    rw [incidence_square G h]
    dsimp [A]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    noncomm_ring
  rw [hrewrite, point_adjacency_polynomial G h]
  have hAJ := point_adjacency_times_ones G h
  change (A - 14 • 1) * (2 • J) = 0
  calc
    _ = A * (2 • J) - (14 • 1) * (2 • J) := Matrix.sub_mul _ _ _
    _ = 2 • (A * J) - 2 • (14 • J) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, one_mul]
    _ = 0 := by
      have hAJ' : A * J = 14 • J := hAJ
      simpa [hAJ']

/-- The triangle overlap matrix has the source's four-root annihilator. -/
theorem overlap_annihilator (h : G.IsSRGWith 99 14 1 2) :
    (Bblk G - 18 • 1) * (Bblk G - 7 • 1) * Bblk G * (Bblk G + 3 • 1) = 0 := by
  let N := Ninc G
  let M : Matrix (Triangle G) (Triangle G) ℤ := Nᵀ * N
  let K : Matrix V V ℤ := N * Nᵀ
  have hshift (c : ℕ) :
      (M - c • 1) * Nᵀ = Nᵀ * (K - c • 1) := by
    calc
      _ = M * Nᵀ - c • Nᵀ := by
        rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = Nᵀ * K - c • Nᵀ := by
        dsimp [M, K]
        rw [Matrix.mul_assoc]
      _ = Nᵀ * (K - c • 1) := by
        rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  have htransfer :
      ((M - 21 • 1) * (M - 10 • 1) * (M - 3 • 1)) * Nᵀ =
        Nᵀ * ((K - 21 • 1) * (K - 10 • 1) * (K - 3 • 1)) := by
    calc
      _ = ((M - 21 • 1) * (M - 10 • 1)) * ((M - 3 • 1) * Nᵀ) := by
        simp only [Matrix.mul_assoc]
      _ = ((M - 21 • 1) * (M - 10 • 1)) * (Nᵀ * (K - 3 • 1)) := by
        rw [hshift 3]
      _ = ((M - 21 • 1) * ((M - 10 • 1) * Nᵀ)) * (K - 3 • 1) := by
        simp only [Matrix.mul_assoc]
      _ = ((M - 21 • 1) * (Nᵀ * (K - 10 • 1))) * (K - 3 • 1) := by
        rw [hshift 10]
      _ = ((M - 21 • 1) * Nᵀ) * (K - 10 • 1) * (K - 3 • 1) := by
        simp only [Matrix.mul_assoc]
      _ = (Nᵀ * (K - 21 • 1)) * (K - 10 • 1) * (K - 3 • 1) := by
        rw [hshift 21]
      _ = Nᵀ * ((K - 21 • 1) * (K - 10 • 1) * (K - 3 • 1)) := by
        simp only [Matrix.mul_assoc]
  have hMpoly :
      (M - 21 • 1) * (M - 10 • 1) * (M - 3 • 1) * M = 0 := by
    calc
      _ = (((M - 21 • 1) * (M - 10 • 1) * (M - 3 • 1)) * Nᵀ) * N := by
        dsimp [M]
        simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [htransfer]
        have hK := pointGram_cubic G h
        change (K - 21 • 1) * (K - 10 • 1) * (K - 3 • 1) = 0 at hK
        rw [hK]
        simp
  have h18 : Bblk G - 18 • 1 = M - 21 • 1 := by
    dsimp [Bblk, M, N]
    module
  have h7 : Bblk G - 7 • 1 = M - 10 • 1 := by
    dsimp [Bblk, M, N]
    module
  have h3 : Bblk G = M - 3 • 1 := by rfl
  have hplus : Bblk G + 3 • 1 = M := by
    dsimp [Bblk, M, N]
    module
  calc
    (Bblk G - 18 • 1) * (Bblk G - 7 • 1) * Bblk G * (Bblk G + 3 • 1) =
        (M - 21 • 1) * (M - 10 • 1) * (M - 3 • 1) * M := by
          rw [h18, h7, hplus, h3]
    _ = 0 := hMpoly



theorem Gtri_symm : (Gtri G)ᵀ = Gtri G := by
  have hB := overlap_symm G
  have hsq : ((Bblk G) ^ 2)ᵀ = (Bblk G) ^ 2 := by
    rw [sq, Matrix.transpose_mul, hB]
  have hJ : ((of 1 : Matrix (Triangle G) (Triangle G) ℤ))ᵀ = of 1 := by
    ext S T
    rfl
  simp only [Gtri, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, hB, hsq, hJ]

theorem triangle_carrier_card (h : G.IsSRGWith 99 14 1 2) :
    Fintype.card (Triangle G) = 231 := by
  simpa only [Triangle, Fintype.card_coe] using triangle_count G h

theorem overlap_times_ones (h : G.IsSRGWith 99 14 1 2) :
    Bblk G * (of 1 : Matrix (Triangle G) (Triangle G) ℤ) =
      18 • (of 1 : Matrix (Triangle G) (Triangle G) ℤ) := by
  ext S T
  have hsym (U : Triangle G) : Bblk G S U = Bblk G U S := by
    have heq := congrArg (fun M : Matrix (Triangle G) (Triangle G) ℤ => M U S)
      (overlap_symm G)
    simpa only [Matrix.transpose_apply] using heq
  have hrow : (∑ U : Triangle G, Bblk G S U) = 18 := by
      calc
        _ = ∑ U : Triangle G, Bblk G U S := by
          apply Finset.sum_congr rfl
          intro U _
          exact hsym U
        _ = 18 := overlap_degree_eighteen G h S
  simpa only [Matrix.mul_apply, Matrix.of_apply, Pi.one_apply, mul_one,
    Matrix.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] using hrow

theorem ones_times_overlap (h : G.IsSRGWith 99 14 1 2) :
    (of 1 : Matrix (Triangle G) (Triangle G) ℤ) * Bblk G =
      18 • (of 1 : Matrix (Triangle G) (Triangle G) ℤ) := by
  ext S T
  simpa only [Matrix.mul_apply, Matrix.of_apply, Pi.one_apply, one_mul,
    Matrix.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, mul_one] using
    overlap_degree_eighteen G h T

theorem triangle_ones_square (h : G.IsSRGWith 99 14 1 2) :
    (of 1 : Matrix (Triangle G) (Triangle G) ℤ) *
        (of 1 : Matrix (Triangle G) (Triangle G) ℤ) =
      231 • (of 1 : Matrix (Triangle G) (Triangle G) ℤ) := by
  ext S T
  simp [Matrix.mul_apply, triangle_count G h]

theorem incidence_ones_bridge :
    (Ninc G)ᵀ * (of 1 : Matrix V V ℤ) * Ninc G =
      9 • (of 1 : Matrix (Triangle G) (Triangle G) ℤ) := by
  ext S T
  calc
    _ = ∑ v : V, (∑ u : V, Ninc G u S) * Ninc G v T := by
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ v : V, 3 * Ninc G v T := by
      rw [incidence_column_sum G S]
    _ = 9 := by
      rw [← Finset.mul_sum, incidence_column_sum G T]
      norm_num
    _ = (9 • (of 1 : Matrix (Triangle G) (Triangle G) ℤ)) S T := by
      simp

theorem pointGram_square (h : G.IsSRGWith 99 14 1 2) :
    (Ninc G * (Ninc G)ᵀ) ^ 2 =
      13 • (Ninc G * (Ninc G)ᵀ) - 30 • (1 : Matrix V V ℤ) +
        2 • (of 1 : Matrix V V ℤ) := by
  let A := G.adjMatrix ℤ
  let J : Matrix V V ℤ := of 1
  have hA : A ^ 2 = 12 • (1 : Matrix V V ℤ) - A + 2 • J :=
    point_adjacency_square G h
  have hrel :
      (7 • (1 : Matrix V V ℤ) + A) ^ 2 =
        13 • (7 • (1 : Matrix V V ℤ) + A) - 30 • 1 + 2 • J +
          (A ^ 2 - (12 • 1 - A + 2 • J)) := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, sq]
    noncomm_ring
  rw [incidence_square G h]
  change (7 • (1 : Matrix V V ℤ) + A) ^ 2 =
    13 • (7 • (1 : Matrix V V ℤ) + A) - 30 • 1 + 2 • J
  rw [hrel, hA]
  module

theorem triangleGram_cubic_relation (h : G.IsSRGWith 99 14 1 2) :
    ((Ninc G)ᵀ * Ninc G) ^ 3 =
      13 • (((Ninc G)ᵀ * Ninc G) ^ 2) -
        30 • ((Ninc G)ᵀ * Ninc G) +
        18 • (of 1 : Matrix (Triangle G) (Triangle G) ℤ) := by
  let N := Ninc G
  let M : Matrix (Triangle G) (Triangle G) ℤ := Nᵀ * N
  let K : Matrix V V ℤ := N * Nᵀ
  let Jp : Matrix V V ℤ := of 1
  let Jl : Matrix (Triangle G) (Triangle G) ℤ := of 1
  have hK : K ^ 2 = 13 • K - 30 • 1 + 2 • Jp := pointGram_square G h
  have hMsq : M ^ 2 = Nᵀ * K * N := by
    dsimp [M, K]
    simp only [pow_two, Matrix.mul_assoc]
  have hMcube : M ^ 3 = Nᵀ * K ^ 2 * N := by
    dsimp [M, K]
    simp only [pow_succ, pow_zero, mul_one, one_mul, Matrix.mul_assoc]
  have hJN : Nᵀ * Jp * N = 9 • Jl := incidence_ones_bridge G
  change M ^ 3 = 13 • M ^ 2 - 30 • M + 18 • Jl
  calc
    M ^ 3 = Nᵀ * K ^ 2 * N := hMcube
    _ = Nᵀ * (13 • K - 30 • 1 + 2 • Jp) * N := by rw [hK]
    _ = 13 • (Nᵀ * K * N) - 30 • (Nᵀ * N) + 2 • (Nᵀ * Jp * N) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    _ = 13 • M ^ 2 - 30 • M + 18 • Jl := by
      rw [← hMsq, hJN]
      module

theorem overlap_cubic_relation (h : G.IsSRGWith 99 14 1 2) :
    (Bblk G) ^ 3 = 4 • (Bblk G) ^ 2 + 21 • Bblk G +
      18 • (of 1 : Matrix (Triangle G) (Triangle G) ℤ) := by
  let M : Matrix (Triangle G) (Triangle G) ℤ := (Ninc G)ᵀ * Ninc G
  let J : Matrix (Triangle G) (Triangle G) ℤ := of 1
  have hM : M ^ 3 - 13 • M ^ 2 + 30 • M = 18 • J := by
    have hc := triangleGram_cubic_relation G h
    change M ^ 3 = 13 • M ^ 2 - 30 • M + 18 • J at hc
    rw [hc]
    module
  have hpoly :
      (Bblk G) ^ 3 - 4 • (Bblk G) ^ 2 - 21 • Bblk G =
        M ^ 3 - 13 • M ^ 2 + 30 • M := by
    change (M - 3 • 1) ^ 3 - 4 • (M - 3 • 1) ^ 2 - 21 • (M - 3 • 1) =
      M ^ 3 - 13 • M ^ 2 + 30 • M
    simp only [nsmul_eq_mul, Nat.cast_ofNat, sq]
    noncomm_ring
  have hB := hpoly.trans hM
  calc
    (Bblk G) ^ 3 =
        4 • (Bblk G) ^ 2 + 21 • Bblk G +
          ((Bblk G) ^ 3 - 4 • (Bblk G) ^ 2 - 21 • Bblk G) := by module
    _ = _ := by rw [hB]

theorem overlap_mul_Gtri (h : G.IsSRGWith 99 14 1 2) :
    Bblk G * Gtri G = 0 := by
  let B := Bblk G
  let J : Matrix (Triangle G) (Triangle G) ℤ := of 1
  have hBcube : B ^ 3 = 4 • B ^ 2 + 21 • B + 18 • J :=
    overlap_cubic_relation G h
  have hBJ : B * J = 18 • J := overlap_times_ones G h
  have hrewrite :
      B * (21 • 1 + 4 • B - B ^ 2 + J) =
        21 • B + 4 • B ^ 2 - B ^ 3 + B * J := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, sq]
    noncomm_ring
  change B * (21 • 1 + 4 • B - B ^ 2 + J) = 0
  rw [hrewrite, hBcube, hBJ]
  module

theorem ones_mul_Gtri (h : G.IsSRGWith 99 14 1 2) :
    (of 1 : Matrix (Triangle G) (Triangle G) ℤ) * Gtri G = 0 := by
  let B := Bblk G
  let J : Matrix (Triangle G) (Triangle G) ℤ := of 1
  have hJB : J * B = 18 • J := ones_times_overlap G h
  have hJJ : J * J = 231 • J := triangle_ones_square G h
  have hJBsq : J * B ^ 2 = 324 • J := by
    rw [sq, ← Matrix.mul_assoc, hJB, Matrix.smul_mul, hJB]
    module
  have hrewrite :
      J * (21 • 1 + 4 • B - B ^ 2 + J) =
        21 • J + 4 • (J * B) - J * B ^ 2 + J * J := by
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  change J * (21 • 1 + 4 • B - B ^ 2 + J) = 0
  rw [hrewrite, hJB, hJBsq, hJJ]
  module

theorem Gtri_idem (h : G.IsSRGWith 99 14 1 2) :
    Gtri G * Gtri G = 21 • Gtri G := by
  let B := Bblk G
  let J : Matrix (Triangle G) (Triangle G) ℤ := of 1
  have hBG : B * Gtri G = 0 := overlap_mul_Gtri G h
  have hJG : J * Gtri G = 0 := ones_mul_Gtri G h
  have hBsqG : B ^ 2 * Gtri G = 0 := by
    rw [sq, Matrix.mul_assoc, hBG]
    simp
  change (21 • 1 + 4 • B - B ^ 2 + J) * Gtri G = 21 • Gtri G
  rw [Matrix.add_mul, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.smul_mul, hBG, hBsqG, hJG]
  module

/-- The diagonal of the overlap-square counts the eighteen other triangles meeting a line. -/
theorem overlap_square_diagonal (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) : ((Bblk G) ^ 2) T T = 18 := by
  rw [sq, Matrix.mul_apply]
  have hentry (S : Triangle G) : Bblk G T S * Bblk G S T = Bblk G S T := by
    have hsym : Bblk G T S = Bblk G S T := by
      have hs := congrArg (fun M : Matrix (Triangle G) (Triangle G) ℤ => M S T)
        (overlap_symm G)
      simpa only [Matrix.transpose_apply] using hs
    rw [hsym]
    rcases (overlap_zero_one G h S T).1 with hz | ho
    · simp [hz]
    · simp [ho]
  calc
    (∑ S : Triangle G, Bblk G T S * Bblk G S T) =
        ∑ S : Triangle G, Bblk G S T := Finset.sum_congr rfl (fun S _ => hentry S)
    _ = 18 := overlap_degree_eighteen G h T

/-- The integer triangle Gram has constant diagonal four. -/
theorem Gtri_diagonal (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) : Gtri G T T = 4 := by
  have hB : Bblk G T T = 0 := (overlap_zero_one G h T T).2 rfl
  simp only [Gtri, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply, hB, overlap_square_diagonal G h T]
  norm_num

/-- Distinct triangles meeting at a point have zero triangle-Gram entry. -/
theorem Gtri_overlap_zero (h : G.IsSRGWith 99 14 1 2)
    (S T : Triangle G) (hST : Bblk G S T = 1) :
    Gtri G S T = 0 := by
  have hne : S ≠ T := by
    intro heq
    subst T
    have hzero := (overlap_zero_one G h S S).2 rfl
    omega
  simp only [Gtri, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply, hne, hST,
    overlap_square_adjacent_five G h S T hST]
  norm_num

/-- Each row of the literal triangle Gram sums to zero. -/
theorem Gtri_row_sum_zero (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) : ∑ U : Triangle G, Gtri G T U = 0 := by
  have hcol := congrArg (fun M : Matrix (Triangle G) (Triangle G) ℤ => M T T)
    (ones_mul_Gtri G h)
  have hcol' : (∑ U : Triangle G, Gtri G U T) = 0 := by
    simpa only [Matrix.mul_apply, Matrix.of_apply, Pi.one_apply, one_mul,
      Matrix.zero_apply] using hcol
  calc
    (∑ U : Triangle G, Gtri G T U) = ∑ U : Triangle G, Gtri G U T := by
      apply Finset.sum_congr rfl
      intro U _
      have hs := congrArg (fun M : Matrix (Triangle G) (Triangle G) ℤ => M U T)
        (Gtri_symm G)
      simpa only [Matrix.transpose_apply] using hs
    _ = 0 := hcol'

/-- The squared entries in every triangle-Gram row sum to eighty-four. -/
theorem Gtri_row_square_sum (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) : ∑ U : Triangle G, (Gtri G T U) ^ 2 = 84 := by
  have hsq := congrArg (fun M : Matrix (Triangle G) (Triangle G) ℤ => M T T)
    (Gtri_idem G h)
  have hsq' : (∑ U : Triangle G, Gtri G T U * Gtri G U T) = 84 := by
    simpa [Matrix.mul_apply, Matrix.smul_apply, Gtri_diagonal G h T,
      nsmul_eq_mul] using hsq
  calc
    (∑ U : Triangle G, (Gtri G T U) ^ 2) =
        ∑ U : Triangle G, Gtri G T U * Gtri G U T := by
      apply Finset.sum_congr rfl
      intro U _
      have hs := congrArg (fun M : Matrix (Triangle G) (Triangle G) ℤ => M U T)
        (Gtri_symm G)
      have hsym : Gtri G T U = Gtri G U T := by
        simpa only [Matrix.transpose_apply] using hs
      rw [hsym, sq]
    _ = 84 := hsq'

/-- The weighted triangle-Gram row sum isolates disjoint cross-edge counts. -/
theorem Gtri_row_weight_sum (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) :
    (∑ U : Triangle G, ((Gtri G T U) ^ 2 - Gtri G T U)) = 84 := by
  rw [Finset.sum_sub_distrib, Gtri_row_square_sum G h T, Gtri_row_sum_zero G h T]
  norm_num



theorem GtriRat_scaled_idem (h : G.IsSRGWith 99 14 1 2) :
    GtriRat G * GtriRat G = 21 • GtriRat G := by
  change (Gtri G).map (Int.castRingHom ℚ) *
    (Gtri G).map (Int.castRingHom ℚ) =
      21 • (Gtri G).map (Int.castRingHom ℚ)
  rw [← Matrix.map_mul, Gtri_idem G h]
  ext S T
  simp only [Matrix.map_apply, Matrix.smul_apply]
  norm_num [nsmul_eq_mul]

private theorem rational_idempotent_rank_eq_trace {n : Type*}
    [Fintype n] [DecidableEq n] (E : Matrix n n ℚ)
    (hE : E * E = E) : (E.rank : ℚ) = E.trace := by
  have hidem : IsIdempotentElem E.mulVecLin := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hE]
  have htr := ((LinearMap.isProj_range_iff_isIdempotentElem E.mulVecLin).mpr hidem).trace
  rw [Matrix.rank, ← htr, LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ n)]
  congr 1
  ext i j
  simp [Matrix.mulVec_single]

/-- The source's triangle Gram has rank 44 over the rationals. -/
theorem GtriRat_rank (h : G.IsSRGWith 99 14 1 2) :
    (GtriRat G).rank = 44 := by
  let E : Matrix (Triangle G) (Triangle G) ℚ := (1 / 21 : ℚ) • GtriRat G
  have hG : GtriRat G * GtriRat G = 21 • GtriRat G :=
    GtriRat_scaled_idem G h
  have hE : E * E = E := by
    dsimp [E]
    rw [Matrix.smul_mul, Matrix.mul_smul, hG]
    ext S T
    simp only [Matrix.smul_apply, smul_eq_mul]
    norm_num <;> ring
  have htrace : E.trace = 44 := by
    simp [Matrix.trace, E, GtriRat, Matrix.smul_apply, Gtri_diagonal G h]
    rw [triangle_count G h]
    norm_num
  have hnonzero : (1 / 21 : ℚ) ∈ nonZeroDivisors ℚ :=
    mem_nonZeroDivisors_of_ne_zero (by norm_num)
  have hrank := Matrix.rank_smul_of_mem_nonZeroDivisors (GtriRat G) hnonzero
  change E.rank = (GtriRat G).rank at hrank
  have hrt := rational_idempotent_rank_eq_trace E hE
  rw [htrace] at hrt
  have hErank : E.rank = 44 := by exact_mod_cast hrt
  exact hrank.symm.trans hErank

/-- The adjacency term between two incidence columns counts their literal cross edges. -/
theorem incidence_adjacency_cross_entry (S T : Triangle G) :
    ((Ninc G)ᵀ * G.adjMatrix ℤ * Ninc G) S T =
      ((G.interedges S.1 T.1).card : ℤ) := by
  classical
  have hsum :
      ((Ninc G)ᵀ * G.adjMatrix ℤ * Ninc G) S T =
        ∑ x ∈ S.1, ∑ y ∈ T.1, if G.Adj x y then (1 : ℤ) else 0 := by
    rw [Matrix.mul_assoc]
    simp [Matrix.mul_apply, Ninc, SimpleGraph.adjMatrix_apply,
      Finset.sum_ite, mul_ite, ite_mul]
  calc
    _ = ∑ x ∈ S.1, ∑ y ∈ T.1, if G.Adj x y then (1 : ℤ) else 0 := hsum
    _ = ∑ p ∈ S.1.product T.1, if G.Adj p.1 p.2 then (1 : ℤ) else 0 := by
      exact (Finset.sum_product' S.1 T.1
        (fun x y => if G.Adj x y then (1 : ℤ) else 0)).symm
    _ = ((G.interedges S.1 T.1).card : ℤ) := by
      change (∑ p ∈ S.1.product T.1, if G.Adj p.1 p.2 then (1 : ℤ) else 0) =
        (((S.1.product T.1).filter fun p => G.Adj p.1 p.2).card : ℤ)
      exact Finset.sum_boole (p := fun p : V × V => G.Adj p.1 p.2)
        (s := S.1.product T.1) (R := ℤ)

/-- The overlap square separates common points from literal point cross edges. -/
theorem overlap_square_cross_identity (h : G.IsSRGWith 99 14 1 2) :
    (Bblk G) ^ 2 = (Ninc G)ᵀ * Ninc G +
      (Ninc G)ᵀ * G.adjMatrix ℤ * Ninc G +
        9 • (1 : Matrix (Triangle G) (Triangle G) ℤ) := by
  let N := Ninc G
  let M : Matrix (Triangle G) (Triangle G) ℤ := Nᵀ * N
  let A := G.adjMatrix ℤ
  have hK : N * Nᵀ = 7 • (1 : Matrix V V ℤ) + A := incidence_square G h
  have hM2 : M ^ 2 = Nᵀ * (N * Nᵀ) * N := by
    dsimp [M]
    simp only [sq, Matrix.mul_assoc]
  have hB : (Bblk G) ^ 2 = M ^ 2 - 6 • M +
      9 • (1 : Matrix (Triangle G) (Triangle G) ℤ) := by
    change (M - 3 • 1) ^ 2 = M ^ 2 - 6 • M + 9 • 1
    simp only [nsmul_eq_mul, Nat.cast_ofNat, sq]
    noncomm_ring
  have hexpand : Nᵀ * (7 • (1 : Matrix V V ℤ) + A) * N =
      7 • M + Nᵀ * A * N := by
    dsimp [M]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_one]
  change (Bblk G) ^ 2 = M + Nᵀ * A * N + 9 • 1
  calc
    (Bblk G) ^ 2 = M ^ 2 - 6 • M + 9 • 1 := hB
    _ = Nᵀ * (N * Nᵀ) * N - 6 • M + 9 • 1 := by rw [hM2]
    _ = Nᵀ * (7 • (1 : Matrix V V ℤ) + A) * N - 6 • M + 9 • 1 := by rw [hK]
    _ = 7 • M + Nᵀ * A * N - 6 • M + 9 • 1 := by rw [hexpand]
    _ = M + Nᵀ * A * N + 9 • 1 := by module

/-- For disjoint actual triangles, a squared-overlap entry is the literal cross-edge count. -/
theorem overlap_square_disjoint_cross_count (h : G.IsSRGWith 99 14 1 2)
    (S T : Triangle G) (hd : Disjoint S.1 T.1) :
    ((Bblk G) ^ 2) S T = ((G.interedges S.1 T.1).card : ℤ) := by
  have hne : S ≠ T := by
    intro heq
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
      rw [triangle_card_three G S]
      norm_num)
    exact (Finset.disjoint_left.mp hd hx) (heq ▸ hx)
  have hM : ((Ninc G)ᵀ * Ninc G) S T = 0 := by
    rw [overlap_entry G S T]
    have hinter : S.1 ∩ T.1 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd
    simp [hinter]
  have hI : (1 : Matrix (Triangle G) (Triangle G) ℤ) S T = 0 := by
    simp [Matrix.one_apply, hne]
  have hE := incidence_adjacency_cross_entry G S T
  have hs := congrArg (fun M : Matrix (Triangle G) (Triangle G) ℤ => M S T)
    (overlap_square_cross_identity G h)
  simpa only [Matrix.add_apply, Matrix.smul_apply, hM, hI, hE,
    smul_zero, add_zero, zero_add] using hs

/-- For disjoint triangles, the triangle-Gram entry is one minus the cross-edge count. -/
theorem Gtri_disjoint_cross_entry (h : G.IsSRGWith 99 14 1 2)
    (S T : Triangle G) (hd : Disjoint S.1 T.1) :
    Gtri G S T = 1 - ((G.interedges S.1 T.1).card : ℤ) := by
  have hne : S ≠ T := by
    intro heq
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
      rw [triangle_card_three G S]
      norm_num)
    exact (Finset.disjoint_left.mp hd hx) (heq ▸ hx)
  have hB : Bblk G S T = 0 := by
    have hinter : S.1 ∩ T.1 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd
    simp [Bblk, overlap_entry G S T, Matrix.ofNat_apply, hne, hinter]
  simp only [Gtri, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply, Pi.one_apply, hne, hB,
    overlap_square_disjoint_cross_count G h S T hd, if_false, smul_zero, zero_add]
  abel

private theorem cross_weight (c : ℕ) (hc : c ≤ 3) :
    ((1 - (c : ℤ)) ^ 2 - (1 - (c : ℤ))) =
      (if c = 2 then (2 : ℤ) else 0) + (if c = 3 then 6 else 0) := by
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3 <;> simp [*]

/-- The Gram row weight detects precisely two- and three-edge disjoint partners. -/
theorem Gtri_weight_entry (h : G.IsSRGWith 99 14 1 2)
    (S U : Triangle G) :
    (Gtri G S U) ^ 2 - Gtri G S U =
      (if S = U then (12 : ℤ) else 0) +
        (if Disjoint S.1 U.1 ∧ (G.interedges S.1 U.1).card = 2 then
          (2 : ℤ) else 0) +
        (if Disjoint S.1 U.1 ∧ (G.interedges S.1 U.1).card = 3 then
          (6 : ℤ) else 0) := by
  by_cases heq : S = U
  · subst U
    have hnonempty : S.1 ≠ ∅ := by
      intro hempty
      have hc := triangle_card_three G S
      simp [hempty] at hc
    simp [Gtri_diagonal G h S, hnonempty]
  · rcases distinct_triangle_disjoint_or_overlap G h S U heq with hd | ho
    · rw [Gtri_disjoint_cross_entry G h S U hd]
      rw [cross_weight _ (disjoint_cross_card_le_three G h S U hd)]
      simp [heq, hd]
    · have hnot : ¬ Disjoint S.1 U.1 := by
        intro hd
        have hcard := ((overlap_one_iff G h S U).1 ho).2
        have hinter : S.1 ∩ U.1 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd
        simp [hinter] at hcard
      simp [heq, hnot, Gtri_overlap_zero G h S U ho]

/-- Every actual triangle has weighted total thirty-six among disjoint partners. -/
theorem local_partner_census_subtype (h : G.IsSRGWith 99 14 1 2)
    (S : Triangle G) :
    ((Finset.univ.filter fun U : Triangle G =>
        Disjoint S.1 U.1 ∧ (G.interedges S.1 U.1).card = 2).card) +
      3 * ((Finset.univ.filter fun U : Triangle G =>
        Disjoint S.1 U.1 ∧ (G.interedges S.1 U.1).card = 3).card) = 36 := by
  let c2 : Finset (Triangle G) := Finset.univ.filter fun U =>
    Disjoint S.1 U.1 ∧ (G.interedges S.1 U.1).card = 2
  let c3 : Finset (Triangle G) := Finset.univ.filter fun U =>
    Disjoint S.1 U.1 ∧ (G.interedges S.1 U.1).card = 3
  have hsum : (84 : ℤ) = 12 + 2 * (c2.card : ℤ) + 6 * (c3.card : ℤ) := by
    calc
      (84 : ℤ) = ∑ U : Triangle G,
          ((Gtri G S U) ^ 2 - Gtri G S U) :=
        (Gtri_row_weight_sum G h S).symm
      _ = ∑ U : Triangle G,
          ((if S = U then (12 : ℤ) else 0) +
          (if Disjoint S.1 U.1 ∧ (G.interedges S.1 U.1).card = 2 then
            (2 : ℤ) else 0) +
          (if Disjoint S.1 U.1 ∧ (G.interedges S.1 U.1).card = 3 then
            (6 : ℤ) else 0)) := by
        apply Finset.sum_congr rfl
        intro U _
        exact Gtri_weight_entry G h S U
      _ = 12 + 2 * (c2.card : ℤ) + 6 * (c3.card : ℤ) := by
        simp only [Finset.sum_add_distrib]
        simp [c2, c3, Finset.sum_ite, Finset.sum_const,
          nsmul_eq_mul, mul_comm]
  dsimp [c2, c3] at hsum ⊢
  omega

private theorem triangle_filter_card (P : Finset V → Prop) [DecidablePred P] :
    ((Finset.univ.filter fun T : Triangle G => P T.1).card) =
      ((G.cliqueFinset 3).filter P).card := by
  let s : Finset (Triangle G) := Finset.univ.filter fun T => P T.1
  have hmap : s.image (fun T : Triangle G => T.1) = (G.cliqueFinset 3).filter P := by
    ext U
    constructor
    · intro hU
      obtain ⟨T, hTs, hTU⟩ := Finset.mem_image.mp hU
      have hp : P T.1 := (Finset.mem_filter.mp hTs).2
      exact Finset.mem_filter.mpr ⟨hTU ▸ T.2, hTU ▸ hp⟩
    · intro hU
      obtain ⟨hcl, hp⟩ := Finset.mem_filter.mp hU
      exact Finset.mem_image.mpr ⟨⟨U, hcl⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩
  have hinj : Set.InjOn (fun T : Triangle G => T.1) s := by
    intro S _ T _ hval
    exact Subtype.ext hval
  have hcard : (s.image (fun T : Triangle G => T.1)).card = s.card :=
    Finset.card_image_iff.mpr hinj
  rw [hmap] at hcard
  exact hcard.symm

private theorem disjoint_triangle_ne (S : Triangle G) (U : Finset V)
    (hd : Disjoint S.1 U) : S.1 ≠ U := by
  intro heq
  subst U
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
    rw [triangle_card_three G S]
    norm_num)
  exact (Finset.disjoint_left.mp hd hx) hx

private theorem partner_filter_ne (S : Triangle G) (j : ℕ) :
    ((G.cliqueFinset 3).filter fun U =>
      S.1 ≠ U ∧ Disjoint S.1 U ∧ (G.interedges S.1 U).card = j) =
    ((G.cliqueFinset 3).filter fun U =>
      Disjoint S.1 U ∧ (G.interedges S.1 U).card = j) := by
  ext U
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hU, _, hd, hc⟩
    exact ⟨hU, hd, hc⟩
  · rintro ⟨hU, hd, hc⟩
    exact ⟨hU, disjoint_triangle_ne G S U hd, hd, hc⟩

/-- The local partner count uses the graph's literal unordered triangle carrier. -/
theorem local_partner_census (h : G.IsSRGWith 99 14 1 2)
    (S : Triangle G) :
    ((G.cliqueFinset 3).filter fun U =>
      S.1 ≠ U ∧ Disjoint S.1 U ∧ (G.interedges S.1 U).card = 2).card +
      3 * ((G.cliqueFinset 3).filter fun U =>
      S.1 ≠ U ∧ Disjoint S.1 U ∧ (G.interedges S.1 U).card = 3).card = 36 := by
  have hc := local_partner_census_subtype G h S
  rw [triangle_filter_card G (fun U =>
      Disjoint S.1 U ∧ (G.interedges S.1 U).card = 2),
    triangle_filter_card G (fun U =>
      Disjoint S.1 U ∧ (G.interedges S.1 U).card = 3)] at hc
  rw [partner_filter_ne G S 2, partner_filter_ne G S 3]
  exact hc

#print axioms Conway99Formal.TriangleIncidence.adjacent_common_unique
#print axioms Conway99Formal.TriangleIncidence.edge_triangle
#print axioms Conway99Formal.TriangleIncidence.triangle_card_three
#print axioms Conway99Formal.TriangleIncidence.incidence_column_sum
#print axioms Conway99Formal.TriangleIncidence.triangle_eq_of_edge
#print axioms Conway99Formal.TriangleIncidence.edge_triangle_unique
#print axioms Conway99Formal.TriangleIncidence.edge_triangle_count
#print axioms Conway99Formal.TriangleIncidence.locally_linear
#print axioms Conway99Formal.TriangleIncidence.triangle_count
#print axioms Conway99Formal.TriangleIncidence.triangles_through_vertex
#print axioms Conway99Formal.TriangleIncidence.outside_triangle_neighbor_le_one
#print axioms Conway99Formal.TriangleIncidence.disjoint_cross_matching
#print axioms Conway99Formal.TriangleIncidence.incidence_entry
#print axioms Conway99Formal.TriangleIncidence.incidence_square
#print axioms Conway99Formal.TriangleIncidence.incidence_square_real
#print axioms Conway99Formal.TriangleIncidence.overlap_identity
#print axioms Conway99Formal.TriangleIncidence.overlap_symm
#print axioms Conway99Formal.TriangleIncidence.incidence_row_sum
#print axioms Conway99Formal.TriangleIncidence.overlap_degree_eighteen
#print axioms Conway99Formal.TriangleIncidence.distinct_triangles_inter_le_one
#print axioms Conway99Formal.TriangleIncidence.overlap_entry
#print axioms Conway99Formal.TriangleIncidence.overlap_zero_one
#print axioms Conway99Formal.TriangleIncidence.overlap_neighbor_count
#print axioms Conway99Formal.TriangleIncidence.triangle_star_card_six
#print axioms Conway99Formal.TriangleIncidence.overlap_one_iff
#print axioms Conway99Formal.TriangleIncidence.triangle_star_clique
#print axioms Conway99Formal.TriangleIncidence.triangle_star_disjoint
#print axioms Conway99Formal.TriangleIncidence.overlap_neighbors_eq_star_union
#print axioms Conway99Formal.TriangleIncidence.triangle_star_cross_nonadjacent
#print axioms Conway99Formal.TriangleIncidence.overlap_locally_three_six_cliques
#print axioms Conway99Formal.TriangleIncidence.point_adjacency_square
#print axioms Conway99Formal.TriangleIncidence.point_adjacency_polynomial
#print axioms Conway99Formal.TriangleIncidence.point_adjacency_times_ones
#print axioms Conway99Formal.TriangleIncidence.pointGram_cubic
#print axioms Conway99Formal.TriangleIncidence.overlap_annihilator
#print axioms Conway99Formal.TriangleIncidence.triangle_carrier_card
#print axioms Conway99Formal.TriangleIncidence.Gtri_symm
#print axioms Conway99Formal.TriangleIncidence.overlap_times_ones
#print axioms Conway99Formal.TriangleIncidence.ones_times_overlap
#print axioms Conway99Formal.TriangleIncidence.triangle_ones_square
#print axioms Conway99Formal.TriangleIncidence.incidence_ones_bridge
#print axioms Conway99Formal.TriangleIncidence.pointGram_square
#print axioms Conway99Formal.TriangleIncidence.triangleGram_cubic_relation
#print axioms Conway99Formal.TriangleIncidence.overlap_cubic_relation
#print axioms Conway99Formal.TriangleIncidence.overlap_mul_Gtri
#print axioms Conway99Formal.TriangleIncidence.ones_mul_Gtri
#print axioms Conway99Formal.TriangleIncidence.Gtri_idem
#print axioms Conway99Formal.TriangleIncidence.overlap_square_diagonal
#print axioms Conway99Formal.TriangleIncidence.Gtri_diagonal
#print axioms Conway99Formal.TriangleIncidence.GtriRat_scaled_idem
#print axioms Conway99Formal.TriangleIncidence.GtriRat_rank
#print axioms Conway99Formal.TriangleIncidence.incidence_adjacency_cross_entry
#print axioms Conway99Formal.TriangleIncidence.disjoint_cross_card_le_three
#print axioms Conway99Formal.TriangleIncidence.overlap_square_adjacent_five
#print axioms Conway99Formal.TriangleIncidence.Gtri_overlap_zero
#print axioms Conway99Formal.TriangleIncidence.Gtri_disjoint_cross_entry
#print axioms Conway99Formal.TriangleIncidence.Gtri_row_sum_zero
#print axioms Conway99Formal.TriangleIncidence.Gtri_row_square_sum
#print axioms Conway99Formal.TriangleIncidence.Gtri_row_weight_sum
#print axioms Conway99Formal.TriangleIncidence.distinct_triangle_disjoint_or_overlap
#print axioms Conway99Formal.TriangleIncidence.Gtri_weight_entry
#print axioms Conway99Formal.TriangleIncidence.local_partner_census_subtype
#print axioms Conway99Formal.TriangleIncidence.local_partner_census
#print axioms Conway99Formal.TriangleIncidence.overlap_square_cross_identity
#print axioms Conway99Formal.TriangleIncidence.overlap_square_disjoint_cross_count

end Conway99Formal.TriangleIncidence


namespace Conway99Delta858
open Finset SimpleGraph
open Conway99Formal.TriangleBound (triangles disjointTrianglePartnerCount prismCount delta)
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The frozen local partner census, restated for the frozen `TriangleBound` counts. -/
theorem local_census (h : G.IsSRGWith 99 14 1 2) (t : Finset V) (ht : t ∈ triangles G) :
    disjointTrianglePartnerCount G 2 t + 3 * disjointTrianglePartnerCount G 3 t = 36 := by
  have hc := Conway99Formal.TriangleIncidence.local_partner_census G h ⟨t, ht⟩
  have e (j : ℕ) : disjointTrianglePartnerCount G j t = ((G.cliqueFinset 3).filter fun U =>
      t ≠ U ∧ Disjoint t U ∧ (G.interedges t U).card = j).card := by
    unfold disjointTrianglePartnerCount
    congr 1
  rw [e 2, e 3]
  exact hc
end Conway99Delta858

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    Conway99Formal.TriangleBound.delta G +
      3 * Conway99Formal.TriangleBound.prismCount G = 4158 := by
  exact Conway99Formal.TriangleBound.graph_partner_census G h
    (Conway99Delta858.local_census G h)

#print axioms Conway99Delta858.local_census
#print axioms solution
