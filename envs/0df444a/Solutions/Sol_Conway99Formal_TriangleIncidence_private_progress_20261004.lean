-- Prove2me | solution 1 for Conway99Formal.TriangleIncidence.private_progress_20261004
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T01:49:50.198692+00:00
-- url     : https://prove2.me/submissions/1923aa8c-7122-4c71-b34f-8a884f369247

import Mathlib

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

/-- The actual three-cliques of the graph. -/
abbrev Triangle := {T : Finset V // T ∈ G.cliqueFinset 3}

/-- The point by triangle incidence matrix. -/
def Ninc : Matrix V (Triangle G) ℤ :=
  fun v T => if v ∈ T.1 then 1 else 0

/-- The same literal incidence matrix over the reals. -/
def NincReal : Matrix V (Triangle G) ℝ :=
  fun v T => if v ∈ T.1 then 1 else 0

/-- The overlap matrix derived from this graph's actual triangle incidence. -/
def Bblk : Matrix (Triangle G) (Triangle G) ℤ :=
  (Ninc G)ᵀ * Ninc G - 3 • 1

theorem overlap_symm : (Bblk G)ᵀ = Bblk G := by
  simp [Bblk, Matrix.transpose_sub, Matrix.transpose_mul]

theorem overlap_identity :
    (Ninc G)ᵀ * Ninc G = 3 • (1 : Matrix (Triangle G) (Triangle G) ℤ) + Bblk G := by
  rw [Bblk]
  abel

/-- The actual triangles containing both indicated points. -/
def edgeTriangles (x y : V) : Finset (Triangle G) :=
  Finset.univ.filter fun T => x ∈ T.1 ∧ y ∈ T.1

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

end Conway99Formal.TriangleIncidence

open Conway99Formal.TriangleIncidence Matrix

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    let Tri := {T : Finset V // T ∈ G.cliqueFinset 3};
    let N : Matrix V Tri ℤ := fun v T => if v ∈ T.1 then 1 else 0;
    let B : Matrix Tri Tri ℤ := Nᵀ * N - 3 • 1;
    (G.cliqueFinset 3).card = 231 ∧
    (∀ v : V, (Finset.univ.filter fun T : Tri => v ∈ T.1).card = 7) ∧
    (∀ T : Tri, (Finset.univ.filter fun S : Tri => B S T = 1).card = 18) ∧
    N * Nᵀ = 7 • (1 : Matrix V V ℤ) + G.adjMatrix ℤ := by
  exact ⟨triangle_count G h, triangles_through_vertex G h,
    overlap_neighbor_count G h, incidence_square G h⟩

#print axioms solution
