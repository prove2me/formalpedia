-- Prove2me | solution 1 for Conway99Formal.Coclique22Server.cq09_simultaneous_equivalence_20261003
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T01:24:57.259504+00:00
-- url     : https://prove2.me/submissions/b570a531-cc43-41d5-8628-b585212b77d3

/- Private standalone proof of the five source claims and their exact simultaneous completion equivalence. -/
import Definitions.Def_Conway99_Coclique22_20261003
set_option autoImplicit false

/-!
Graph-owned triangle incidence for the Conway parameter set.

The source statements are `Conway99/Conway99/Core.lean` (Line and Obligation
namespaces) and `proofs/FOUNDATIONS.md` in the September proof library. All
objects below use one literal `SimpleGraph (Fin 99)`.
-/

namespace Conway99Formal.TriangleIncidence

open Finset Matrix SimpleGraph

variable (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj]

/-- The point by triangle incidence matrix. -/
def Ninc : Matrix (Fin 99) (Triangle G) ℤ :=
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
def edgeTriangles (x y : Fin 99) : Finset (Triangle G) :=
  Finset.univ.filter fun T => x ∈ T.1 ∧ y ∈ T.1

/-- Every line of the incidence carrier has three points. -/
theorem triangle_card_three (T : Triangle G) : T.1.card = 3 :=
  (G.mem_cliqueFinset_iff.mp T.2).card_eq

/-- Every column of the incidence matrix has sum three. -/
theorem incidence_column_sum (T : Triangle G) :
    ∑ v : Fin 99, Ninc G v T = 3 := by
  simp [Ninc, ← Finset.sum_ite, triangle_card_three G T]

/-- An adjacent pair has exactly one common neighbor. -/
theorem adjacent_common_unique (h : G.IsSRGWith 99 14 1 2)
    {x y : Fin 99} (hxy : G.Adj x y) :
    ∃! z : Fin 99, G.Adj x z ∧ G.Adj y z := by
  obtain ⟨z, hz⟩ := Fintype.card_eq_one_iff.mp (h.of_adj x y hxy)
  refine ⟨z.1, (G.mem_commonNeighbors.mp z.2), ?_⟩
  intro w hw
  have hw' : (⟨w, G.mem_commonNeighbors.mpr hw⟩ : G.commonNeighbors x y) = z :=
    hz _
  exact congrArg Subtype.val hw'

/-- Every edge extends to a triangle in the same graph. -/
theorem edge_triangle (h : G.IsSRGWith 99 14 1 2)
    {x y : Fin 99} (hxy : G.Adj x y) :
    ∃ T : Triangle G, x ∈ T.1 ∧ y ∈ T.1 := by
  obtain ⟨z, hz, _⟩ := adjacent_common_unique G h hxy
  refine ⟨⟨{x, y, z}, G.mem_cliqueFinset_iff.mpr ?_⟩, by simp, by simp⟩
  exact G.is3Clique_triple_iff.mpr ⟨hxy, hz.1, hz.2⟩

/-- An edge determines every triangle containing it by its unique third point. -/
theorem triangle_eq_of_edge (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) {x y : Fin 99} (hxy : G.Adj x y)
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
    {x y : Fin 99} (hxy : G.Adj x y) :
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
    (x y : Fin 99) (hne : x ≠ y) :
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
  have hdegree : ∀ v : Fin 99, G.degree v = 14 := fun v => h.regular.degree_eq v
  have hedges : G.edgeFinset.card = 693 := by
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp [hdegree] at hsum
    omega
  have hlinear := (locally_linear G h).card_edgeFinset
  omega

/-- Exactly seven actual triangles pass through each point. -/
theorem triangles_through_vertex (h : G.IsSRGWith 99 14 1 2) (v : Fin 99) :
    (Finset.univ.filter fun T : Triangle G => v ∈ T.1).card = 7 := by
  classical
  have hleft :
      (∑ u : Fin 99, if u ≠ v then (edgeTriangles G v u).card else 0) = 14 := by
    calc
      _ = ∑ u : Fin 99, if G.Adj v u then 1 else 0 := by
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
      (∑ u : Fin 99, if u ≠ v then (edgeTriangles G v u).card else 0) =
        2 * (Finset.univ.filter fun T : Triangle G => v ∈ T.1).card := by
    calc
      _ = ∑ u : Fin 99, ∑ T : Triangle G,
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
      _ = ∑ T : Triangle G, ∑ u : Fin 99,
          if u ≠ v ∧ v ∈ T.1 ∧ u ∈ T.1 then (1 : ℕ) else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ T : Triangle G, if v ∈ T.1 then 2 else 0 := by
            apply Finset.sum_congr rfl
            intro T _
            by_cases hvT : v ∈ T.1
            · have hcard : (T.1.erase v).card = 2 := by
                rw [Finset.card_erase_of_mem hvT, triangle_card_three G T]
              calc
                (∑ u : Fin 99,
                    if u ≠ v ∧ v ∈ T.1 ∧ u ∈ T.1 then (1 : ℕ) else 0) =
                    (Finset.univ.filter fun u => u ≠ v ∧ u ∈ T.1).card := by
                      simp [hvT]
                _ = (T.1.erase v).card := by
                  have hset : (Finset.univ.filter fun u : Fin 99 => u ≠ v ∧ u ∈ T.1) =
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
    (T : Triangle G) (v : Fin 99) (hv : v ∉ T.1) :
    (T.1.filter fun x => G.Adj v x).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  have hxT : x ∈ T.1 := (Finset.mem_filter.mp hx).1
  have hyT : y ∈ T.1 := (Finset.mem_filter.mp hy).1
  have hxyAdj : G.Adj x y :=
    (G.mem_cliqueFinset_iff.mp T.2).isClique hxT hyT hxy
  obtain ⟨z, hxz, hyz, hT⟩ := triangle_eq_of_edge G h T hxyAdj hxT hyT
  have hzT : z ∈ T.1 := hT.symm ▸ (by simp : z ∈ ({x, y, z} : Finset (Fin 99)))
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

/-- Each entry of `N Nᵀ` counts triangles through its two point indices. -/
theorem incidence_entry (x y : Fin 99) :
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
      7 • (1 : Matrix (Fin 99) (Fin 99) ℤ) + G.adjMatrix ℤ := by
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

/-- The triangle incidence row sum is seven. -/
theorem incidence_row_sum (h : G.IsSRGWith 99 14 1 2) (v : Fin 99) :
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
        (∑ S : Triangle G, ∑ v : Fin 99, Ninc G v S * Ninc G v T) - 3 := by
      simp [Bblk, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_sub_distrib,
        Matrix.ofNat_apply]
    _ = (∑ v : Fin 99, (∑ S : Triangle G, Ninc G v S) * Ninc G v T) - 3 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ = (∑ v : Fin 99, 7 * Ninc G v T) - 3 := by
      simp_rw [incidence_row_sum G h]
    _ = 7 * (∑ v : Fin 99, Ninc G v T) - 3 := by rw [Finset.mul_sum]
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
    _ = ∑ v : Fin 99, if v ∈ S.1 ∩ T.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hs : v ∈ S.1 <;> by_cases ht : v ∈ T.1 <;>
        simp [Ninc, hs, ht, Matrix.transpose_apply]
    _ = ((Finset.univ.filter fun v : Fin 99 => v ∈ S.1 ∩ T.1).card : ℤ) := by
      exact Finset.sum_boole (p := fun v : Fin 99 => v ∈ S.1 ∩ T.1)
        (s := Finset.univ) (R := ℤ)
    _ = _ := by
      have heq : (Finset.univ.filter fun v : Fin 99 => v ∈ S.1 ∩ T.1) =
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

/-- Other triangles through one point of a fixed triangle. -/
def triangleStar (T : Triangle G) (v : Fin 99) : Finset (Triangle G) :=
  Finset.univ.filter fun S => S ≠ T ∧ v ∈ S.1

theorem triangle_star_card_six (h : G.IsSRGWith 99 14 1 2)
    (T : Triangle G) (v : Fin 99) (hv : v ∈ T.1) :
    (triangleStar G T v).card = 6 := by
  have hmem : T ∈ (Finset.univ.filter fun S : Triangle G => v ∈ S.1) := by
    simp [hv]
  have hstar : triangleStar G T v =
      (Finset.univ.filter fun S : Triangle G => v ∈ S.1).erase T := by
    ext S
    simp [triangleStar, and_comm]
  rw [hstar, Finset.card_erase_of_mem hmem, triangles_through_vertex G h v]

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
#print axioms Conway99Formal.TriangleIncidence.overlap_identity
#print axioms Conway99Formal.TriangleIncidence.overlap_symm
#print axioms Conway99Formal.TriangleIncidence.incidence_row_sum
#print axioms Conway99Formal.TriangleIncidence.overlap_degree_eighteen
#print axioms Conway99Formal.TriangleIncidence.distinct_triangles_inter_le_one
#print axioms Conway99Formal.TriangleIncidence.overlap_entry
#print axioms Conway99Formal.TriangleIncidence.overlap_zero_one
#print axioms Conway99Formal.TriangleIncidence.overlap_neighbor_count
#print axioms Conway99Formal.TriangleIncidence.triangle_star_card_six

end Conway99Formal.TriangleIncidence

set_option autoImplicit false

/-! The block matrices of an actual independent 22-set in one Conway graph.
Source: `proofs/COCLIQUE22.md` §§1–2 in `archive/clean-start/proof-library.zip`. -/

namespace Conway99Formal.Coclique22

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj] (C : Coclique G)

/-- A constant-one matrix, including the rectangular cases. -/
@[simp] theorem J_apply {I K : Type*} (i : I) (k : K) : J I K i k = 1 := rfl

private theorem split_sum {G : SimpleGraph V} (C : Coclique G) (f : V → ℤ) :
    (∑ v : V, f v) = (∑ c : Inside C, f c.1) +
      (∑ u : Outside C, f u.1) := by
  have hi : (∑ v ∈ C.carrier, f v) = ∑ c : Inside C, f c.1 :=
    Finset.sum_subtype C.carrier (fun _ => Iff.rfl) f
  have ho : (∑ v ∈ C.carrierᶜ, f v) = ∑ u : Outside C, f u.1 :=
    Finset.sum_subtype C.carrierᶜ (fun _ => Iff.rfl) f
  calc
    (∑ v : V, f v) = (∑ v ∈ C.carrier, f v) +
        (∑ v ∈ C.carrierᶜ, f v) := by
      simpa using (Finset.sum_add_sum_compl C.carrier f).symm
    _ = _ := by rw [hi, ho]

private theorem inside_zero (c d : Inside C) : G.adjMatrix ℤ c.1 d.1 = 0 := by
  simp [SimpleGraph.adjMatrix_apply, C.independent c.2 d.2]

private theorem symmetry (x y : V) :
    G.adjMatrix ℤ x y = G.adjMatrix ℤ y x := by
  simp [SimpleGraph.adjMatrix_apply, G.adj_comm]

theorem adjacency_square (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix ℤ) ^ 2 =
      12 • (1 : Matrix V V ℤ) - G.adjMatrix ℤ +
        2 • (of 1 : Matrix V V ℤ) := by
  have hm := h.matrix_eq (α := ℤ)
  have hc := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := ℤ)
  rw [G.compl_adjMatrix_eq_adjMatrix_compl ℤ] at hc
  have hcomp : Gᶜ.adjMatrix ℤ =
      (of 1 : Matrix V V ℤ) - 1 - G.adjMatrix ℤ := by
    linear_combination (norm := module) hc
  rw [hcomp] at hm
  rw [hm]
  module

private theorem square_entry (h : G.IsSRGWith 99 14 1 2) (x y : V) :
    (∑ v : V, G.adjMatrix ℤ x v * G.adjMatrix ℤ v y) +
      G.adjMatrix ℤ x y = (if x = y then 12 else 0) + 2 := by
  have heq := congrArg (fun M : Matrix V V ℤ => M x y)
    (adjacency_square G h)
  simp only [sq, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply] at heq
  simp [Matrix.one_apply, Matrix.of_apply] at heq ⊢
  omega

/-- The upper-left block of the actual SRG equation. -/
theorem P_mul_transpose (h : G.IsSRGWith 99 14 1 2) :
    P G C * (P G C)ᵀ =
      12 • (1 : Matrix (Inside C) (Inside C) ℤ) +
        2 • J (Inside C) (Inside C) := by
  ext c d
  have hs := split_sum C
    (fun v => G.adjMatrix ℤ c.1 v * G.adjMatrix ℤ v d.1)
  have hz : (∑ b : Inside C,
      G.adjMatrix ℤ c.1 b.1 * G.adjMatrix ℤ b.1 d.1) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    rw [inside_zero G C c b, zero_mul]
  rw [hz, zero_add] at hs
  have he := square_entry G h c.1 d.1
  rw [inside_zero G C c d, add_zero, hs] at he
  simp only [P, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, J_apply, Subtype.coe_inj] at ⊢
  simp only [nsmul_eq_mul, mul_ite, mul_one, mul_zero] at ⊢
  have hsym (u : Outside C) :
      G.adjMatrix ℤ d.1 u.1 = G.adjMatrix ℤ u.1 d.1 :=
    symmetry G _ _
  simp_rw [hsym]
  change (∑ u : Outside C,
      G.adjMatrix ℤ c.1 u.1 * G.adjMatrix ℤ u.1 d.1) =
    (if c = d then (12 : ℤ) else 0) + 2
  simpa only [Subtype.coe_inj] using he

/-- The upper-right block of the actual SRG equation. -/
theorem P_mul_D (h : G.IsSRGWith 99 14 1 2) :
    P G C * D G C + P G C =
      2 • J (Inside C) (Outside C) := by
  ext c u
  have hs := split_sum C
    (fun v => G.adjMatrix ℤ c.1 v * G.adjMatrix ℤ v u.1)
  have hz : (∑ b : Inside C,
      G.adjMatrix ℤ c.1 b.1 * G.adjMatrix ℤ b.1 u.1) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    rw [inside_zero G C c b, zero_mul]
  rw [hz, zero_add] at hs
  have hne : c.1 ≠ u.1 := by
    intro e
    exact (Finset.mem_compl.mp u.2) (e ▸ c.2)
  have he := square_entry G h c.1 u.1
  rw [hs, if_neg hne, zero_add] at he
  simp only [P, D, Matrix.mul_apply, Matrix.add_apply,
    Matrix.submatrix_apply, Matrix.smul_apply, J_apply,
    Matrix.one_apply] at ⊢
  simp only [nsmul_eq_mul, mul_one] at ⊢
  exact he

/-- The lower-right block of the actual SRG equation. -/
theorem D_quadratic (h : G.IsSRGWith 99 14 1 2) :
    D G C * D G C + D G C + (P G C)ᵀ * P G C =
      12 • (1 : Matrix (Outside C) (Outside C) ℤ) +
        2 • J (Outside C) (Outside C) := by
  ext u v
  have hs := split_sum C
    (fun w => G.adjMatrix ℤ u.1 w * G.adjMatrix ℤ w v.1)
  have he := square_entry G h u.1 v.1
  rw [hs] at he
  have hsym (c : Inside C) :
      G.adjMatrix ℤ u.1 c.1 = G.adjMatrix ℤ c.1 u.1 :=
    symmetry G _ _
  simp_rw [hsym] at he
  simp only [P, D, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, J_apply, Subtype.coe_inj] at ⊢
  simp only [nsmul_eq_mul, mul_ite, mul_one, mul_zero] at ⊢
  change (∑ w : Outside C,
      G.adjMatrix ℤ u.1 w.1 * G.adjMatrix ℤ w.1 v.1) +
    G.adjMatrix ℤ u.1 v.1 +
    (∑ c : Inside C,
      G.adjMatrix ℤ c.1 u.1 * G.adjMatrix ℤ c.1 v.1) =
      (if u = v then (12 : ℤ) else 0) + 2
  simp only [Subtype.coe_inj] at he
  omega

/-- Every point of the specified coclique has fourteen outside neighbors. -/
theorem P_row_sum (h : G.IsSRGWith 99 14 1 2) (c : Inside C) :
    (∑ u : Outside C, P G C c u) = 14 := by
  have hr := G.adjMatrix_mulVec_const_apply_of_regular
    (α := ℤ) (a := 1) h.regular (v := c.1)
  have hr' : (∑ v : V, G.adjMatrix ℤ c.1 v) = 14 := by
    simpa [Matrix.mulVec, dotProduct, Function.const] using hr
  rw [split_sum C (fun v => G.adjMatrix ℤ c.1 v)] at hr'
  have hz : (∑ b : Inside C, G.adjMatrix ℤ c.1 b.1) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    exact inside_zero G C c b
  rw [hz, zero_add] at hr'
  simpa [P, Matrix.submatrix_apply] using hr'

/-- The two index types have the dimensions claimed in the source. -/
theorem inside_card {G : SimpleGraph V} (C : Coclique G) :
    Fintype.card (Inside C) = 22 := by
  change Fintype.card (↥C.carrier) = 22
  simpa only [Fintype.card_coe] using C.card_eq

theorem outside_card (h : G.IsSRGWith 99 14 1 2) :
    Fintype.card (Outside C) = 77 := by
  change Fintype.card (↥C.carrierᶜ) = 77
  rw [Fintype.card_coe, Finset.card_compl, h.card, C.card_eq]

private def columnDegree (u : Outside C) : ℤ :=
  ∑ c : Inside C, P G C c u

private theorem first_moment (h : G.IsSRGWith 99 14 1 2) :
    (∑ u : Outside C, columnDegree G C u) = 308 := by
  calc
    _ = ∑ c : Inside C, ∑ u : Outside C, P G C c u := Finset.sum_comm
    _ = ∑ _c : Inside C, (14 : ℤ) := by
      apply Finset.sum_congr rfl
      intro c _
      exact P_row_sum G C h c
    _ = 308 := by simp [C.card_eq]

private theorem second_moment (h : G.IsSRGWith 99 14 1 2) :
    (∑ u : Outside C, (columnDegree G C u)^2) = 1232 := by
  have hsquare (u : Outside C) :
      (columnDegree G C u)^2 =
        ∑ c : Inside C, ∑ d : Inside C,
          P G C c u * P G C d u := by
    rw [columnDegree, pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  calc
    _ = ∑ u : Outside C, ∑ c : Inside C, ∑ d : Inside C,
          P G C c u * P G C d u := by
      apply Finset.sum_congr rfl
      intro u _
      exact hsquare u
    _ = ∑ c : Inside C, ∑ d : Inside C, ∑ u : Outside C,
          P G C c u * P G C d u := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ c : Inside C, ∑ d : Inside C,
          (P G C * (P G C)ᵀ) c d := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ c : Inside C, ∑ d : Inside C,
          (12 • (1 : Matrix (Inside C) (Inside C) ℤ) +
            2 • J (Inside C) (Inside C)) c d := by
      rw [P_mul_transpose G C h]
    _ = ∑ c : Inside C, ∑ d : Inside C,
          ((if c = d then (12 : ℤ) else 0) + 2) := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, J_apply]
      simp
    _ = 1232 := by
      simp [Finset.sum_add_distrib, C.card_eq]

private theorem variance_zero (h : G.IsSRGWith 99 14 1 2) :
    (∑ u : Outside C, (columnDegree G C u - 4)^2) = 0 := by
  have hex (u : Outside C) :
      (columnDegree G C u - 4)^2 =
        (columnDegree G C u)^2 - 8 * columnDegree G C u + 16 := by ring
  calc
    _ = (∑ u : Outside C, (columnDegree G C u)^2) -
        8 * (∑ u : Outside C, columnDegree G C u) +
        16 * (Fintype.card (Outside C) : ℤ) := by
      simp_rw [hex, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = 0 := by
      rw [second_moment G C h, first_moment G C h, outside_card G C h]
      norm_num

/-- Every outside point has exactly four neighbors in the actual coclique. -/
theorem P_column_sum (h : G.IsSRGWith 99 14 1 2) (u : Outside C) :
    (∑ c : Inside C, P G C c u) = 4 := by
  have hnonneg : ∀ v ∈ (Finset.univ : Finset (Outside C)),
      0 ≤ (columnDegree G C v - 4)^2 := by
    intro v _
    positivity
  have hle : (columnDegree G C u - 4)^2 ≤ 0 := by
    have hs := Finset.single_le_sum hnonneg (Finset.mem_univ u)
    simpa only [variance_zero G C h] using hs
  have hsq : (columnDegree G C u - 4)^2 = 0 :=
    le_antisymm hle (sq_nonneg _)
  unfold columnDegree at hsq
  nlinarith

/-- The complementary induced graph has degree ten. -/
theorem D_row_sum (h : G.IsSRGWith 99 14 1 2) (u : Outside C) :
    (∑ v : Outside C, D G C u v) = 10 := by
  have hr := G.adjMatrix_mulVec_const_apply_of_regular
    (α := ℤ) (a := 1) h.regular (v := u.1)
  have hr' : (∑ v : V, G.adjMatrix ℤ u.1 v) = 14 := by
    simpa [Matrix.mulVec, dotProduct, Function.const] using hr
  rw [split_sum C (fun v => G.adjMatrix ℤ u.1 v)] at hr'
  have hi : (∑ c : Inside C, G.adjMatrix ℤ u.1 c.1) = 4 := by
    calc
      _ = ∑ c : Inside C, G.adjMatrix ℤ c.1 u.1 := by
        apply Finset.sum_congr rfl
        intro c _
        exact symmetry G _ _
      _ = ∑ c : Inside C, P G C c u := by simp [P]
      _ = 4 := P_column_sum G C h u
  rw [hi] at hr'
  change (∑ v : Outside C, G.adjMatrix ℤ u.1 v.1) = 10
  omega

/-- The actual incidence entries are binary. -/
theorem P_binary (c : Inside C) (u : Outside C) :
    P G C c u = 0 ∨ P G C c u = 1 := by
  simpa [P] using (G.isAdjMatrix_adjMatrix ℤ).zero_or_one c.1 u.1

/-- The actual outside block is a binary, symmetric, loopless adjacency matrix. -/
theorem D_adjacency : (D G C).IsAdjMatrix := by
  simpa [D] using
    (G.isAdjMatrix_adjMatrix ℤ).submatrix (fun u : Outside C => u.1)

/-- The three block equations are simultaneous consequences of the same graph. -/
theorem forward_blocks (h : G.IsSRGWith 99 14 1 2) :
    (P G C * (P G C)ᵀ =
      12 • (1 : Matrix (Inside C) (Inside C) ℤ) +
        2 • J (Inside C) (Inside C)) ∧
    (P G C * D G C + P G C =
      2 • J (Inside C) (Outside C)) ∧
    (D G C * D G C + D G C + (P G C)ᵀ * P G C =
      12 • (1 : Matrix (Outside C) (Outside C) ℤ) +
        2 • J (Outside C) (Outside C)) := by
  exact ⟨P_mul_transpose G C h, P_mul_D G C h, D_quadratic G C h⟩

/-- The complete forward binary and regularity packet. -/
theorem forward_completion (h : G.IsSRGWith 99 14 1 2) :
    Fintype.card (Inside C) = 22 ∧
    Fintype.card (Outside C) = 77 ∧
    (∀ c u, P G C c u = 0 ∨ P G C c u = 1) ∧
    (D G C).IsAdjMatrix ∧
    (∀ c, (∑ u : Outside C, P G C c u) = 14) ∧
    (∀ u, (∑ c : Inside C, P G C c u) = 4) ∧
    (∀ u, (∑ v : Outside C, D G C u v) = 10) ∧
    (P G C * (P G C)ᵀ =
      12 • (1 : Matrix (Inside C) (Inside C) ℤ) +
        2 • J (Inside C) (Inside C)) ∧
    (P G C * D G C + P G C = 2 • J (Inside C) (Outside C)) ∧
    (D G C * D G C + D G C + (P G C)ᵀ * P G C =
      12 • (1 : Matrix (Outside C) (Outside C) ℤ) +
        2 • J (Outside C) (Outside C)) := by
  obtain ⟨h11, h12, h22⟩ := forward_blocks G C h
  exact ⟨inside_card C, outside_card G C h, P_binary G C, D_adjacency G C,
    P_row_sum G C h, P_column_sum G C h, D_row_sum G C h,
    h11, h12, h22⟩

end Conway99Formal.Coclique22

#print axioms Conway99Formal.Coclique22.P_mul_transpose
#print axioms Conway99Formal.Coclique22.adjacency_square
#print axioms Conway99Formal.Coclique22.P_mul_D
#print axioms Conway99Formal.Coclique22.D_quadratic
#print axioms Conway99Formal.Coclique22.P_row_sum
#print axioms Conway99Formal.Coclique22.forward_blocks
#print axioms Conway99Formal.Coclique22.inside_card
#print axioms Conway99Formal.Coclique22.outside_card
#print axioms Conway99Formal.Coclique22.P_column_sum
#print axioms Conway99Formal.Coclique22.D_row_sum
#print axioms Conway99Formal.Coclique22.P_binary
#print axioms Conway99Formal.Coclique22.D_adjacency
#print axioms Conway99Formal.Coclique22.forward_completion

namespace Conway99Formal.Coclique22

open Matrix SimpleGraph Finset

variable {W : Type*} [Fintype W] [DecidableEq W]

private theorem walks_two (G : SimpleGraph W) [DecidableRel G.Adj]
    (v w : W) :
    (G.adjMatrix ℤ * G.adjMatrix ℤ) v w =
      (Fintype.card (G.commonNeighbors v w) : ℤ) := by
  calc
    _ = (G.adjMatrix ℤ ^ 2) v w := by rw [sq]
    _ = (Fintype.card {p : G.Walk v w // p.length = 2} : ℤ) :=
      G.adjMatrix_pow_apply_eq_card_walk (α := ℤ) 2 v w
    _ = (Fintype.card (G.commonNeighbors v w) : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ))
        (Fintype.card_congr (G.walkLengthTwoEquivCommonNeighbors v w))

theorem srg_of_matrix_equation (A : Matrix W W ℤ) (hA : A.IsAdjMatrix)
    (hcard : Fintype.card W = 99)
    (hEq : A * A + A = 12 • (1 : Matrix W W ℤ) + 2 • J W W) :
    hA.toGraph.IsSRGWith 99 14 1 2 := by
  let G := hA.toGraph
  letI : DecidableRel G.Adj := inferInstance
  have hadj : G.adjMatrix ℤ = A := hA.adjMatrix_toGraph_eq
  have hentry (v w : W) :
      (Fintype.card (G.commonNeighbors v w) : ℤ) + G.adjMatrix ℤ v w =
        (if v = w then 12 else 0) + 2 := by
    have he := congrArg (fun M : Matrix W W ℤ => M v w) hEq
    rw [← hadj] at he
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] at he
    change (G.adjMatrix ℤ * G.adjMatrix ℤ) v w + G.adjMatrix ℤ v w =
      12 * (if v = w then 1 else 0) + 2 at he
    rw [walks_two G v w] at he
    simpa [mul_ite] using he
  refine {
    card := hcard
    regular := ?_
    of_adj := ?_
    of_not_adj := ?_
  }
  · intro v
    have hv := hentry v v
    have hd : (Fintype.card (G.commonNeighbors v v) : ℤ) = G.degree v := by
      simp [SimpleGraph.commonNeighbors, SimpleGraph.degree,
        SimpleGraph.neighborFinset_def]
    rw [hd] at hv
    simp [SimpleGraph.adjMatrix_apply] at hv
    exact_mod_cast hv
  · intro v w hvw
    have he := hentry v w
    have hne : v ≠ w := hvw.ne
    have hval : G.adjMatrix ℤ v w = 1 := by
      rw [hadj]
      exact hvw
    rw [hval, if_neg hne] at he
    have hc : (Fintype.card (G.commonNeighbors v w) : ℤ) = 1 := by omega
    exact_mod_cast hc
  · intro v w hne hna
    have he := hentry v w
    have hval : G.adjMatrix ℤ v w = 0 := by
      rw [hadj]
      rcases hA.zero_or_one v w with hz | ho
      · exact hz
      · exact False.elim (hna ho)
    rw [hval, if_neg hne] at he
    have hc : (Fintype.card (G.commonNeighbors v w) : ℤ) = 2 := by omega
    exact_mod_cast hc

theorem blockMatrix_isAdjMatrix (Q : BlockCompletion) :
    (blockMatrix Q).IsAdjMatrix := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rcases i with c | u <;> rcases j with d | v
    · simp [blockMatrix, Matrix.fromBlocks_apply₁₁]
    · simpa [blockMatrix, Matrix.fromBlocks_apply₁₂] using Q.P_binary c v
    · simpa [blockMatrix, Matrix.fromBlocks_apply₂₁] using Q.P_binary d u
    · simpa [blockMatrix, Matrix.fromBlocks_apply₂₂] using Q.D_adjacency.zero_or_one u v
  · have hD : Q.Dᵀ = Q.D := Q.D_adjacency.symm
    change (blockMatrix Q)ᵀ = blockMatrix Q
    simp [blockMatrix, Matrix.fromBlocks_transpose, hD]
  · intro i
    rcases i with c | u
    · simp [blockMatrix, Matrix.fromBlocks_apply₁₁]
    · simpa [blockMatrix, Matrix.fromBlocks_apply₂₂] using
        Q.D_adjacency.apply_diag u

theorem blockMatrix_equation (Q : BlockCompletion) :
    blockMatrix Q * blockMatrix Q + blockMatrix Q =
      12 • (1 : Matrix (Fin 22 ⊕ Fin 77) (Fin 22 ⊕ Fin 77) ℤ) +
        2 • J (Fin 22 ⊕ Fin 77) (Fin 22 ⊕ Fin 77) := by
  have h21 : Q.D * Q.Pᵀ + Q.Pᵀ =
      2 • J (Fin 77) (Fin 22) := by
    have hj : (J (Fin 22) (Fin 77))ᵀ = J (Fin 77) (Fin 22) := by ext u c; rfl
    have h := congrArg Matrix.transpose Q.mixed
    have hD : Q.Dᵀ = Q.D := Q.D_adjacency.symm
    simpa [Matrix.transpose_add, Matrix.transpose_mul, hD, hj] using h
  have hleft : blockMatrix Q * blockMatrix Q + blockMatrix Q =
      Matrix.fromBlocks (Q.P * Q.Pᵀ) (Q.P * Q.D + Q.P)
        (Q.D * Q.Pᵀ + Q.Pᵀ) (Q.Pᵀ * Q.P + Q.D * Q.D + Q.D) := by
    simp [blockMatrix, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  rw [hleft]
  ext i j
  rcases i with c | u <;> rcases j with d | v
  · have he := congrArg (fun M : Matrix (Fin 22) (Fin 22) ℤ => M c d) Q.P_design
    simpa [Matrix.fromBlocks_apply₁₁, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply, J] using he
  · have he := congrArg (fun M : Matrix (Fin 22) (Fin 77) ℤ => M c v) Q.mixed
    simpa [Matrix.fromBlocks_apply₁₂, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply, J] using he
  · have he := congrArg (fun M : Matrix (Fin 77) (Fin 22) ℤ => M u d) h21
    simpa [Matrix.fromBlocks_apply₂₁, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply, J] using he
  · have he := congrArg (fun M : Matrix (Fin 77) (Fin 77) ℤ => M u v) Q.quadratic
    simp only [Matrix.add_apply] at he
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, J] at ⊢
    simpa [add_assoc, add_left_comm, add_comm, Matrix.smul_apply,
      Matrix.one_apply, J] using he

theorem blockCompletion_srg (Q : BlockCompletion) :
    (blockMatrix_isAdjMatrix Q).toGraph.IsSRGWith 99 14 1 2 := by
  apply srg_of_matrix_equation (blockMatrix Q) (blockMatrix_isAdjMatrix Q)
  · norm_num
  · exact blockMatrix_equation Q

#print axioms blockMatrix_isAdjMatrix
#print axioms blockMatrix_equation
#print axioms blockCompletion_srg


def blockGraph (Q : BlockCompletion) : SimpleGraph (Fin 22 ⊕ Fin 77) :=
  (blockMatrix_isAdjMatrix Q).toGraph

theorem blockCocliqueCarrier_card : blockCocliqueCarrier.card = 22 := by
  rw [blockCocliqueCarrier,
    Finset.card_image_of_injective _ Sum.inl_injective]
  norm_num

theorem blockCocliqueCarrier_independent (Q : BlockCompletion) :
    ∀ ⦃x⦄, x ∈ blockCocliqueCarrier →
      ∀ ⦃y⦄, y ∈ blockCocliqueCarrier → ¬ (blockGraph Q).Adj x y := by
  intro x hx y hy
  change x ∈ Finset.univ.image (Sum.inl : Fin 22 → Fin 22 ⊕ Fin 77) at hx
  change y ∈ Finset.univ.image (Sum.inl : Fin 22 → Fin 22 ⊕ Fin 77) at hy
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hy
  change blockMatrix Q (Sum.inl c) (Sum.inl d) ≠ 1
  simp [blockMatrix, Matrix.fromBlocks_apply₁₁]

/-- The binary block packet reconstructs one actual SRG and its specified independent 22-set. -/
theorem blockCompletion_graph_and_coclique (Q : BlockCompletion) :
    (blockMatrix_isAdjMatrix Q).toGraph.IsSRGWith 99 14 1 2 ∧
      ∃ C : Coclique (blockGraph Q), C.carrier = blockCocliqueCarrier := by
  refine ⟨blockCompletion_srg Q, ?_⟩
  refine ⟨{
    carrier := blockCocliqueCarrier
    card_eq := blockCocliqueCarrier_card
    independent := blockCocliqueCarrier_independent Q
  }, rfl⟩

#print axioms blockCocliqueCarrier_card
#print axioms blockCocliqueCarrier_independent
#print axioms blockCompletion_graph_and_coclique

end Conway99Formal.Coclique22

namespace Conway99Formal.Coclique22

open Matrix Finset

private abbrev CPoint := Fin 22
private abbrev OPoint := Fin 77

private theorem outsideR_isAdjMatrix (Q : SimultaneousCompletion) :
    (outsideR Q.H).IsAdjMatrix := by
  refine ⟨?_, ?_, Q.R_diag⟩
  · intro u v
    by_cases huv : u = v
    · subst v
      exact Or.inl (Q.R_diag u)
    · exact Q.R_binary_offdiag u v huv
  · exact (Matrix.isSymm_mul_transpose_self Q.H).sub
      (Matrix.isSymm_one.smul 3)

private theorem outsideR_row_sum (Q : SimultaneousCompletion) (u : OPoint) :
    (∑ v : OPoint, outsideR Q.H u v) = 6 := by
  have hh : (∑ v : OPoint, (Q.H * Q.Hᵀ) u v) = 9 := by
    calc
      _ = ∑ v : OPoint, ∑ t : OPoint, Q.H u t * Q.H v t := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
      _ = ∑ t : OPoint, ∑ v : OPoint, Q.H u t * Q.H v t :=
        Finset.sum_comm
      _ = ∑ t : OPoint, Q.H u t * (∑ v : OPoint, Q.H v t) := by
        simp only [Finset.mul_sum]
      _ = ∑ t : OPoint, Q.H u t * 3 := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Q.H_column_sum t]
      _ = (∑ t : OPoint, Q.H u t) * 3 := by rw [Finset.sum_mul]
      _ = 9 := by rw [Q.H_row_sum u]; norm_num
  calc
    _ = (∑ v : OPoint, (Q.H * Q.Hᵀ) u v) -
        (∑ v : OPoint, (3 • (1 : Matrix OPoint OPoint ℤ)) u v) := by
      simp only [outsideR, Matrix.sub_apply, Finset.sum_sub_distrib]
    _ = 9 - 3 := by rw [hh]; simp [Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply]
    _ = 6 := by norm_num

private theorem R_E_disjoint (Q : SimultaneousCompletion) (u v : OPoint)
    (hr : outsideR Q.H u v = 1) (he : Q.E u v = 1) : False := by
  have hzero := Q.R_edge_disjoint u v hr
  have hone := Q.E_edge_meets u v he
  rw [hzero] at hone
  norm_num at hone

private theorem simultaneousD_isAdjMatrix (Q : SimultaneousCompletion) :
    (simultaneousD Q).IsAdjMatrix := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    change outsideR Q.H u v + Q.E u v = 0 ∨
      outsideR Q.H u v + Q.E u v = 1
    rcases (outsideR_isAdjMatrix Q).zero_or_one u v with hr | hr
    · rcases Q.E_adjacency.zero_or_one u v with he | he <;> simp [hr, he]
    · have he : Q.E u v = 0 := by
        rcases Q.E_adjacency.zero_or_one u v with he | he
        · exact he
        · exact False.elim (R_E_disjoint Q u v hr he)
      simp [hr, he]
  · exact (outsideR_isAdjMatrix Q).symm.add Q.E_adjacency.symm
  · intro u
    change outsideR Q.H u u + Q.E u u = 0
    rw [Q.R_diag u, Q.E_adjacency.apply_diag u]
    ring

private theorem simultaneousD_row_sum (Q : SimultaneousCompletion) (u : OPoint) :
    (∑ v : OPoint, simultaneousD Q u v) = 10 := by
  calc
    _ = (∑ v : OPoint, outsideR Q.H u v) + (∑ v : OPoint, Q.E u v) := by
      simp only [simultaneousD, Matrix.add_apply, Finset.sum_add_distrib]
    _ = 6 + 4 := by rw [outsideR_row_sum Q u, Q.E_row_sum u]
    _ = 10 := by norm_num

/-- CQ09's simultaneous packet supplies CQ02's complete binary block packet. -/
def SimultaneousCompletion.toBlockCompletion (Q : SimultaneousCompletion) :
    BlockCompletion where
  P := Q.P
  D := simultaneousD Q
  P_binary := Q.P_binary
  D_adjacency := simultaneousD_isAdjMatrix Q
  P_row_sum := Q.P_row_sum
  P_column_sum := Q.P_column_sum
  D_row_sum := simultaneousD_row_sum Q
  P_design := Q.P_design
  mixed := Q.mixed
  quadratic := Q.quadratic

/-- CQ09 converse: the simultaneous P/H/E packet reconstructs an actual SRG. -/
theorem simultaneousCompletion_srg (Q : SimultaneousCompletion) :
    (blockMatrix_isAdjMatrix Q.toBlockCompletion).toGraph.IsSRGWith 99 14 1 2 :=
  blockCompletion_srg Q.toBlockCompletion

end Conway99Formal.Coclique22

#print axioms Conway99Formal.Coclique22.SimultaneousCompletion.toBlockCompletion
#print axioms Conway99Formal.Coclique22.simultaneousCompletion_srg

namespace Conway99Formal.Coclique22

/-- One simultaneous P/H/E packet constructs an actual SRG and its canonical 22-coclique. -/
theorem simultaneousCompletion_graph_and_coclique
    (Q : SimultaneousCompletion) :
    (blockMatrix_isAdjMatrix Q.toBlockCompletion).toGraph.IsSRGWith 99 14 1 2 ∧
      ∃ C : Coclique (blockGraph Q.toBlockCompletion),
        C.carrier = blockCocliqueCarrier :=
  blockCompletion_graph_and_coclique Q.toBlockCompletion

end Conway99Formal.Coclique22

#print axioms Conway99Formal.Coclique22.simultaneousCompletion_graph_and_coclique

set_option autoImplicit false

namespace Conway99Formal.Coclique22

open Matrix Finset SimpleGraph

private abbrev Split := Fin 22 ⊕ Fin 77

noncomputable instance reconstructedGraphDecidable (Q : SimultaneousCompletion) :
    DecidableRel (blockGraph Q.toBlockCompletion).Adj := by
  change DecidableRel
    ((blockMatrix_isAdjMatrix Q.toBlockCompletion).toGraph).Adj
  infer_instance

/-- The actual outside three-cliques of the graph reconstructed from one packet. -/
abbrev ReconstructedOutsideTriangle (Q : SimultaneousCompletion) :=
  {T : Finset Split //
    T ∈ (blockGraph Q.toBlockCompletion).cliqueFinset 3 ∧
      Disjoint T blockCocliqueCarrier}

def columnSupport (Q : SimultaneousCompletion) (t : Fin 77) :
    Finset (Fin 77) :=
  Finset.univ.filter fun u => Q.H u t = 1

theorem columnSupport_card (Q : SimultaneousCompletion) (t : Fin 77) :
    (columnSupport Q t).card = 3 := by
  have hsum : (∑ u : Fin 77, Q.H u t) =
      ((columnSupport Q t).card : ℤ) := by
    calc
      _ = ∑ u : Fin 77, if Q.H u t = 1 then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        rcases Q.H_binary u t with hz | ho
        · simp [hz]
        · simp [ho]
      _ = ((columnSupport Q t).card : ℤ) := by
        simp [columnSupport, Finset.sum_boole]
  rw [Q.H_column_sum t] at hsum
  exact_mod_cast hsum.symm

theorem H_overlap_entry (Q : SimultaneousCompletion) (u v : Fin 77) :
    (Q.H * Q.Hᵀ) u v =
      ((Finset.univ.filter fun t : Fin 77 =>
        Q.H u t = 1 ∧ Q.H v t = 1).card : ℤ) := by
  rw [Matrix.mul_apply]
  calc
    _ = ∑ t : Fin 77,
        if Q.H u t = 1 ∧ Q.H v t = 1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      rcases Q.H_binary u t with hu | hu <;>
        rcases Q.H_binary v t with hv | hv <;>
        simp [Matrix.transpose_apply, hu, hv]
    _ = _ := by simp [Finset.sum_boole]

private theorem R_one_of_column_pair (Q : SimultaneousCompletion)
    (u v t : Fin 77) (huv : u ≠ v)
    (hu : Q.H u t = 1) (hv : Q.H v t = 1) :
    outsideR Q.H u v = 1 := by
  have hmem : t ∈ (Finset.univ.filter fun s : Fin 77 =>
      Q.H u s = 1 ∧ Q.H v s = 1) := by
    simp [hu, hv]
  have hpos : 0 < (Finset.univ.filter fun s : Fin 77 =>
      Q.H u s = 1 ∧ Q.H v s = 1).card :=
    Finset.card_pos.mpr ⟨t, hmem⟩
  have hgram := H_overlap_entry Q u v
  have hr : outsideR Q.H u v =
      ((Finset.univ.filter fun s : Fin 77 =>
        Q.H u s = 1 ∧ Q.H v s = 1).card : ℤ) := by
    simpa [outsideR, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.ofNat_apply, huv] using hgram
  rcases Q.R_binary_offdiag u v huv with hz | ho
  · omega
  · exact ho

/-- The vertices in one H column form an actual graph triangle outside C. -/
def columnTriangle (Q : SimultaneousCompletion) (t : Fin 77) :
    ReconstructedOutsideTriangle Q := by
  let S := columnSupport Q t
  let T : Finset Split := S.image Sum.inr
  refine ⟨T, ?_, ?_⟩
  · apply (blockGraph Q.toBlockCompletion).mem_cliqueFinset_iff.mpr
    refine ⟨?_, ?_⟩
    · intro x hx y hy hne
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      have huv : u ≠ v := by
        intro heq
        exact hne (congrArg Sum.inr heq)
      have hut : Q.H u t = 1 := (Finset.mem_filter.mp hu).2
      have hvt : Q.H v t = 1 := (Finset.mem_filter.mp hv).2
      have hr := R_one_of_column_pair Q u v t huv hut hvt
      have he : Q.E u v = 0 := by
        rcases Q.E_adjacency.zero_or_one u v with hz | ho
        · exact hz
        · have hz := Q.R_edge_disjoint u v hr
          have hone := Q.E_edge_meets u v ho
          omega
      have hd : Q.toBlockCompletion.D u v = 1 := by
        change outsideR Q.H u v + Q.E u v = 1
        rw [hr, he]
        norm_num
      change blockMatrix Q.toBlockCompletion (Sum.inr u) (Sum.inr v) = 1
      simpa [blockMatrix, Matrix.fromBlocks_apply₂₂] using hd
    · have hinj : Function.Injective (Sum.inr : Fin 77 → Split) :=
        Sum.inr_injective
      simpa [T, S, Finset.card_image_of_injective _ hinj] using
        (columnSupport_card Q t)
  · apply Finset.disjoint_left.mpr
    intro x hx hxC
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    simp [blockCocliqueCarrier] at hxC

theorem columnTriangle_mem (Q : SimultaneousCompletion)
    (u t : Fin 77) :
    (Sum.inr u : Split) ∈ (columnTriangle Q t).1 ↔ Q.H u t = 1 := by
  simp [columnTriangle, columnSupport, Sum.inr_injective]

private theorem pair_column_card_le_one (Q : SimultaneousCompletion)
    (u v : Fin 77) (huv : u ≠ v) :
    (Finset.univ.filter fun t : Fin 77 =>
      Q.H u t = 1 ∧ Q.H v t = 1).card ≤ 1 := by
  have hg := H_overlap_entry Q u v
  have hr : outsideR Q.H u v =
      ((Finset.univ.filter fun t : Fin 77 =>
        Q.H u t = 1 ∧ Q.H v t = 1).card : ℤ) := by
    simpa [outsideR, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.ofNat_apply, huv] using hg
  rcases Q.R_binary_offdiag u v huv with hz | ho
  · omega
  · omega

theorem columnTriangle_injective (Q : SimultaneousCompletion) :
    Function.Injective (columnTriangle Q) := by
  intro t s hts
  obtain ⟨u, v, w, huv, _, _, hs⟩ :=
    Finset.card_eq_three.mp (columnSupport_card Q t)
  have humem : u ∈ columnSupport Q t := by
    rw [hs]
    simp
  have hvmem : v ∈ columnSupport Q t := by
    rw [hs]
    simp
  have hut : Q.H u t = 1 := by
    exact (Finset.mem_filter.mp humem).2
  have hvt : Q.H v t = 1 := by
    exact (Finset.mem_filter.mp hvmem).2
  have hus : Q.H u s = 1 :=
    (columnTriangle_mem Q u s).mp
      (by rw [← hts]; exact (columnTriangle_mem Q u t).mpr hut)
  have hvs : Q.H v s = 1 :=
    (columnTriangle_mem Q v s).mp
      (by rw [← hts]; exact (columnTriangle_mem Q v t).mpr hvt)
  have htmem : t ∈ (Finset.univ.filter fun j : Fin 77 =>
      Q.H u j = 1 ∧ Q.H v j = 1) := by simp [hut, hvt]
  have hsmem : s ∈ (Finset.univ.filter fun j : Fin 77 =>
      Q.H u j = 1 ∧ Q.H v j = 1) := by simp [hus, hvs]
  exact (Finset.card_le_one.mp (pair_column_card_le_one Q u v huv))
    t htmem s hsmem

private theorem adjacent_common_unique_generic
    (G : SimpleGraph Split) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) {x y : Split}
    (hxy : G.Adj x y) :
    ∃! z : Split, G.Adj x z ∧ G.Adj y z := by
  obtain ⟨z, hz⟩ := Fintype.card_eq_one_iff.mp (h.of_adj x y hxy)
  refine ⟨z.1, G.mem_commonNeighbors.mp z.2, ?_⟩
  intro w hw
  have hw' : (⟨w, G.mem_commonNeighbors.mpr hw⟩ :
      G.commonNeighbors x y) = z := hz _
  exact congrArg Subtype.val hw'

private theorem triangle_eq_of_edge_generic
    (G : SimpleGraph Split) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2)
    (T : Finset Split) (hT : T ∈ G.cliqueFinset 3)
    {x y : Split} (hxy : G.Adj x y)
    (hx : x ∈ T) (hy : y ∈ T) :
    ∃ z, G.Adj x z ∧ G.Adj y z ∧ T = {x, y, z} := by
  obtain ⟨z, hz, hz_unique⟩ :=
    adjacent_common_unique_generic G h hxy
  refine ⟨z, hz.1, hz.2, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    by_cases hwx : w = x
    · simp [hwx]
    by_cases hwy : w = y
    · simp [hwy]
    have hclique := (G.mem_cliqueFinset_iff.mp hT).isClique
    have hxw : G.Adj x w := hclique hx hw (Ne.symm hwx)
    have hyw : G.Adj y w := hclique hy hw (Ne.symm hwy)
    have hwz := hz_unique w ⟨hxw, hyw⟩
    simp [hwz]
  · have hxy' : x ≠ y := hxy.ne
    have hxz : x ≠ z := hz.1.ne
    have hyz : y ≠ z := hz.2.ne
    simpa [hxy', hxz, hyz,
      (G.mem_cliqueFinset_iff.mp hT).card_eq]

private theorem P_entry_iff_graph_adj (Q : SimultaneousCompletion)
    (c : Fin 22) (u : Fin 77) :
    Q.P c u = 1 ↔
      (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr u) := by
  change Q.P c u = 1 ↔
    blockMatrix Q.toBlockCompletion (Sum.inl c) (Sum.inr u) = 1
  simp only [blockMatrix, Matrix.fromBlocks_apply₁₂]
  rfl

private theorem D_entry_iff_graph_adj (Q : SimultaneousCompletion)
    (u v : Fin 77) :
    simultaneousD Q u v = 1 ↔
      (blockGraph Q.toBlockCompletion).Adj (Sum.inr u) (Sum.inr v) := by
  change simultaneousD Q u v = 1 ↔
    blockMatrix Q.toBlockCompletion (Sum.inr u) (Sum.inr v) = 1
  simp only [blockMatrix, Matrix.fromBlocks_apply₂₂]
  rfl

private theorem B_overlap_entry (Q : SimultaneousCompletion)
    (u v : Fin 77) :
    (Q.Pᵀ * Q.P) u v =
      ((Finset.univ.filter fun c : Fin 22 =>
        (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr u) ∧
        (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr v)).card : ℤ) := by
  rw [Matrix.mul_apply]
  calc
    _ = ∑ c : Fin 22,
        if Q.P c u = 1 ∧ Q.P c v = 1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rcases Q.P_binary c u with hu | hu <;>
        rcases Q.P_binary c v with hv | hv <;>
        simp [Matrix.transpose_apply, hu, hv]
    _ = ((Finset.univ.filter fun c : Fin 22 =>
        (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr u) ∧
        (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr v)).card : ℤ) := by
      simp_rw [P_entry_iff_graph_adj]
      simp [Finset.sum_boole]

private theorem outside_vertex_of_triangle (Q : SimultaneousCompletion)
    (T : ReconstructedOutsideTriangle Q) {x : Split} (hx : x ∈ T.1) :
    ∃ u : Fin 77, x = Sum.inr u := by
  cases x with
  | inl c =>
      have hxC : (Sum.inl c : Split) ∈ blockCocliqueCarrier := by
        simp [blockCocliqueCarrier]
      exact False.elim ((Finset.disjoint_left.mp T.2.2) hx hxC)
  | inr u => exact ⟨u, rfl⟩

private theorem B_zero_of_outside_triangle_edge
    (Q : SimultaneousCompletion) (u v w : Fin 77)
    (huv : (blockGraph Q.toBlockCompletion).Adj (Sum.inr u) (Sum.inr v))
    (huw : (blockGraph Q.toBlockCompletion).Adj (Sum.inr u) (Sum.inr w))
    (hvw : (blockGraph Q.toBlockCompletion).Adj (Sum.inr v) (Sum.inr w)) :
    (Q.Pᵀ * Q.P) u v = 0 := by
  let G := blockGraph Q.toBlockCompletion
  have hG : G.IsSRGWith 99 14 1 2 := simultaneousCompletion_srg Q
  obtain ⟨_, _, hunique⟩ := adjacent_common_unique_generic G hG huv
  have hnone (c : Fin 22) :
      ¬ (G.Adj (Sum.inl c) (Sum.inr u) ∧
        G.Adj (Sum.inl c) (Sum.inr v)) := by
    rintro ⟨hcu, hcv⟩
    have hEq : (Sum.inl c : Split) = Sum.inr w :=
      (hunique (Sum.inl c) ⟨hcu.symm, hcv.symm⟩).trans
        (hunique (Sum.inr w) ⟨huw, hvw⟩).symm
    cases hEq
  have hempty :
      (Finset.univ.filter fun c : Fin 22 =>
        G.Adj (Sum.inl c) (Sum.inr u) ∧
          G.Adj (Sum.inl c) (Sum.inr v)) = ∅ := by
    ext c
    simp [hnone c]
  rw [B_overlap_entry Q u v, hempty]
  norm_num

private theorem R_one_of_outside_triangle_edge
    (Q : SimultaneousCompletion) (u v w : Fin 77)
    (huv : (blockGraph Q.toBlockCompletion).Adj (Sum.inr u) (Sum.inr v))
    (huw : (blockGraph Q.toBlockCompletion).Adj (Sum.inr u) (Sum.inr w))
    (hvw : (blockGraph Q.toBlockCompletion).Adj (Sum.inr v) (Sum.inr w)) :
    outsideR Q.H u v = 1 := by
  have hB := B_zero_of_outside_triangle_edge Q u v w huv huw hvw
  have hE : Q.E u v = 0 := by
    rcases Q.E_adjacency.zero_or_one u v with hz | ho
    · exact hz
    · have hone := Q.E_edge_meets u v ho
      rw [hB] at hone
      norm_num at hone
  have hD : simultaneousD Q u v = 1 :=
    (D_entry_iff_graph_adj Q u v).mpr huv
  change outsideR Q.H u v + Q.E u v = 1 at hD
  rw [hE] at hD
  omega

theorem columnTriangle_surjective (Q : SimultaneousCompletion) :
    Function.Surjective (columnTriangle Q) := by
  intro T
  let G := blockGraph Q.toBlockCompletion
  have hG : G.IsSRGWith 99 14 1 2 := simultaneousCompletion_srg Q
  have hclique := (G.mem_cliqueFinset_iff.mp T.2.1).isClique
  have hcard := (G.mem_cliqueFinset_iff.mp T.2.1).card_eq
  obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Finset.card_eq_three.mp hcard
  have hx : x ∈ T.1 := by rw [hset]; simp
  have hy : y ∈ T.1 := by rw [hset]; simp
  have hz : z ∈ T.1 := by rw [hset]; simp
  obtain ⟨u, rfl⟩ := outside_vertex_of_triangle Q T hx
  obtain ⟨v, rfl⟩ := outside_vertex_of_triangle Q T hy
  obtain ⟨w, rfl⟩ := outside_vertex_of_triangle Q T hz
  have huv : G.Adj (Sum.inr u) (Sum.inr v) :=
    hclique hx hy hxy
  have huw : G.Adj (Sum.inr u) (Sum.inr w) :=
    hclique hx hz hxz
  have hvw : G.Adj (Sum.inr v) (Sum.inr w) :=
    hclique hy hz hyz
  have hR := R_one_of_outside_triangle_edge Q u v w huv huw hvw
  have huvNe : u ≠ v := by
    intro heq
    exact huv.ne (congrArg Sum.inr heq)
  have hgram := H_overlap_entry Q u v
  have hcardPair :
      (Finset.univ.filter fun t : Fin 77 =>
        Q.H u t = 1 ∧ Q.H v t = 1).card = 1 := by
    have heq : outsideR Q.H u v =
        ((Finset.univ.filter fun t : Fin 77 =>
          Q.H u t = 1 ∧ Q.H v t = 1).card : ℤ) := by
      simpa [outsideR, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, Matrix.ofNat_apply, huvNe] using hgram
    omega
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcardPair
  have htmem : t ∈ (Finset.univ.filter fun s : Fin 77 =>
      Q.H u s = 1 ∧ Q.H v s = 1) := by
    rw [ht]
    simp
  have hut : Q.H u t = 1 := (Finset.mem_filter.mp htmem).2.1
  have hvt : Q.H v t = 1 := (Finset.mem_filter.mp htmem).2.2
  have htu : (Sum.inr u : Split) ∈ (columnTriangle Q t).1 :=
    (columnTriangle_mem Q u t).mpr hut
  have htv : (Sum.inr v : Split) ∈ (columnTriangle Q t).1 :=
    (columnTriangle_mem Q v t).mpr hvt
  obtain ⟨zT, hzTu, hzTv, hTset⟩ :=
    triangle_eq_of_edge_generic G hG T.1 T.2.1 huv hx hy
  obtain ⟨zH, hzHu, hzHv, hHset⟩ :=
    triangle_eq_of_edge_generic G hG
      (columnTriangle Q t).1 (columnTriangle Q t).2.1 huv htu htv
  obtain ⟨_, _, hunique⟩ := adjacent_common_unique_generic G hG huv
  have hzz : zH = zT :=
    (hunique zH ⟨hzHu, hzHv⟩).trans
      (hunique zT ⟨hzTu, hzTv⟩).symm
  refine ⟨t, ?_⟩
  apply Subtype.ext
  exact hHset.trans (by simpa [hzz] using hTset.symm)

theorem columnTriangle_bijective (Q : SimultaneousCompletion) :
    Function.Bijective (columnTriangle Q) :=
  ⟨columnTriangle_injective Q, columnTriangle_surjective Q⟩

/-- Each H entry is literal membership in its actual reconstructed triangle. -/
theorem H_eq_reconstructed_triangle_incidence (Q : SimultaneousCompletion)
    (u t : Fin 77) :
    Q.H u t = if (Sum.inr u : Split) ∈ (columnTriangle Q t).1 then 1 else 0 := by
  by_cases ht : Q.H u t = 1
  · have hm := (columnTriangle_mem Q u t).mpr ht
    simp [hm, ht]
  · have hm : (Sum.inr u : Split) ∉ (columnTriangle Q t).1 := by
      intro hm
      exact ht ((columnTriangle_mem Q u t).mp hm)
    rcases Q.H_binary u t with hz | ho
    · simp [hm, hz]
    · exact False.elim (ht ho)

end Conway99Formal.Coclique22

#print axioms Conway99Formal.Coclique22.columnSupport_card
#print axioms Conway99Formal.Coclique22.H_overlap_entry
#print axioms Conway99Formal.Coclique22.columnTriangle
#print axioms Conway99Formal.Coclique22.columnTriangle_mem
#print axioms Conway99Formal.Coclique22.columnTriangle_injective
#print axioms Conway99Formal.Coclique22.columnTriangle_surjective
#print axioms Conway99Formal.Coclique22.columnTriangle_bijective
#print axioms Conway99Formal.Coclique22.H_eq_reconstructed_triangle_incidence

namespace Conway99Formal.Coclique22

open Matrix Finset SimpleGraph

/-- Literal outside edges whose common neighbor is in the reconstructed coclique. -/
noncomputable def reconstructedE (Q : SimultaneousCompletion) :
    Matrix (Fin 77) (Fin 77) ℤ :=
  fun u v => if
      (blockGraph Q.toBlockCompletion).Adj (Sum.inr u) (Sum.inr v) ∧
        ∃ c : Fin 22,
          (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr u) ∧
          (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr v)
    then 1 else 0

theorem E_one_iff_reconstructed_edge (Q : SimultaneousCompletion)
    (u v : Fin 77) :
    Q.E u v = 1 ↔
      (blockGraph Q.toBlockCompletion).Adj (Sum.inr u) (Sum.inr v) ∧
        ∃ c : Fin 22,
          (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr u) ∧
          (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr v) := by
  constructor
  · intro he
    have hne : u ≠ v := by
      intro huv
      subst v
      have hz := Q.E_adjacency.apply_diag u
      omega
    have hr0 : outsideR Q.H u v = 0 := by
      rcases Q.R_binary_offdiag u v hne with hr | hr
      · exact hr
      · have hb0 := Q.R_edge_disjoint u v hr
        have hb1 := Q.E_edge_meets u v he
        omega
    have hd : simultaneousD Q u v = 1 := by
      change outsideR Q.H u v + Q.E u v = 1
      rw [hr0, he]
      norm_num
    have hAdj := (D_entry_iff_graph_adj Q u v).mp hd
    have hb := Q.E_edge_meets u v he
    rw [B_overlap_entry Q u v] at hb
    have hp : 0 < (Finset.univ.filter fun c : Fin 22 =>
        (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr u) ∧
        (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr v)).card := by
      omega
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hp
    exact ⟨hAdj, c, (Finset.mem_filter.mp hc).2⟩
  · rintro ⟨hAdj, c, hcu, hcv⟩
    have hc : c ∈ (Finset.univ.filter fun c : Fin 22 =>
        (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr u) ∧
        (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr v)) := by
      simp [hcu, hcv]
    have hp : 0 < (Finset.univ.filter fun c : Fin 22 =>
        (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr u) ∧
        (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr v)).card :=
      Finset.card_pos.mpr ⟨c, hc⟩
    have hb : (Q.Pᵀ * Q.P) u v ≠ 0 := by
      rw [B_overlap_entry Q u v]
      exact_mod_cast (Nat.ne_of_gt hp)
    rcases Q.E_adjacency.zero_or_one u v with hz | ho
    · have hd : simultaneousD Q u v = 1 :=
        (D_entry_iff_graph_adj Q u v).mpr hAdj
      change outsideR Q.H u v + Q.E u v = 1 at hd
      rw [hz] at hd
      have hr : outsideR Q.H u v = 1 := by omega
      exact False.elim (hb (Q.R_edge_disjoint u v hr))
    · exact ho

theorem E_eq_reconstructedE (Q : SimultaneousCompletion) :
    Q.E = reconstructedE Q := by
  ext u v
  by_cases hc :
      (blockGraph Q.toBlockCompletion).Adj (Sum.inr u) (Sum.inr v) ∧
        ∃ c : Fin 22,
          (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr u) ∧
          (blockGraph Q.toBlockCompletion).Adj (Sum.inl c) (Sum.inr v)
  · rw [(E_one_iff_reconstructed_edge Q u v).mpr hc]
    simp [reconstructedE, hc]
  · have hz : Q.E u v = 0 := by
      rcases Q.E_adjacency.zero_or_one u v with hz | ho
      · exact hz
      · exact False.elim (hc ((E_one_iff_reconstructed_edge Q u v).mp ho))
    simp [reconstructedE, hc, hz]

end Conway99Formal.Coclique22

#print axioms Conway99Formal.Coclique22.E_one_iff_reconstructed_edge
#print axioms Conway99Formal.Coclique22.E_eq_reconstructedE

/- Graph-owned outside triangles and PH packet. Source: proofs/COCLIQUE22.md §§2–3 in archive/clean-start/proof-library.zip. -/

namespace Conway99Formal.Coclique22Triangle

open Finset Matrix SimpleGraph
open Conway99Formal.Coclique22
open Conway99Formal.TriangleIncidence

variable (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj] (C : Coclique G)

theorem triangle_meets_C_at_most_one (T : Triangle G) :
    (T.1 ∩ C.carrier).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hne
  have hxT : x ∈ T.1 := (Finset.mem_inter.mp hx).1
  have hyT : y ∈ T.1 := (Finset.mem_inter.mp hy).1
  have hxC : x ∈ C.carrier := (Finset.mem_inter.mp hx).2
  have hyC : y ∈ C.carrier := (Finset.mem_inter.mp hy).2
  have hxy : G.Adj x y :=
    (G.mem_cliqueFinset_iff.mp T.2).isClique hxT hyT hne
  exact C.independent hxC hyC hxy

theorem H_binary (u : Outside C) (T : OutsideTriangle G C) :
    H G C u T = 0 ∨ H G C u T = 1 := by
  simp only [H]
  split_ifs <;> simp

theorem H_column_sum (T : OutsideTriangle G C) :
    (∑ u : Outside C, H G C u T) = 3 := by
  have hsub : ∀ v ∈ T.1.1, v ∈ C.carrierᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr
      (Finset.disjoint_left.mp T.2 hv)
  have hfilter : T.1.1.filter (fun v => v ∈ C.carrierᶜ) = T.1.1 := by
    ext v
    constructor
    · intro hv
      exact (Finset.mem_filter.mp hv).1
    · intro hv
      exact Finset.mem_filter.mpr ⟨hv, hsub v hv⟩
  have hsum : (∑ u : Outside C, H G C u T) =
      ((T.1.1.filter fun v => v ∈ C.carrierᶜ).card : ℤ) := by
    calc
      _ = ∑ v ∈ C.carrierᶜ, if v ∈ T.1.1 then (1 : ℤ) else 0 := by
        simpa only [H] using
          (Finset.sum_subtype C.carrierᶜ (fun _ => Iff.rfl)
            (fun v => if v ∈ T.1.1 then (1 : ℤ) else 0)).symm
      _ = ((T.1.1.filter fun v => v ∈ C.carrierᶜ).card : ℤ) := by
        rw [Finset.sum_boole]
        have heq : (C.carrierᶜ.filter fun v => v ∈ T.1.1) =
            T.1.1.filter (fun v => v ∈ C.carrierᶜ) := by
          ext v
          simp only [Finset.mem_filter]
          tauto
        rw [heq]
  rw [hsum, hfilter, triangle_card_three G T.1]
  norm_num

theorem E_plus_R_eq_D : E G C + R G C = D G C := by
  ext u v
  by_cases hAdj : G.Adj u.1 v.1
  · by_cases hC : ∃ c : Inside C,
        G.Adj c.1 u.1 ∧ G.Adj c.1 v.1
    · simp [E, R, D, SimpleGraph.adjMatrix_apply, hAdj, hC]
    · simp [E, R, D, SimpleGraph.adjMatrix_apply, hAdj, hC]
  · simp [E, R, D, SimpleGraph.adjMatrix_apply, hAdj]

/-- This is the unique-common-neighbor form of the edge split. On a D-edge,
the P-column overlap is either zero or one by λ=1 and equals one precisely
when its unique graph triangle meets C. -/
def EdgeMatrixBridge (h : G.IsSRGWith 99 14 1 2) : Prop :=
  ∀ u v : Outside C,
    E G C u v = D G C u v * ((P G C)ᵀ * P G C) u v

private theorem P_overlap_entry (u v : Outside C) :
    ((P G C)ᵀ * P G C) u v =
      ((Finset.univ.filter fun c : Inside C =>
        G.Adj c.1 u.1 ∧ G.Adj c.1 v.1).card : ℤ) := by
  rw [Matrix.mul_apply]
  calc
    _ = ∑ c : Inside C,
        if G.Adj c.1 u.1 ∧ G.Adj c.1 v.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hcu : G.Adj c.1 u.1 <;>
        by_cases hcv : G.Adj c.1 v.1 <;>
        simp [P, SimpleGraph.adjMatrix_apply, Matrix.transpose_apply,
          hcu, hcv]
    _ = _ := Finset.sum_boole
      (p := fun c : Inside C => G.Adj c.1 u.1 ∧ G.Adj c.1 v.1)
      (s := Finset.univ) (R := ℤ)

/-- Candidate proof of the first graph bridge. The λ=1 unique common neighbor
turns a nonzero P-column overlap on a D-edge into exactly one. -/
theorem edge_matrix_bridge (h : G.IsSRGWith 99 14 1 2) :
    EdgeMatrixBridge G C h := by
  intro u v
  by_cases huv : G.Adj u.1 v.1
  · obtain ⟨z, hz, huniq⟩ := adjacent_common_unique G h huv
    by_cases hC : ∃ c : Inside C,
        G.Adj c.1 u.1 ∧ G.Adj c.1 v.1
    · obtain ⟨c, hcu, hcv⟩ := hC
      have hExists : ∃ d : Inside C,
          G.Adj d.1 u.1 ∧ G.Adj d.1 v.1 := ⟨c, hcu, hcv⟩
      have hsingleton :
          (Finset.univ.filter fun d : Inside C =>
            G.Adj d.1 u.1 ∧ G.Adj d.1 v.1) = {c} := by
        ext d
        constructor
        · intro hd
          have hdu := (Finset.mem_filter.mp hd).2.1
          have hdv := (Finset.mem_filter.mp hd).2.2
          have hdz : d.1 = z := huniq d.1 ⟨hdu.symm, hdv.symm⟩
          have hcz : c.1 = z := huniq c.1 ⟨hcu.symm, hcv.symm⟩
          exact Finset.mem_singleton.mpr (Subtype.ext (hdz.trans hcz.symm))
        · intro hd
          have hdc : d = c := Finset.mem_singleton.mp hd
          subst d
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hcu, hcv⟩⟩
      rw [P_overlap_entry G C u v, hsingleton]
      simp [E, D, SimpleGraph.adjMatrix_apply, huv, hExists]
    · have hempty :
          (Finset.univ.filter fun d : Inside C =>
            G.Adj d.1 u.1 ∧ G.Adj d.1 v.1) = ∅ := by
        ext d
        constructor
        · intro hd
          exact False.elim (hC ⟨d, (Finset.mem_filter.mp hd).2⟩)
        · intro hd
          simp at hd
      rw [P_overlap_entry G C u v, hempty]
      simp [E, D, SimpleGraph.adjMatrix_apply, huv, hC]
  · simp [E, D, SimpleGraph.adjMatrix_apply, huv]

/-- The four E-neighbors are forced by the mixed SRG block equation. -/
theorem E_row_sum_from_bridge (h : G.IsSRGWith 99 14 1 2)
    (hEdge : EdgeMatrixBridge G C h) (u : Outside C) :
    (∑ v : Outside C, E G C u v) = 4 := by
  have hDsym (v : Outside C) : D G C u v = D G C v u := by
    simp [D, SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hPD (c : Inside C) :
      (P G C * D G C) c u = 2 - P G C c u := by
    have hm := congrArg
      (fun M : Matrix (Inside C) (Outside C) ℤ => M c u)
      (P_mul_D G C h)
    simp only [Matrix.add_apply, Matrix.smul_apply, J_apply,
      nsmul_eq_mul, mul_one] at hm
    omega
  calc
    (∑ v : Outside C, E G C u v) =
        ∑ v : Outside C, D G C u v *
          (∑ c : Inside C, P G C c u * P G C c v) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hEdge u v]
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ c : Inside C, P G C c u *
          (∑ v : Outside C, P G C c v * D G C v u) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro v _
      rw [← hDsym v]
      ring
    _ = ∑ c : Inside C, P G C c u * (2 - P G C c u) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← Matrix.mul_apply, hPD c]
    _ = ∑ c : Inside C, P G C c u := by
      apply Finset.sum_congr rfl
      intro c _
      rcases P_binary G C c u with hz | ho
      · simp [hz]
      · simp [ho]
    _ = 4 := P_column_sum G C h u

theorem R_row_sum_from_bridge (h : G.IsSRGWith 99 14 1 2)
    (hEdge : EdgeMatrixBridge G C h) (u : Outside C) :
    (∑ v : Outside C, R G C u v) = 6 := by
  have hs := congrArg
    (fun M : Matrix (Outside C) (Outside C) ℤ =>
      ∑ v : Outside C, M u v) (E_plus_R_eq_D G C)
  simp only [Matrix.add_apply, Finset.sum_add_distrib] at hs
  rw [E_row_sum_from_bridge G C h hEdge u, D_row_sum G C h u] at hs
  omega

/-!
The finite graph bridges are packaged below before their candidate proofs.
The proof route uses λ=1 to show `E = D ⊙ (PᵀP)` and to identify each R-edge
with its unique outside triangle. Summing the off-diagonal H Gram entries
then forces H row sum three; double counting gives 77 outside triangles.
-/

def GraphTriangleBridges (h : G.IsSRGWith 99 14 1 2) : Prop :=
  Fintype.card (OutsideTriangle G C) = 77 ∧
  (∀ u : Outside C,
    (∑ T : OutsideTriangle G C, H G C u T) = 3) ∧
  EdgeMatrixBridge G C h

/-- An outside triangle's three P blocks are pairwise disjoint. -/
theorem outside_triangle_C_neighbor_le_one
    (h : G.IsSRGWith 99 14 1 2)
    (T : OutsideTriangle G C) (c : Inside C) :
    (T.1.1.filter fun v => G.Adj c.1 v).card ≤ 1 := by
  have hc : c.1 ∉ T.1.1 := by
    intro hmem
    exact (Finset.disjoint_left.mp T.2 hmem) c.2
  exact outside_triangle_neighbor_le_one G h T.1 c.1 hc

/-- Every entry of `H Hᵀ` counts actual outside triangles through the two
outside points. The rest of its evaluation is a unique-edge-triangle argument. -/
theorem H_overlap_entry (u v : Outside C) :
    (H G C * (H G C)ᵀ) u v =
      ((Finset.univ.filter fun T : OutsideTriangle G C =>
        u.1 ∈ T.1.1 ∧ v.1 ∈ T.1.1).card : ℤ) := by
  rw [Matrix.mul_apply]
  calc
    _ = ∑ T : OutsideTriangle G C,
        if u.1 ∈ T.1.1 ∧ v.1 ∈ T.1.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      by_cases hu : u.1 ∈ T.1.1 <;> by_cases hv : v.1 ∈ T.1.1 <;>
        simp [H, hu, hv, Matrix.transpose_apply]
    _ = _ := Finset.sum_boole
      (p := fun T : OutsideTriangle G C =>
        u.1 ∈ T.1.1 ∧ v.1 ∈ T.1.1)
      (s := Finset.univ) (R := ℤ)

/-- Reindex the matrix entry to the C-neighbors of an outside triangle. -/
theorem PH_entry (c : Inside C) (T : OutsideTriangle G C) :
    (P G C * H G C) c T =
      ((T.1.1.filter fun v => G.Adj c.1 v).card : ℤ) := by
  rw [Matrix.mul_apply]
  have hsub : ∀ v ∈ T.1.1, v ∈ C.carrierᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr (Finset.disjoint_left.mp T.2 hv)
  calc
    _ = ∑ u : Outside C,
        if u.1 ∈ T.1.1 ∧ G.Adj c.1 u.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hT : u.1 ∈ T.1.1 <;>
        by_cases hA : G.Adj c.1 u.1 <;>
        simp [P, H, SimpleGraph.adjMatrix_apply, hT, hA]
    _ = ∑ v ∈ C.carrierᶜ,
        if v ∈ T.1.1 ∧ G.Adj c.1 v then (1 : ℤ) else 0 := by
      let f : Fin 99 → ℤ := fun v =>
        if v ∈ T.1.1 ∧ G.Adj c.1 v then 1 else 0
      have hs : (∑ v ∈ C.carrierᶜ, f v) =
          ∑ u : Outside C, f u.1 :=
        Finset.sum_subtype C.carrierᶜ (fun _ => Iff.rfl) f
      exact hs.symm
    _ = _ := by
      rw [Finset.sum_boole]
      have heq : (C.carrierᶜ.filter fun v => v ∈ T.1.1 ∧ G.Adj c.1 v) =
          T.1.1.filter (fun v => G.Adj c.1 v) := by
        ext v
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨_, hvT, hvA⟩
          exact ⟨hvT, hvA⟩
        · rintro ⟨hvT, hvA⟩
          exact ⟨hsub v hvT, hvT, hvA⟩
      rw [heq]

theorem PH_binary (h : G.IsSRGWith 99 14 1 2)
    (c : Inside C) (T : OutsideTriangle G C) :
    (P G C * H G C) c T = 0 ∨
      (P G C * H G C) c T = 1 := by
  rw [PH_entry G C c T]
  have hle := outside_triangle_C_neighbor_le_one G C h T c
  omega

private theorem outside_triangle_unique (h : G.IsSRGWith 99 14 1 2)
    {u v : Outside C} (huv : G.Adj u.1 v.1)
    (S T : OutsideTriangle G C)
    (huS : u.1 ∈ S.1.1) (hvS : v.1 ∈ S.1.1)
    (huT : u.1 ∈ T.1.1) (hvT : v.1 ∈ T.1.1) : S = T := by
  obtain ⟨U, _, hU⟩ := edge_triangle_unique G h huv
  apply Subtype.ext
  exact (hU S.1 ⟨huS, hvS⟩).trans (hU T.1 ⟨huT, hvT⟩).symm

/-- R is exactly the edge relation carried by an actual outside triangle. -/
private theorem R_one_iff_outside_triangle (h : G.IsSRGWith 99 14 1 2)
    {u v : Outside C} (hne : u ≠ v) :
    R G C u v = 1 ↔
      ∃ T : OutsideTriangle G C, u.1 ∈ T.1.1 ∧ v.1 ∈ T.1.1 := by
  constructor
  · intro hR
    have hcond : G.Adj u.1 v.1 ∧
        ¬ ∃ c : Inside C, G.Adj c.1 u.1 ∧ G.Adj c.1 v.1 := by
      by_cases hc : G.Adj u.1 v.1 ∧
          ¬ ∃ c : Inside C, G.Adj c.1 u.1 ∧ G.Adj c.1 v.1
      · exact hc
      · change (if G.Adj u.1 v.1 ∧
            ¬ ∃ c : Inside C, G.Adj c.1 u.1 ∧ G.Adj c.1 v.1
          then (1 : ℤ) else 0) = 1 at hR
        rw [if_neg hc] at hR
        norm_num at hR
    obtain ⟨T, hu, hv⟩ := edge_triangle G h hcond.1
    have hdisj : Disjoint T.1 C.carrier := by
      apply Finset.disjoint_left.mpr
      intro x hxT hxC
      have hxu : x ≠ u.1 := by
        intro e
        exact (Finset.mem_compl.mp u.2) (e ▸ hxC)
      have hxv : x ≠ v.1 := by
        intro e
        exact (Finset.mem_compl.mp v.2) (e ▸ hxC)
      have hclique := (G.mem_cliqueFinset_iff.mp T.2).isClique
      exact hcond.2 ⟨⟨x, hxC⟩,
        hclique hxT hu hxu, hclique hxT hv hxv⟩
    exact ⟨⟨T, hdisj⟩, hu, hv⟩
  · rintro ⟨T, hu, hv⟩
    have hneval : u.1 ≠ v.1 := by
      intro e
      exact hne (Subtype.ext e)
    have huv : G.Adj u.1 v.1 :=
      (G.mem_cliqueFinset_iff.mp T.1.2).isClique hu hv hneval
    have hNoC : ¬ ∃ c : Inside C,
        G.Adj c.1 u.1 ∧ G.Adj c.1 v.1 := by
      rintro ⟨c, hcu, hcv⟩
      have hcnot : c.1 ∉ T.1.1 := by
        intro hcT
        exact (Finset.disjoint_left.mp T.2 hcT) c.2
      have hbound := outside_triangle_neighbor_le_one G h T.1 c.1 hcnot
      have hsub := Finset.card_le_one_iff_subsingleton.mp hbound
      have huF : u.1 ∈ T.1.1.filter (fun x => G.Adj c.1 x) :=
        Finset.mem_filter.mpr ⟨hu, hcu⟩
      have hvF : v.1 ∈ T.1.1.filter (fun x => G.Adj c.1 x) :=
        Finset.mem_filter.mpr ⟨hv, hcv⟩
      exact hneval (hsub huF hvF)
    simp [R, huv, hNoC]

/-- Off the diagonal, the outside triangle Gram entry is the R adjacency. -/
theorem H_offdiag (h : G.IsSRGWith 99 14 1 2)
    (u v : Outside C) (hne : u ≠ v) :
    (H G C * (H G C)ᵀ) u v = R G C u v := by
  let pairTris : Finset (OutsideTriangle G C) :=
    Finset.univ.filter fun T => u.1 ∈ T.1.1 ∧ v.1 ∈ T.1.1
  have hentry : (H G C * (H G C)ᵀ) u v = (pairTris.card : ℤ) :=
    H_overlap_entry G C u v
  by_cases hR : R G C u v = 1
  · obtain ⟨T, hu, hv⟩ := (R_one_iff_outside_triangle G C h hne).mp hR
    have hneval : u.1 ≠ v.1 := by
      intro e
      exact hne (Subtype.ext e)
    have huv : G.Adj u.1 v.1 :=
      (G.mem_cliqueFinset_iff.mp T.1.2).isClique hu hv hneval
    have hsingle : pairTris = {T} := by
      ext S
      constructor
      · intro hS
        have hs := (Finset.mem_filter.mp hS).2
        exact Finset.mem_singleton.mpr
          (outside_triangle_unique G C h huv S T hs.1 hs.2 hu hv)
      · intro hS
        have hST : S = T := Finset.mem_singleton.mp hS
        subst S
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hu, hv⟩⟩
    rw [hentry, hsingle]
    simp [hR]
  · have hempty : pairTris = ∅ := by
      ext T
      constructor
      · intro hT
        have ht := (Finset.mem_filter.mp hT).2
        exact False.elim (hR ((R_one_iff_outside_triangle G C h hne).mpr
          ⟨T, ht.1, ht.2⟩))
      · intro hT
        simp at hT
    have hRzero : R G C u v = 0 := by
      unfold R at hR ⊢
      split_ifs at hR ⊢ <;> omega
    rw [hentry, hempty]
    simp [hRzero]

private theorem H_diagonal (u : Outside C) :
    (H G C * (H G C)ᵀ) u u =
      ∑ T : OutsideTriangle G C, H G C u T := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro T _
  rcases H_binary G C u T with hz | ho
  · simp [Matrix.transpose_apply, hz]
  · simp [Matrix.transpose_apply, ho]

/-- The global column sum three, the off-diagonal R degree six, and binary
incidence force exactly three outside triangles through every outside point. -/
theorem H_row_sum (h : G.IsSRGWith 99 14 1 2)
    (u : Outside C) :
    (∑ T : OutsideTriangle G C, H G C u T) = 3 := by
  let row : ℤ := ∑ T : OutsideTriangle G C, H G C u T
  have hEdge := edge_matrix_bridge G C h
  have hfirst :
      (∑ v : Outside C, (H G C * (H G C)ᵀ) u v) = 3 * row := by
    calc
      _ = ∑ T : OutsideTriangle G C, H G C u T *
            (∑ v : Outside C, H G C v T) := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = ∑ T : OutsideTriangle G C, H G C u T * 3 := by
        apply Finset.sum_congr rfl
        intro T _
        rw [H_column_sum G C T]
      _ = 3 * row := by rw [← Finset.sum_mul]; dsimp [row]; ring
  have hRdiag : R G C u u = 0 := by
    simp [R, G.irrefl]
  have hsecond :
      (∑ v : Outside C, (H G C * (H G C)ᵀ) u v) = row + 6 := by
    have hsplit := Finset.sum_add_sum_compl
      ({u} : Finset (Outside C))
      (fun v => (H G C * (H G C)ᵀ) u v)
    have hsplitR := Finset.sum_add_sum_compl
      ({u} : Finset (Outside C)) (fun v => R G C u v)
    have hOutside :
        (∑ v ∈ ({u} : Finset (Outside C))ᶜ,
          (H G C * (H G C)ᵀ) u v) =
        ∑ v ∈ ({u} : Finset (Outside C))ᶜ, R G C u v := by
      apply Finset.sum_congr rfl
      intro v hv
      have hne : u ≠ v := by
        intro e
        subst v
        exact (Finset.mem_compl.mp hv) (by simp)
      exact H_offdiag G C h u v hne
    have hOutsideR :
        (∑ v ∈ ({u} : Finset (Outside C))ᶜ, R G C u v) = 6 := by
      have hdegree := R_row_sum_from_bridge G C h hEdge u
      simpa [hRdiag] using hsplitR.trans hdegree
    calc
      _ = (H G C * (H G C)ᵀ) u u +
          (∑ v ∈ ({u} : Finset (Outside C))ᶜ,
            (H G C * (H G C)ᵀ) u v) := by
        simpa using hsplit.symm
      _ = row + 6 := by rw [H_diagonal G C u, hOutside, hOutsideR]
  dsimp [row] at hfirst hsecond ⊢
  omega

/-- There are 77 actual outside triangles: both sides of the incidence
matrix have total sum 231, with three in each row and in each column. -/
theorem outside_triangle_card_seventy_seven
    (h : G.IsSRGWith 99 14 1 2) :
    Fintype.card (OutsideTriangle G C) = 77 := by
  have htotal : (3 : ℤ) * (Fintype.card (OutsideTriangle G C) : ℤ) =
      3 * 77 := by
    calc
      _ = ∑ T : OutsideTriangle G C, (3 : ℤ) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ = ∑ T : OutsideTriangle G C,
            ∑ u : Outside C, H G C u T := by
        apply Finset.sum_congr rfl
        intro T _
        exact (H_column_sum G C T).symm
      _ = ∑ u : Outside C,
            ∑ T : OutsideTriangle G C, H G C u T := Finset.sum_comm
      _ = ∑ u : Outside C, (3 : ℤ) := by
        apply Finset.sum_congr rfl
        intro u _
        exact H_row_sum G C h u
      _ = 3 * 77 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [outside_card G C h]
        ring
  omega

/-- The complete point Gram identity, now with its actual diagonal. -/
theorem H_gram (h : G.IsSRGWith 99 14 1 2) :
    H G C * (H G C)ᵀ =
      3 • (1 : Matrix (Outside C) (Outside C) ℤ) + R G C := by
  ext u v
  by_cases hEq : u = v
  · subst v
    rw [H_diagonal G C u, H_row_sum G C h u]
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.ofNat_apply, R,
      G.irrefl]
  · rw [H_offdiag G C h u v hEq]
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.ofNat_apply, hEq]

/-- This point Gram bridge follows by unique edge triangles: the diagonal
counts three through u, and an off-diagonal entry counts the unique outside
triangle on a pair exactly when that pair is an R-edge. -/
def GraphIncidenceBridge (h : G.IsSRGWith 99 14 1 2) : Prop :=
  H G C * (H G C)ᵀ =
    3 • (1 : Matrix (Outside C) (Outside C) ℤ) + R G C

/-- A precise same-graph packet for subsequent algebra. -/
def GraphPacket (h : G.IsSRGWith 99 14 1 2) : Prop :=
  GraphTriangleBridges G C h ∧ GraphIncidenceBridge G C h

theorem graph_triangle_bridges (h : G.IsSRGWith 99 14 1 2) :
    GraphTriangleBridges G C h := by
  exact ⟨outside_triangle_card_seventy_seven G C h,
    H_row_sum G C h, edge_matrix_bridge G C h⟩

theorem graph_incidence_bridge (h : G.IsSRGWith 99 14 1 2) :
    GraphIncidenceBridge G C h := H_gram G C h

theorem graph_packet (h : G.IsSRGWith 99 14 1 2) :
    GraphPacket G C h :=
  ⟨graph_triangle_bridges G C h, graph_incidence_bridge G C h⟩

/-- The row margin 42 follows from the actual H row margin 3 and the actual
P row margin 14. This proof does not assume an independent design witness. -/
theorem PH_row_sum (h : G.IsSRGWith 99 14 1 2)
    (hpacket : GraphPacket G C h) (c : Inside C) :
    (∑ T : OutsideTriangle G C, (P G C * H G C) c T) = 42 := by
  have hH := hpacket.1.2.1
  calc
    _ = ∑ u : Outside C, P G C c u *
        (∑ T : OutsideTriangle G C, H G C u T) := by
      simp only [Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ u : Outside C, P G C c u * 3 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [hH u]
    _ = 42 := by
      rw [← Finset.sum_mul, P_row_sum G C h c]
      norm_num

/-- The column margin 12 follows from the actual P column margin 4 and the
three vertices of each actual outside triangle. -/
theorem PH_column_sum (h : G.IsSRGWith 99 14 1 2)
    (T : OutsideTriangle G C) :
    (∑ c : Inside C, (P G C * H G C) c T) = 12 := by
  calc
    _ = ∑ u : Outside C,
        (∑ c : Inside C, P G C c u) * H G C u T := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∑ u : Outside C, 4 * H G C u T := by
      apply Finset.sum_congr rfl
      intro u _
      rw [P_column_sum G C h u]
    _ = 12 := by
      rw [← Finset.mul_sum, H_column_sum G C T]
      norm_num

/-- If H has its actual Gram matrix, the first mixed identity is pure matrix
algebra. The equation P D + P = 2 J is already proved in Coclique22. -/
theorem PH_mul_transpose (h : G.IsSRGWith 99 14 1 2)
    (hGram : GraphIncidenceBridge G C h) :
    (P G C * H G C) * (H G C)ᵀ =
      2 • P G C + 2 • J (Inside C) (Outside C) - P G C * E G C := by
  have hD := P_mul_D G C h
  have hER := E_plus_R_eq_D G C
  calc
    (P G C * H G C) * (H G C)ᵀ =
        P G C * (H G C * (H G C)ᵀ) := by rw [Matrix.mul_assoc]
    _ = P G C * (3 • 1 + R G C) := by rw [hGram]
    _ = 2 • P G C + 2 • J (Inside C) (Outside C) -
          P G C * E G C := by
      -- Normalize `R = D - E`, distribute, then use `P D + P = 2 J`.
      have hR : R G C = D G C - E G C := by
        rw [← hER]
        abel
      rw [hR]
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
        Matrix.mul_one]
      have hPD : P G C * D G C =
          2 • J (Inside C) (Outside C) - P G C := by
        rw [← hD]
        abel
      rw [hPD]
      module

/-- The second mixed identity uses the same actual graph packet. -/
theorem PH_mul_transpose_PH (h : G.IsSRGWith 99 14 1 2)
    (hGram : GraphIncidenceBridge G C h) :
    (P G C * H G C) * (P G C * H G C)ᵀ =
      24 • (1 : Matrix (Inside C) (Inside C) ℤ) +
      32 • J (Inside C) (Inside C) -
      P G C * E G C * (P G C)ᵀ := by
  have h11 := P_mul_transpose G C h
  have h12 := P_mul_D G C h
  have hJPT : Coclique22.J (Inside C) (Outside C) * (P G C)ᵀ =
      14 • Coclique22.J (Inside C) (Inside C) := by
    ext c d
    have hd := P_row_sum G C h d
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Coclique22.J,
      Matrix.smul_apply] using hd
  have hR : R G C = D G C - E G C := by
    have hER := E_plus_R_eq_D G C
    rw [← hER]
    abel
  calc
    (P G C * H G C) * (P G C * H G C)ᵀ =
        P G C * (H G C * (H G C)ᵀ) * (P G C)ᵀ := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = P G C * (3 • 1 + R G C) * (P G C)ᵀ := by rw [hGram]
    _ = 24 • (1 : Matrix (Inside C) (Inside C) ℤ) +
          32 • J (Inside C) (Inside C) -
          P G C * E G C * (P G C)ᵀ := by
      rw [hR]
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
        Matrix.mul_one, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul]
      -- Rewrite the two proven block equations in the distributed product.
      have hPD : P G C * D G C =
          2 • Coclique22.J (Inside C) (Outside C) - P G C := by
        rw [← h12]
        abel
      rw [hPD]
      simp only [Matrix.sub_mul, Matrix.smul_mul]
      rw [h11, hJPT]
      module

/-- CQ05/CQ07 as one forward packet owned by the specified graph and C. -/
theorem forward_outside_triangle_packet (h : G.IsSRGWith 99 14 1 2) :
    Fintype.card (OutsideTriangle G C) = 77 ∧
    (∀ u : Outside C, (∑ v : Outside C, E G C u v) = 4) ∧
    (∀ u : Outside C, (∑ v : Outside C, R G C u v) = 6) ∧
    (∀ T : OutsideTriangle G C, (∑ u : Outside C, H G C u T) = 3) ∧
    (∀ u : Outside C, (∑ T : OutsideTriangle G C, H G C u T) = 3) ∧
    (H G C * (H G C)ᵀ =
      3 • (1 : Matrix (Outside C) (Outside C) ℤ) + R G C) ∧
    (∀ c T, (P G C * H G C) c T = 0 ∨ (P G C * H G C) c T = 1) ∧
    (∀ c, (∑ T : OutsideTriangle G C, (P G C * H G C) c T) = 42) ∧
    (∀ T, (∑ c : Inside C, (P G C * H G C) c T) = 12) ∧
    ((P G C * H G C) * (H G C)ᵀ =
      2 • P G C + 2 • J (Inside C) (Outside C) - P G C * E G C) ∧
    ((P G C * H G C) * (P G C * H G C)ᵀ =
      24 • (1 : Matrix (Inside C) (Inside C) ℤ) +
      32 • J (Inside C) (Inside C) -
      P G C * E G C * (P G C)ᵀ) := by
  have hEdge := edge_matrix_bridge G C h
  have hGram := graph_incidence_bridge G C h
  exact ⟨outside_triangle_card_seventy_seven G C h,
    E_row_sum_from_bridge G C h hEdge,
    R_row_sum_from_bridge G C h hEdge,
    H_column_sum G C,
    H_row_sum G C h,
    H_gram G C h,
    PH_binary G C h,
    PH_row_sum G C h (graph_packet G C h),
    PH_column_sum G C h,
    PH_mul_transpose G C h hGram,
    PH_mul_transpose_PH G C h hGram⟩

/-- The C-triangle edge part is an actual binary adjacency matrix. -/
theorem E_adjacency : (E G C).IsAdjMatrix := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    unfold E
    split_ifs <;> simp
  · ext u v
    have hs :
        (G.Adj v.1 u.1 ∧
            ∃ c : Inside C, G.Adj c.1 v.1 ∧ G.Adj c.1 u.1) ↔
          (G.Adj u.1 v.1 ∧
            ∃ c : Inside C, G.Adj c.1 u.1 ∧ G.Adj c.1 v.1) := by
      constructor
      · rintro ⟨ha, c, hcv, hcu⟩
        exact ⟨ha.symm, c, hcu, hcv⟩
      · rintro ⟨ha, c, hcu, hcv⟩
        exact ⟨ha.symm, c, hcv, hcu⟩
    change (if G.Adj v.1 u.1 ∧
        (∃ c : Inside C, G.Adj c.1 v.1 ∧ G.Adj c.1 u.1) then
        (1 : ℤ) else 0) =
      if G.Adj u.1 v.1 ∧
        (∃ c : Inside C, G.Adj c.1 u.1 ∧ G.Adj c.1 v.1) then
        1 else 0
    simp only [hs]
  · intro u
    simp [E, G.irrefl]

/-- The outside-triangle edge part is an actual binary adjacency matrix. -/
theorem R_adjacency : (R G C).IsAdjMatrix := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    unfold R
    split_ifs <;> simp
  · ext u v
    have hs :
        (G.Adj v.1 u.1 ∧
            ¬ ∃ c : Inside C, G.Adj c.1 v.1 ∧ G.Adj c.1 u.1) ↔
          (G.Adj u.1 v.1 ∧
            ¬ ∃ c : Inside C, G.Adj c.1 u.1 ∧ G.Adj c.1 v.1) := by
      constructor
      · rintro ⟨ha, hn⟩
        refine ⟨ha.symm, ?_⟩
        rintro ⟨c, hcu, hcv⟩
        exact hn ⟨c, hcv, hcu⟩
      · rintro ⟨ha, hn⟩
        refine ⟨ha.symm, ?_⟩
        rintro ⟨c, hcv, hcu⟩
        exact hn ⟨c, hcu, hcv⟩
    change (if G.Adj v.1 u.1 ∧
        ¬ (∃ c : Inside C, G.Adj c.1 v.1 ∧ G.Adj c.1 u.1) then
        (1 : ℤ) else 0) =
      if G.Adj u.1 v.1 ∧
        ¬ (∃ c : Inside C, G.Adj c.1 u.1 ∧ G.Adj c.1 v.1) then
        1 else 0
    simp only [hs]
  · intro u
    simp [R, G.irrefl]

/-- Every actual E-edge has exactly one C-common neighbor. -/
theorem E_edge_B_one (h : G.IsSRGWith 99 14 1 2)
    (u v : Outside C) (he : E G C u v = 1) :
    ((P G C)ᵀ * P G C) u v = 1 := by
  have hAdj : G.Adj u.1 v.1 := by
    by_contra hn
    have hz : E G C u v = 0 := by simp [E, hn]
    omega
  have hD : D G C u v = 1 := by
    simp [D, SimpleGraph.adjMatrix_apply, hAdj]
  have hb := edge_matrix_bridge G C h u v
  rw [he, hD] at hb
  simpa using hb.symm

/-- Every actual R-edge has no C-common neighbor. -/
theorem R_edge_B_zero (u v : Outside C) (hr : R G C u v = 1) :
    ((P G C)ᵀ * P G C) u v = 0 := by
  have hNo : ¬ ∃ c : Inside C,
      G.Adj c.1 u.1 ∧ G.Adj c.1 v.1 := by
    by_contra hExists
    have hz : R G C u v = 0 := by
      simp [R, hExists]
    omega
  have hempty :
      (Finset.univ.filter fun c : Inside C =>
        G.Adj c.1 u.1 ∧ G.Adj c.1 v.1) = ∅ := by
    ext c
    constructor
    · intro hc
      exact False.elim (hNo ⟨c, (Finset.mem_filter.mp hc).2⟩)
    · intro hc
      simp at hc
  rw [P_overlap_entry G C u v, hempty]
  simp

end Conway99Formal.Coclique22Triangle

#print axioms Conway99Formal.Coclique22Triangle.edge_matrix_bridge
#print axioms Conway99Formal.Coclique22Triangle.E_row_sum_from_bridge
#print axioms Conway99Formal.Coclique22Triangle.R_row_sum_from_bridge
#print axioms Conway99Formal.Coclique22Triangle.outside_triangle_card_seventy_seven
#print axioms Conway99Formal.Coclique22Triangle.H_gram
#print axioms Conway99Formal.Coclique22Triangle.PH_binary
#print axioms Conway99Formal.Coclique22Triangle.PH_row_sum
#print axioms Conway99Formal.Coclique22Triangle.PH_column_sum
#print axioms Conway99Formal.Coclique22Triangle.PH_mul_transpose
#print axioms Conway99Formal.Coclique22Triangle.PH_mul_transpose_PH
#print axioms Conway99Formal.Coclique22Triangle.forward_outside_triangle_packet

set_option autoImplicit false

namespace Conway99Formal.Coclique22Triangle

open Matrix Finset
open Conway99Formal.Coclique22

variable (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj] (C : Coclique G)

noncomputable def insideIndex : Fin 22 ≃ Inside C :=
  (Fintype.equivFinOfCardEq (inside_card C)).symm

noncomputable def outsideIndex (h : G.IsSRGWith 99 14 1 2) :
    Fin 77 ≃ Outside C :=
  (Fintype.equivFinOfCardEq (outside_card G C h)).symm

noncomputable def triangleIndex (h : G.IsSRGWith 99 14 1 2) :
    Fin 77 ≃ OutsideTriangle G C :=
  (Fintype.equivFinOfCardEq
    (outside_triangle_card_seventy_seven G C h)).symm

noncomputable def indexedP (h : G.IsSRGWith 99 14 1 2) :
    Matrix (Fin 22) (Fin 77) ℤ :=
  (P G C).submatrix (insideIndex G C) (outsideIndex G C h)

noncomputable def indexedH (h : G.IsSRGWith 99 14 1 2) :
    Matrix (Fin 77) (Fin 77) ℤ :=
  (H G C).submatrix (outsideIndex G C h) (triangleIndex G C h)

noncomputable def indexedE (h : G.IsSRGWith 99 14 1 2) :
    Matrix (Fin 77) (Fin 77) ℤ :=
  (E G C).submatrix (outsideIndex G C h) (outsideIndex G C h)

noncomputable def indexedR (h : G.IsSRGWith 99 14 1 2) :
    Matrix (Fin 77) (Fin 77) ℤ :=
  (R G C).submatrix (outsideIndex G C h) (outsideIndex G C h)

noncomputable def indexedD (h : G.IsSRGWith 99 14 1 2) :
    Matrix (Fin 77) (Fin 77) ℤ :=
  (D G C).submatrix (outsideIndex G C h) (outsideIndex G C h)

theorem indexedP_design (h : G.IsSRGWith 99 14 1 2) :
    indexedP G C h * (indexedP G C h)ᵀ =
      12 • (1 : Matrix (Fin 22) (Fin 22) ℤ) +
        2 • J (Fin 22) (Fin 22) := by
  have hs := congrArg
    (fun M : Matrix (Inside C) (Inside C) ℤ =>
      M.submatrix (insideIndex G C) (insideIndex G C))
    (P_mul_transpose G C h)
  rw [indexedP, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv]
  ext c d
  have he := congrArg (fun M : Matrix (Fin 22) (Fin 22) ℤ => M c d) hs
  simpa only [two_nsmul, Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Coclique22.J_apply,
    (insideIndex G C).injective.eq_iff] using he

theorem indexedH_gram (h : G.IsSRGWith 99 14 1 2) :
    indexedH G C h * (indexedH G C h)ᵀ =
      3 • (1 : Matrix (Fin 77) (Fin 77) ℤ) + indexedR G C h := by
  have hs := congrArg
    (fun M : Matrix (Outside C) (Outside C) ℤ =>
      M.submatrix (outsideIndex G C h) (outsideIndex G C h))
    (H_gram G C h)
  rw [indexedH, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv]
  ext u v
  have he := congrArg (fun M : Matrix (Fin 77) (Fin 77) ℤ => M u v) hs
  simpa [indexedR, Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply] using he

theorem indexedP_row_sum (h : G.IsSRGWith 99 14 1 2)
    (c : Fin 22) :
    (∑ u : Fin 77, indexedP G C h c u) = 14 := by
  calc
    _ = ∑ u : Outside C, P G C (insideIndex G C c) u := by
      apply Fintype.sum_equiv (outsideIndex G C h)
      intro u
      rfl
    _ = 14 := P_row_sum G C h _

theorem indexedP_column_sum (h : G.IsSRGWith 99 14 1 2)
    (u : Fin 77) :
    (∑ c : Fin 22, indexedP G C h c u) = 4 := by
  calc
    _ = ∑ c : Inside C, P G C c (outsideIndex G C h u) := by
      apply Fintype.sum_equiv (insideIndex G C)
      intro c
      rfl
    _ = 4 := P_column_sum G C h _

theorem indexedH_row_sum (h : G.IsSRGWith 99 14 1 2)
    (u : Fin 77) :
    (∑ t : Fin 77, indexedH G C h u t) = 3 := by
  calc
    _ = ∑ T : OutsideTriangle G C,
        H G C (outsideIndex G C h u) T := by
      apply Fintype.sum_equiv (triangleIndex G C h)
      intro t
      rfl
    _ = 3 := H_row_sum G C h _

theorem indexedH_column_sum (h : G.IsSRGWith 99 14 1 2)
    (t : Fin 77) :
    (∑ u : Fin 77, indexedH G C h u t) = 3 := by
  calc
    _ = ∑ u : Outside C,
        H G C u (triangleIndex G C h t) := by
      apply Fintype.sum_equiv (outsideIndex G C h)
      intro u
      rfl
    _ = 3 := H_column_sum G C _

theorem indexedE_row_sum (h : G.IsSRGWith 99 14 1 2)
    (u : Fin 77) :
    (∑ v : Fin 77, indexedE G C h u v) = 4 := by
  calc
    _ = ∑ v : Outside C,
        E G C (outsideIndex G C h u) v := by
      apply Fintype.sum_equiv (outsideIndex G C h)
      intro v
      rfl
    _ = 4 := E_row_sum_from_bridge G C h (edge_matrix_bridge G C h) _

theorem indexedR_row_sum (h : G.IsSRGWith 99 14 1 2)
    (u : Fin 77) :
    (∑ v : Fin 77, indexedR G C h u v) = 6 := by
  calc
    _ = ∑ v : Outside C,
        R G C (outsideIndex G C h u) v := by
      apply Fintype.sum_equiv (outsideIndex G C h)
      intro v
      rfl
    _ = 6 := R_row_sum_from_bridge G C h (edge_matrix_bridge G C h) _

theorem indexedE_plus_R_eq_D (h : G.IsSRGWith 99 14 1 2) :
    indexedE G C h + indexedR G C h = indexedD G C h := by
  have hs := congrArg
    (fun M : Matrix (Outside C) (Outside C) ℤ =>
      M.submatrix (outsideIndex G C h) (outsideIndex G C h))
    (E_plus_R_eq_D G C)
  ext u v
  have he := congrArg (fun M : Matrix (Fin 77) (Fin 77) ℤ => M u v) hs
  simpa [indexedE, indexedR, indexedD,
    Matrix.submatrix_apply, Matrix.add_apply] using he

theorem indexedR_eq_gram_difference (h : G.IsSRGWith 99 14 1 2) :
    indexedR G C h =
      indexedH G C h * (indexedH G C h)ᵀ -
        3 • (1 : Matrix (Fin 77) (Fin 77) ℤ) := by
  rw [indexedH_gram G C h]
  abel

theorem indexedP_mixed (h : G.IsSRGWith 99 14 1 2) :
    indexedP G C h * indexedD G C h + indexedP G C h =
      2 • J (Fin 22) (Fin 77) := by
  have hs := congrArg
    (fun M : Matrix (Inside C) (Outside C) ℤ =>
      M.submatrix (insideIndex G C) (outsideIndex G C h))
    (P_mul_D G C h)
  rw [indexedP, indexedD, Matrix.submatrix_mul_equiv]
  ext c u
  have he := congrArg (fun M : Matrix (Fin 22) (Fin 77) ℤ => M c u) hs
  simpa [Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.smul_apply, Coclique22.J_apply] using he

theorem indexedD_quadratic (h : G.IsSRGWith 99 14 1 2) :
    indexedD G C h * indexedD G C h + indexedD G C h +
        (indexedP G C h)ᵀ * indexedP G C h =
      12 • (1 : Matrix (Fin 77) (Fin 77) ℤ) +
        2 • J (Fin 77) (Fin 77) := by
  have hs := congrArg
    (fun M : Matrix (Outside C) (Outside C) ℤ =>
      M.submatrix (outsideIndex G C h) (outsideIndex G C h))
    (D_quadratic G C h)
  simp only [indexedP, indexedD, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv]
  ext u v
  have he := congrArg (fun M : Matrix (Fin 77) (Fin 77) ℤ => M u v) hs
  simpa only [two_nsmul, Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Coclique22.J_apply,
    (outsideIndex G C h).injective.eq_iff] using he

theorem indexedP_binary (h : G.IsSRGWith 99 14 1 2)
    (c : Fin 22) (u : Fin 77) :
    indexedP G C h c u = 0 ∨ indexedP G C h c u = 1 :=
  P_binary G C _ _

theorem indexedH_binary (h : G.IsSRGWith 99 14 1 2)
    (u t : Fin 77) :
    indexedH G C h u t = 0 ∨ indexedH G C h u t = 1 :=
  H_binary G C _ _

theorem indexedE_adjacency (h : G.IsSRGWith 99 14 1 2) :
    (indexedE G C h).IsAdjMatrix :=
  (E_adjacency G C).submatrix (outsideIndex G C h)

theorem indexedR_adjacency (h : G.IsSRGWith 99 14 1 2) :
    (indexedR G C h).IsAdjMatrix :=
  (R_adjacency G C).submatrix (outsideIndex G C h)

theorem indexedR_edge_B_zero (h : G.IsSRGWith 99 14 1 2)
    (u v : Fin 77) (hr : indexedR G C h u v = 1) :
    ((indexedP G C h)ᵀ * indexedP G C h) u v = 0 := by
  have ho : R G C (outsideIndex G C h u) (outsideIndex G C h v) = 1 := hr
  have hb := R_edge_B_zero G C _ _ ho
  simpa only [indexedP, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_apply] using hb

theorem indexedE_edge_B_one (h : G.IsSRGWith 99 14 1 2)
    (u v : Fin 77) (he : indexedE G C h u v = 1) :
    ((indexedP G C h)ᵀ * indexedP G C h) u v = 1 := by
  have ho : E G C (outsideIndex G C h u) (outsideIndex G C h v) = 1 := he
  have hb := E_edge_B_one G C h _ _ ho
  simpa only [indexedP, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_apply] using hb

/-- The three matrices are one relabeling of the same graph-owned P, H, and E. -/
noncomputable def actualCompletion (h : G.IsSRGWith 99 14 1 2) :
    SimultaneousCompletion := by
  have hR : outsideR (indexedH G C h) = indexedR G C h := by
    simpa only [outsideR] using
      (indexedR_eq_gram_difference G C h).symm
  have hD : outsideR (indexedH G C h) + indexedE G C h =
      indexedD G C h := by
    rw [hR, add_comm]
    exact indexedE_plus_R_eq_D G C h
  exact {
    P := indexedP G C h
    H := indexedH G C h
    E := indexedE G C h
    P_binary := indexedP_binary G C h
    P_row_sum := indexedP_row_sum G C h
    P_column_sum := indexedP_column_sum G C h
    P_design := indexedP_design G C h
    H_binary := indexedH_binary G C h
    H_row_sum := indexedH_row_sum G C h
    H_column_sum := indexedH_column_sum G C h
    R_binary_offdiag := by
      intro u v _
      rw [hR]
      exact (indexedR_adjacency G C h).zero_or_one u v
    R_diag := by
      intro u
      rw [hR]
      exact (indexedR_adjacency G C h).apply_diag u
    R_edge_disjoint := by
      intro u v hr
      rw [hR] at hr
      exact indexedR_edge_B_zero G C h u v hr
    E_adjacency := indexedE_adjacency G C h
    E_row_sum := indexedE_row_sum G C h
    E_edge_meets := indexedE_edge_B_one G C h
    mixed := by
      simpa only [hD] using indexedP_mixed G C h
    quadratic := by
      simpa only [hD] using indexedD_quadratic G C h
  }

end Conway99Formal.Coclique22Triangle

#print axioms Conway99Formal.Coclique22Triangle.E_adjacency
#print axioms Conway99Formal.Coclique22Triangle.R_adjacency
#print axioms Conway99Formal.Coclique22Triangle.E_edge_B_one
#print axioms Conway99Formal.Coclique22Triangle.R_edge_B_zero
#print axioms Conway99Formal.Coclique22Triangle.indexedP_design
#print axioms Conway99Formal.Coclique22Triangle.indexedH_gram
#print axioms Conway99Formal.Coclique22Triangle.indexedP_row_sum
#print axioms Conway99Formal.Coclique22Triangle.indexedP_column_sum
#print axioms Conway99Formal.Coclique22Triangle.indexedH_row_sum
#print axioms Conway99Formal.Coclique22Triangle.indexedH_column_sum
#print axioms Conway99Formal.Coclique22Triangle.indexedE_row_sum
#print axioms Conway99Formal.Coclique22Triangle.indexedR_row_sum
#print axioms Conway99Formal.Coclique22Triangle.indexedE_plus_R_eq_D
#print axioms Conway99Formal.Coclique22Triangle.indexedR_eq_gram_difference
#print axioms Conway99Formal.Coclique22Triangle.indexedP_mixed
#print axioms Conway99Formal.Coclique22Triangle.indexedD_quadratic
#print axioms Conway99Formal.Coclique22Triangle.indexedP_binary
#print axioms Conway99Formal.Coclique22Triangle.indexedH_binary
#print axioms Conway99Formal.Coclique22Triangle.indexedE_adjacency
#print axioms Conway99Formal.Coclique22Triangle.indexedR_adjacency
#print axioms Conway99Formal.Coclique22Triangle.indexedR_edge_B_zero
#print axioms Conway99Formal.Coclique22Triangle.indexedE_edge_B_one
#print axioms Conway99Formal.Coclique22Triangle.actualCompletion

set_option autoImplicit false

namespace Conway99Formal.Coclique22Coordinate

open SimpleGraph Finset
open Conway99Formal.Coclique22

private abbrev Split := Fin 22 ⊕ Fin 77

private def coordinateEquiv : Split ≃ Fin 99 := finSumFinEquiv

private def onFin99 (Q : BlockCompletion) : SimpleGraph (Fin 99) :=
  ((blockMatrix_isAdjMatrix Q).toGraph).map coordinateEquiv.toEmbedding

private noncomputable instance onFin99Decidable (Q : BlockCompletion) :
    DecidableRel (onFin99 Q).Adj := Classical.decRel _

/-- The CQ02 graph is still an actual SRG after the literal 22+77 to 99 relabeling. -/
private theorem onFin99_srg (Q : BlockCompletion) :
    (onFin99 Q).IsSRGWith 99 14 1 2 := by
  classical
  let G := (blockMatrix_isAdjMatrix Q).toGraph
  letI : DecidableRel G.Adj := inferInstance
  let H := onFin99 Q
  letI : DecidableRel H.Adj := Classical.decRel _
  let e : G ≃g H := SimpleGraph.Iso.map coordinateEquiv G
  have h : G.IsSRGWith 99 14 1 2 := blockCompletion_srg Q
  have hcommon (u v : Split) :
      Fintype.card (G.commonNeighbors u v) =
        Fintype.card (H.commonNeighbors (e u) (e v)) := by
    apply Fintype.card_congr
    refine e.toEquiv.subtypeEquiv ?_
    intro w
    change (G.Adj u w ∧ G.Adj v w) ↔
      (H.Adj (e u) (e w) ∧ H.Adj (e v) (e w))
    simp only [e.map_adj_iff]
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro w
    have hc : G.degree (e.symm w) = H.degree w := by
      simpa only [G.card_neighborSet_eq_degree,
        H.card_neighborSet_eq_degree, e.apply_symm_apply] using
        Fintype.card_congr (e.mapNeighborSet (e.symm w))
    exact hc.symm.trans (h.regular.degree_eq (e.symm w))
  · intro w z hwz
    have hwz' : G.Adj (e.symm w) (e.symm z) := by
      apply e.map_adj_iff.mp
      simpa using hwz
    have hc := hcommon (e.symm w) (e.symm z)
    simpa only [e.apply_symm_apply] using hc.symm.trans (h.of_adj _ _ hwz')
  · intro w z hwz hn
    have hne : e.symm w ≠ e.symm z := by
      intro heq
      apply hwz
      simpa using congrArg e heq
    have hn' : ¬ G.Adj (e.symm w) (e.symm z) := by
      intro huv
      apply hn
      have hh := e.map_adj_iff.mpr huv
      simpa using hh
    have hc := hcommon (e.symm w) (e.symm z)
    simpa only [e.apply_symm_apply] using hc.symm.trans (h.of_not_adj hne hn')

private def canonicalCarrier : Finset (Fin 99) :=
  Finset.univ.image (fun c : Fin 22 => coordinateEquiv (Sum.inl c))

private theorem canonicalCarrier_card : canonicalCarrier.card = 22 := by
  have hinj : Function.Injective
      (fun c : Fin 22 => coordinateEquiv (Sum.inl c)) :=
    coordinateEquiv.injective.comp Sum.inl_injective
  simpa [canonicalCarrier] using
    (Finset.card_image_of_injective (Finset.univ : Finset (Fin 22)) hinj)

/-- The relabeled first summand is the specified independent 22-set. -/
private def canonicalCoclique (Q : BlockCompletion) : Coclique (onFin99 Q) where
  carrier := canonicalCarrier
  card_eq := canonicalCarrier_card
  independent := by
    intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hy
    let G := (blockMatrix_isAdjMatrix Q).toGraph
    let e : G ≃g onFin99 Q := SimpleGraph.Iso.map coordinateEquiv G
    have hec : e (Sum.inl c) = coordinateEquiv (Sum.inl c) := rfl
    have hed : e (Sum.inl d) = coordinateEquiv (Sum.inl d) := rfl
    have hmap : (onFin99 Q).Adj (e (Sum.inl c)) (e (Sum.inl d)) := by
      rw [hec, hed]
      exact hxy
    have hsrc : G.Adj (Sum.inl c) (Sum.inl d) :=
      e.map_adj_iff.mp hmap
    change blockMatrix Q (Sum.inl c) (Sum.inl d) = 1 at hsrc
    simp [blockMatrix] at hsrc

/-- The CQ02 witness on literal Fin 99 coordinates, including its actual coclique. -/
theorem blockCompletion_overFin99 (Q : BlockCompletion) :
    (onFin99 Q).IsSRGWith 99 14 1 2 ∧
      Nonempty (Coclique (onFin99 Q)) := by
  exact ⟨onFin99_srg Q, ⟨canonicalCoclique Q⟩⟩

/- Reverse coordinate assignment for a specified actual coclique. The resulting
   equivalence is noncanonical: each subtype gets an arbitrary Fin labeling. -/

private def outsideNegEquiv (G : SimpleGraph (Fin 99)) (C : Coclique G) :
    Outside C ≃ {v : Fin 99 // v ∉ C.carrier} :=
  Equiv.subtypeEquivRight (fun v => Finset.mem_compl)

private def partitionEquiv (G : SimpleGraph (Fin 99)) (C : Coclique G) :
    Inside C ⊕ Outside C ≃ Fin 99 :=
  (Equiv.sumCongr (Equiv.refl (Inside C)) (outsideNegEquiv G C)).trans
    (Equiv.sumCompl (fun v : Fin 99 => v ∈ C.carrier))

noncomputable def actualCocliqueCoordinates (G : SimpleGraph (Fin 99))
    [DecidableRel G.Adj] (C : Coclique G) (h : G.IsSRGWith 99 14 1 2) :
    Split ≃ Fin 99 :=
  (Equiv.sumCongr
    (Fintype.equivFinOfCardEq (inside_card C)).symm
    (Fintype.equivFinOfCardEq (outside_card G C h)).symm).trans
      (partitionEquiv G C)

theorem coordinates_left_mem (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj]
    (C : Coclique G) (h : G.IsSRGWith 99 14 1 2) (c : Fin 22) :
    actualCocliqueCoordinates G C h (Sum.inl c) ∈ C.carrier := by
  let eC : Inside C ≃ Fin 22 := Fintype.equivFinOfCardEq (inside_card C)
  have he : actualCocliqueCoordinates G C h (Sum.inl c) = (eC.symm c).1 := by
    simp [actualCocliqueCoordinates, partitionEquiv, eC,
      Equiv.sumCompl_apply_inl]
  rw [he]
  exact (eC.symm c).2

theorem coordinates_right_outside (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj]
    (C : Coclique G) (h : G.IsSRGWith 99 14 1 2) (u : Fin 77) :
    actualCocliqueCoordinates G C h (Sum.inr u) ∉ C.carrier := by
  let eO : Outside C ≃ Fin 77 := Fintype.equivFinOfCardEq (outside_card G C h)
  have he : actualCocliqueCoordinates G C h (Sum.inr u) = (eO.symm u).1 := by
    simp [actualCocliqueCoordinates, partitionEquiv, outsideNegEquiv, eO,
      Equiv.sumCompl_apply_inr]
  rw [he]
  exact Finset.mem_compl.mp (eO.symm u).2

end Conway99Formal.Coclique22Coordinate

namespace Conway99Formal.Coclique22

end Conway99Formal.Coclique22

namespace Conway99Formal.Coclique22Coordinate

open Conway99Formal.Coclique22

theorem simultaneous_completion_equivalence :
    Nonempty SimultaneousCompletion ↔ HasCoclique99 := by
  classical
  unfold HasCoclique99
  constructor
  · rintro ⟨Q⟩
    exact ⟨onFin99 Q.toBlockCompletion,
      blockCompletion_overFin99 Q.toBlockCompletion⟩
  · rintro ⟨G, hG, ⟨C⟩⟩
    classical
    letI : DecidableRel G.Adj := Classical.decRel _
    exact ⟨Conway99Formal.Coclique22Triangle.actualCompletion G C hG⟩

end Conway99Formal.Coclique22Coordinate

#print axioms Conway99Formal.Coclique22Coordinate.blockCompletion_overFin99
#print axioms Conway99Formal.Coclique22Coordinate.coordinates_left_mem
#print axioms Conway99Formal.Coclique22Coordinate.coordinates_right_outside
#print axioms Conway99Formal.Coclique22Coordinate.simultaneous_completion_equivalence

open Matrix Finset

theorem Conway99Formal.Coclique22Server.cq01_forward_completion_20261003
    (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj]
    (C : Conway99Formal.Coclique22.Coclique G)
    (h : G.IsSRGWith 99 14 1 2) :
    Fintype.card (Conway99Formal.Coclique22.Inside C) = 22 ∧
    Fintype.card (Conway99Formal.Coclique22.Outside C) = 77 ∧
    (∀ c u, Conway99Formal.Coclique22.P G C c u = 0 ∨
      Conway99Formal.Coclique22.P G C c u = 1) ∧
    (Conway99Formal.Coclique22.D G C).IsAdjMatrix ∧
    (∀ c, (∑ u : Conway99Formal.Coclique22.Outside C,
      Conway99Formal.Coclique22.P G C c u) = 14) ∧
    (∀ u, (∑ c : Conway99Formal.Coclique22.Inside C,
      Conway99Formal.Coclique22.P G C c u) = 4) ∧
    (∀ u, (∑ v : Conway99Formal.Coclique22.Outside C,
      Conway99Formal.Coclique22.D G C u v) = 10) ∧
    (Conway99Formal.Coclique22.P G C * (Conway99Formal.Coclique22.P G C)ᵀ =
      12 • (1 : Matrix (Conway99Formal.Coclique22.Inside C)
        (Conway99Formal.Coclique22.Inside C) ℤ) +
      2 • Conway99Formal.Coclique22.J
        (Conway99Formal.Coclique22.Inside C)
        (Conway99Formal.Coclique22.Inside C)) ∧
    (Conway99Formal.Coclique22.P G C * Conway99Formal.Coclique22.D G C +
      Conway99Formal.Coclique22.P G C =
      2 • Conway99Formal.Coclique22.J
        (Conway99Formal.Coclique22.Inside C)
        (Conway99Formal.Coclique22.Outside C)) ∧
    (Conway99Formal.Coclique22.D G C * Conway99Formal.Coclique22.D G C +
      Conway99Formal.Coclique22.D G C +
      (Conway99Formal.Coclique22.P G C)ᵀ * Conway99Formal.Coclique22.P G C =
      12 • (1 : Matrix (Conway99Formal.Coclique22.Outside C)
        (Conway99Formal.Coclique22.Outside C) ℤ) +
      2 • Conway99Formal.Coclique22.J
        (Conway99Formal.Coclique22.Outside C)
        (Conway99Formal.Coclique22.Outside C)) := by
  exact Conway99Formal.Coclique22.forward_completion G C h

#print axioms Conway99Formal.Coclique22Server.cq01_forward_completion_20261003

theorem Conway99Formal.Coclique22Server.cq02_block_converse_20261003
    (Q : Conway99Formal.Coclique22.BlockCompletion) :
    ∃ G : SimpleGraph (Fin 22 ⊕ Fin 77),
      ∃ hDec : DecidableRel G.Adj,
        letI : DecidableRel G.Adj := hDec
        G.IsSRGWith 99 14 1 2 ∧
        (∀ u v, G.Adj u v ↔
          Conway99Formal.Coclique22.blockMatrix Q u v = 1) ∧
        ∃ C : Conway99Formal.Coclique22.Coclique G,
          C.carrier = Conway99Formal.Coclique22.blockCocliqueCarrier := by
  let G := Conway99Formal.Coclique22.blockGraph Q
  let d : DecidableRel G.Adj := by
    change DecidableRel ((Conway99Formal.Coclique22.blockMatrix_isAdjMatrix Q).toGraph).Adj
    infer_instance
  have h := Conway99Formal.Coclique22.blockCompletion_graph_and_coclique Q
  refine ⟨G, d, h.1, ?_, h.2⟩
  intro u v
  change Conway99Formal.Coclique22.blockMatrix Q u v = 1 ↔
    Conway99Formal.Coclique22.blockMatrix Q u v = 1
  exact Iff.rfl

#print axioms Conway99Formal.Coclique22Server.cq02_block_converse_20261003

theorem Conway99Formal.Coclique22Server.cq05_outside_triangles_20261003
    (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj]
    (C : Conway99Formal.Coclique22.Coclique G)
    (h : G.IsSRGWith 99 14 1 2) :
    Fintype.card (Conway99Formal.Coclique22Triangle.OutsideTriangle G C) = 77 ∧
    (∀ u : Conway99Formal.Coclique22.Outside C,
      (∑ v : Conway99Formal.Coclique22.Outside C,
        Conway99Formal.Coclique22Triangle.E G C u v) = 4) ∧
    (∀ u : Conway99Formal.Coclique22.Outside C,
      (∑ v : Conway99Formal.Coclique22.Outside C,
        Conway99Formal.Coclique22Triangle.R G C u v) = 6) ∧
    (∀ T : Conway99Formal.Coclique22Triangle.OutsideTriangle G C,
      (∑ u : Conway99Formal.Coclique22.Outside C,
        Conway99Formal.Coclique22Triangle.H G C u T) = 3) ∧
    (∀ u : Conway99Formal.Coclique22.Outside C,
      (∑ T : Conway99Formal.Coclique22Triangle.OutsideTriangle G C,
        Conway99Formal.Coclique22Triangle.H G C u T) = 3) ∧
    (Conway99Formal.Coclique22Triangle.H G C *
      (Conway99Formal.Coclique22Triangle.H G C)ᵀ =
      3 • (1 : Matrix (Conway99Formal.Coclique22.Outside C)
        (Conway99Formal.Coclique22.Outside C) ℤ) +
      Conway99Formal.Coclique22Triangle.R G C) := by
  rcases Conway99Formal.Coclique22Triangle.forward_outside_triangle_packet G C h with
    ⟨hcard, hE, hR, hcol, hrow, hgram, _, _, _, _, _⟩
  exact ⟨hcard, hE, hR, hcol, hrow, hgram⟩

#print axioms Conway99Formal.Coclique22Server.cq05_outside_triangles_20261003

theorem Conway99Formal.Coclique22Server.cq07_mixed_incidence_20261003
    (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj]
    (C : Conway99Formal.Coclique22.Coclique G)
    (h : G.IsSRGWith 99 14 1 2) :
    (∀ c T, (Conway99Formal.Coclique22.P G C *
      Conway99Formal.Coclique22Triangle.H G C) c T = 0 ∨
      (Conway99Formal.Coclique22.P G C *
      Conway99Formal.Coclique22Triangle.H G C) c T = 1) ∧
    (∀ c, (∑ T : Conway99Formal.Coclique22Triangle.OutsideTriangle G C,
      (Conway99Formal.Coclique22.P G C *
        Conway99Formal.Coclique22Triangle.H G C) c T) = 42) ∧
    (∀ T, (∑ c : Conway99Formal.Coclique22.Inside C,
      (Conway99Formal.Coclique22.P G C *
        Conway99Formal.Coclique22Triangle.H G C) c T) = 12) ∧
    ((Conway99Formal.Coclique22.P G C * Conway99Formal.Coclique22Triangle.H G C) *
      (Conway99Formal.Coclique22Triangle.H G C)ᵀ =
      2 • Conway99Formal.Coclique22.P G C +
      2 • Conway99Formal.Coclique22.J
        (Conway99Formal.Coclique22.Inside C)
        (Conway99Formal.Coclique22.Outside C) -
      Conway99Formal.Coclique22.P G C * Conway99Formal.Coclique22Triangle.E G C) ∧
    ((Conway99Formal.Coclique22.P G C * Conway99Formal.Coclique22Triangle.H G C) *
      (Conway99Formal.Coclique22.P G C *
        Conway99Formal.Coclique22Triangle.H G C)ᵀ =
      24 • (1 : Matrix (Conway99Formal.Coclique22.Inside C)
        (Conway99Formal.Coclique22.Inside C) ℤ) +
      32 • Conway99Formal.Coclique22.J
        (Conway99Formal.Coclique22.Inside C)
        (Conway99Formal.Coclique22.Inside C) -
      Conway99Formal.Coclique22.P G C * Conway99Formal.Coclique22Triangle.E G C *
        (Conway99Formal.Coclique22.P G C)ᵀ) := by
  rcases Conway99Formal.Coclique22Triangle.forward_outside_triangle_packet G C h with
    ⟨_, _, _, _, _, _, hbinary, hrow, hcol, hmixed, hself⟩
  exact ⟨hbinary, hrow, hcol, hmixed, hself⟩

#print axioms Conway99Formal.Coclique22Server.cq07_mixed_incidence_20261003

theorem Conway99Formal.Coclique22Server.cq09_simultaneous_equivalence_20261003 :
    Nonempty Conway99Formal.Coclique22.SimultaneousCompletion ↔
      Conway99Formal.Coclique22.HasCoclique99 := by
  exact Conway99Formal.Coclique22Coordinate.simultaneous_completion_equivalence

#print axioms Conway99Formal.Coclique22Server.cq09_simultaneous_equivalence_20261003

theorem solution :
    Nonempty Conway99Formal.Coclique22.SimultaneousCompletion ↔
      Conway99Formal.Coclique22.HasCoclique99 :=
  Conway99Formal.Coclique22Server.cq09_simultaneous_equivalence_20261003

#print axioms solution
