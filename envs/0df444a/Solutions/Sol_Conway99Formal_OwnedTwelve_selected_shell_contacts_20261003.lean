-- Prove2me | solution 1 for Conway99Formal.OwnedTwelve.selected_shell_contacts_20261003
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T00:25:42.230514+00:00
-- url     : https://prove2.me/submissions/9d88e339-0bcd-40bc-b41f-bd4ed7092a9d

import Mathlib

set_option autoImplicit false

/-! Graph and arithmetic steps in the owned-twelve deduction of
`research/new-export-2026-10-03/AUDIT_REPORT.md`, §§1, 3–5. -/

namespace Conway99Formal.OwnedTwelve

open Finset SimpleGraph
open RealInnerProductSpace
open scoped InnerProductSpace

/-- Vertices far from all three chosen triangle vertices in the original
graph. The chosen vertices must themselves form a triangle when used below. -/
def triangleFarSet {V : Type*} (G : SimpleGraph V) (a b c : V) : Set V :=
  {z | z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ ¬ G.Adj z a ∧ ¬ G.Adj z b ∧ ¬ G.Adj z c}

/-- The far adjacency relation is induced by the one original graph. -/
def triangleFarGraph {V : Type*} (G : SimpleGraph V) (a b c : V) :
    SimpleGraph (triangleFarSet G a b c) :=
  G.induce (triangleFarSet G a b c)

noncomputable instance triangleFarFintype {V : Type*} [Fintype V]
    (G : SimpleGraph V) (a b c : V) : Fintype (triangleFarSet G a b c) :=
  Fintype.ofFinite _

instance triangleFarDecidableRel {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b c : V) :
    DecidableRel (triangleFarGraph G a b c).Adj := by
  intro u v
  change Decidable (G.Adj u.1 v.1)
  infer_instance

@[simp] theorem triangleFarGraph_adj {V : Type*} (G : SimpleGraph V) (a b c : V)
    (u v : triangleFarSet G a b c) :
    (triangleFarGraph G a b c).Adj u v ↔ G.Adj u.1 v.1 := Iff.rfl

theorem common_neighbor_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    (G.neighborFinset u ∩ G.neighborFinset v).card =
      Fintype.card (G.commonNeighbors u v) := by
  symm
  apply Fintype.card_of_finset' (G.neighborFinset u ∩ G.neighborFinset v)
  intro w
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    SimpleGraph.commonNeighbors, Set.mem_inter_iff, SimpleGraph.mem_neighborSet]

/-- Any two distinct vertices in the actual strongly regular graph have at
most two common neighbors. This is the cap used in binary ownership. -/
theorem srg_common_neighbor_cap {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (u v : V) (huv : u ≠ v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 2 := by
  have hcard : (G.neighborFinset u ∩ G.neighborFinset v).card =
      Fintype.card (G.commonNeighbors u v) := by
    exact common_neighbor_card G u v
  rw [hcard]
  by_cases ha : G.Adj u v
  · simp [h.of_adj u v ha]
  · simp [h.of_not_adj huv ha]

/-- Restricting to the graph-derived far set cannot increase the common
neighbor count. -/
theorem triangleFar_common_neighbor_cap {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (a b c : V)
    (u v : triangleFarSet G a b c) (huv : u ≠ v) :
    ((triangleFarGraph G a b c).neighborFinset u ∩
      (triangleFarGraph G a b c).neighborFinset v).card ≤ 2 := by
  have hle : ((triangleFarGraph G a b c).neighborFinset u ∩
      (triangleFarGraph G a b c).neighborFinset v).card ≤
      (G.neighborFinset u.1 ∩ G.neighborFinset v.1).card := by
    apply Finset.card_le_card_of_injOn (fun w : triangleFarSet G a b c => w.1)
    · intro w hw
      rcases Finset.mem_inter.mp hw with ⟨hu, hv⟩
      have hu' : (triangleFarGraph G a b c).Adj u w := by simpa using hu
      have hv' : (triangleFarGraph G a b c).Adj v w := by simpa using hv
      exact Finset.mem_inter.mpr ⟨by simpa using hu', by simpa using hv'⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  have hne : u.1 ≠ v.1 := fun heq => huv (Subtype.ext heq)
  exact hle.trans (srg_common_neighbor_cap G h u.1 v.1 hne)

/-- Each far vertex shares exactly two neighbors with each triangle root;
this is the graph-local count used in the pending far-degree calculation. -/
theorem far_root_common_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (a b c : V)
    (z : triangleFarSet G a b c) :
    (G.neighborFinset z.1 ∩ G.neighborFinset a).card = 2 := by
  rcases z.property with ⟨hza, _, _, hnza, _, _⟩
  have hc := h.of_not_adj hza hnza
  exact (common_neighbor_card G z.1 a).trans hc

/-- The third vertex of a triangle is the unique common neighbor of its
chosen edge in the original graph. -/
theorem triangle_edge_completer_unique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (a b c w : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hwa : G.Adj w a) (hwb : G.Adj w b) : w = c := by
  have hc : (G.neighborFinset a ∩ G.neighborFinset b).card = 1 := by
    exact (common_neighbor_card G a b).trans (h.of_adj a b hab)
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hc
  have hmemc : c ∈ G.neighborFinset a ∩ G.neighborFinset b := by
    simp [hac, hbc]
  have hmemw : w ∈ G.neighborFinset a ∩ G.neighborFinset b := by
    have haw : G.Adj a w := (G.adj_comm w a).mp hwa
    have hbw : G.Adj b w := (G.adj_comm w b).mp hwb
    simpa using And.intro haw hbw
  have hct : c = t := by simpa [ht] using hmemc
  have hwt : w = t := by simpa [ht] using hmemw
  exact hwt.trans hct.symm

/-- A vertex far from the third point of a triangle has disjoint contacts
with the two endpoint neighborhoods of the opposite edge. -/
theorem root_contact_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (a b c z : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hzc : ¬ G.Adj z c) :
    Disjoint (G.neighborFinset z ∩ G.neighborFinset a)
      (G.neighborFinset z ∩ G.neighborFinset b) := by
  apply Finset.disjoint_left.mpr
  intro w hwa hwb
  rcases Finset.mem_inter.mp hwa with ⟨hzw, haw⟩
  rcases Finset.mem_inter.mp hwb with ⟨_, hbw⟩
  have hzw' : G.Adj z w := by simpa using hzw
  have haw' : G.Adj w a := (G.adj_comm a w).mp (by simpa using haw)
  have hbw' : G.Adj w b := (G.adj_comm b w).mp (by simpa using hbw)
  have hwc := triangle_edge_completer_unique G h a b c w hab hac hbc haw' hbw'
  rw [hwc] at hzw'
  exact hzc hzw'

/-- A far vertex has eight neighbors in the literal far graph. Its fourteen
neighbors split into three disjoint two-point root-contact sets and the far set. -/
theorem triangleFar_degree_eight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (a b c : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (z : triangleFarSet G a b c) :
    ((triangleFarGraph G a b c).neighborFinset z).card = 8 := by
  rcases z.property with ⟨hza, hzb, hzc, hnza, hnzb, hnzc⟩
  let N := G.neighborFinset z.1
  let A := N ∩ G.neighborFinset a
  let B := N ∩ G.neighborFinset b
  let C := N ∩ G.neighborFinset c
  let U := (A ∪ B) ∪ C
  have hA : A.card = 2 := far_root_common_two G h a b c z
  have hB : B.card = 2 := far_root_common_two G h b a c
    ⟨z.1, hzb, hza, hzc, hnzb, hnza, hnzc⟩
  have hC : C.card = 2 := far_root_common_two G h c a b
    ⟨z.1, hzc, hza, hzb, hnzc, hnza, hnzb⟩
  have hAB : Disjoint A B :=
    root_contact_disjoint G h a b c z.1 hab hac hbc hnzc
  have hAC : Disjoint A C :=
    root_contact_disjoint G h a c b z.1 hac hab ((G.adj_comm b c).mp hbc) hnzb
  have hBC : Disjoint B C :=
    root_contact_disjoint G h b c a z.1 hbc ((G.adj_comm a b).mp hab)
      ((G.adj_comm a c).mp hac) hnza
  have hU : U.card = 6 := by
    change ((A ∪ B) ∪ C).card = 6
    rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
      Finset.card_union_of_disjoint hAB]
    omega
  have hsub : U ⊆ N := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · rcases Finset.mem_union.mp hw with hw | hw
      · exact (Finset.mem_inter.mp hw).1
      · exact (Finset.mem_inter.mp hw).1
    · exact (Finset.mem_inter.mp hw).1
  have hfar : N ∩ (triangleFarSet G a b c).toFinset = N \ U := by
    ext w
    simp only [Finset.mem_inter, Set.mem_toFinset, Finset.mem_sdiff]
    constructor
    · rintro ⟨hwN, ⟨_, _, _, hwa, hwb, hwc⟩⟩
      refine ⟨hwN, ?_⟩
      simp only [U, Finset.mem_union, A, B, C, Finset.mem_inter,
        SimpleGraph.mem_neighborFinset]
      intro hcontact
      rcases hcontact with hcontact | hcontact
      · rcases hcontact with hcontact | hcontact
        · exact hwa ((G.adj_comm a w).mp hcontact.2)
        · exact hwb ((G.adj_comm b w).mp hcontact.2)
      · exact hwc ((G.adj_comm c w).mp hcontact.2)
    · rintro ⟨hwN, hwU⟩
      have hwa : ¬ G.Adj w a := by
        intro ha
        apply hwU
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_inter.mpr
            ⟨hwN, by simpa using (G.adj_comm w a).mp ha⟩))))
      have hwb : ¬ G.Adj w b := by
        intro hb
        apply hwU
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr (Finset.mem_inter.mpr
            ⟨hwN, by simpa using (G.adj_comm w b).mp hb⟩))))
      have hwc : ¬ G.Adj w c := by
        intro hc
        apply hwU
        exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_inter.mpr
            ⟨hwN, by simpa using (G.adj_comm w c).mp hc⟩))
      refine ⟨hwN, ?_⟩
      refine ⟨?_, ?_, ?_, hwa, hwb, hwc⟩
      · intro heq
        subst w
        exact hwb hab
      · intro heq
        subst w
        exact hwa ((G.adj_comm a b).mp hab)
      · intro heq
        subst w
        exact hwa ((G.adj_comm a c).mp hac)
  have hN : N.card = 14 := by simpa [N] using h.regular.degree_eq z.1
  have hNF : (N \ U).card = 8 := by
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  have hmap : ((triangleFarGraph G a b c).neighborFinset z).map
      (.subtype (· ∈ triangleFarSet G a b c)) =
      N ∩ (triangleFarSet G a b c).toFinset := by
    ext w
    simp only [Finset.mem_map, Finset.mem_inter, Set.mem_toFinset]
    constructor
    · rintro ⟨u, hu, hwu⟩
      have hweq : u.1 = w := hwu
      subst w
      have hzu : (triangleFarGraph G a b c).Adj z u := by simpa using hu
      exact ⟨by simpa [N] using (triangleFarGraph_adj G a b c z u).mp hzu,
        u.property⟩
    · rintro ⟨hzw, hwfar⟩
      let u : triangleFarSet G a b c := ⟨w, hwfar⟩
      refine ⟨u, ?_, rfl⟩
      have hzu : (triangleFarGraph G a b c).Adj z u :=
        (triangleFarGraph_adj G a b c z u).mpr (by simpa [N, u] using hzw)
      simpa using hzu
  have hcard := congrArg Finset.card hmap
  rw [Finset.card_map, hfar] at hcard
  exact hcard.trans hNF

/-- The norm and pairings of the three incident images force the scalar identity
at this triangle. The hypotheses are the special degree-eight signature, not
universal consequences of strong regularity. -/
theorem incident_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (τ xa xb xc : E)
    (hτ : ⟪τ, τ⟫_ℝ = 4)
    (ha : ⟪xa, xa⟫_ℝ = 12) (hb : ⟪xb, xb⟫_ℝ = 12)
    (hc : ⟪xc, xc⟫_ℝ = 12)
    (hab : ⟪xa, xb⟫_ℝ = 0) (hac : ⟪xa, xc⟫_ℝ = 0)
    (hbc : ⟪xb, xc⟫_ℝ = 0)
    (hta : ⟪τ, xa⟫_ℝ = -4) (htb : ⟪τ, xb⟫_ℝ = -4)
    (htc : ⟪τ, xc⟫_ℝ = -4) :
    xa + xb + xc = (-3 : ℝ) • τ := by
  have hz : ⟪xa + xb + xc + (3 : ℝ) • τ,
      xa + xb + xc + (3 : ℝ) • τ⟫_ℝ = 0 := by
    simp only [inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    nlinarith [real_inner_comm xa xb, real_inner_comm xa xc,
      real_inner_comm xb xc, real_inner_comm xa τ,
      real_inner_comm xb τ, real_inner_comm xc τ]
  have heq : xa + xb + xc + (3 : ℝ) • τ = 0 :=
    (inner_self_eq_zero (𝕜 := ℝ)).mp hz
  calc
    xa + xb + xc = -((3 : ℝ) • τ) := eq_neg_of_add_eq_zero_left heq
    _ = (-3 : ℝ) • τ := by rw [neg_smul]

/-- The weighted far-neighbor sum used by the binary-owner argument. -/
def weightedFarDegree {F : Type*} [Fintype F] [DecidableEq F]
    (D : SimpleGraph F) [DecidableRel D.Adj] (a : F → ℕ) (z : F) : ℕ :=
  ∑ w ∈ D.neighborFinset z, a w

/-- The far graph's arithmetic cut. A later bridge must derive these inputs from
one actual SRG, the triangle, and its graph-owned defect completers. -/
theorem binary_owners {F : Type*} [Fintype F] [DecidableEq F]
    (D : SimpleGraph F) [DecidableRel D.Adj]
    (a b : F → ℕ)
    (hdeg : ∀ z, (D.neighborFinset z).card = 8)
    (hcommon : ∀ z w, z ≠ w →
      (D.neighborFinset z ∩ D.neighborFinset w).card ≤ 2)
    (hsum : ∑ z : F, a z = 12)
    (hweight : ∀ z, a z ≤ 3)
    (hcap : ∀ z, b z + 2 * a z ≤ 6)
    (heq : ∀ z, weightedFarDegree D a z + b z = 3 * a z + 5) :
    ∀ z, a z ≤ 1 := by
  let N : F → Finset F := fun z => D.neighborFinset z
  have hself (z : F) : z ∉ N z := by simp [N]
  have hnear_le (z : F) : weightedFarDegree D a z + a z ≤ 12 := by
    have hs : N z ⊆ Finset.univ.erase z := by
      intro w hw
      have hwz : w ≠ z := by
        intro h
        subst w
        exact hself z hw
      simp [hwz]
    have hle : (∑ w ∈ N z, a w) ≤ ∑ w ∈ Finset.univ.erase z, a w :=
      Finset.sum_le_sum_of_subset hs
    have herase : (∑ w ∈ Finset.univ.erase z, a w) + a z = 12 := by
      simpa [hsum] using (Finset.sum_erase_add Finset.univ a (Finset.mem_univ z))
    change (∑ w ∈ N z, a w) + a z ≤ 12
    omega
  have htwo (z : F) : a z ≤ 2 := by
    have hw := hweight z
    by_contra hn
    have haz : a z = 3 := by omega
    have hbz : b z = 0 := by have hc := hcap z; omega
    have hd := heq z
    have hl := hnear_le z
    omega
  have hpair (z w : F) (hzw : z ≠ w) (hz : a z = 2) (hw : a w = 2) : False := by
    have hdz : 9 ≤ weightedFarDegree D a z := by
      have hc := hcap z
      have he := heq z
      omega
    have hdw : 9 ≤ weightedFarDegree D a w := by
      have hc := hcap w
      have he := heq w
      omega
    have hinter : (∑ v ∈ N z ∩ N w, a v) ≤ 4 := by
      calc
        (∑ v ∈ N z ∩ N w, a v) ≤ ∑ _v ∈ N z ∩ N w, (2 : ℕ) := by
          apply Finset.sum_le_sum
          intro v _
          exact htwo v
        _ = 2 * (N z ∩ N w).card := by simp [mul_comm]
        _ ≤ 4 := by have hc := hcommon z w hzw; dsimp [N] at hc ⊢; omega
    have hdouble : weightedFarDegree D a z + weightedFarDegree D a w ≤
        12 + ∑ v ∈ N z ∩ N w, a v := by
      have hsumN (s : Finset F) : (∑ v ∈ s, a v) =
          ∑ v : F, if v ∈ s then a v else 0 := by simp
      change (∑ v ∈ N z, a v) + (∑ v ∈ N w, a v) ≤ _
      calc
        (∑ v ∈ N z, a v) + (∑ v ∈ N w, a v) =
            ∑ v : F, ((if v ∈ N z then a v else 0) +
              (if v ∈ N w then a v else 0)) := by
                rw [hsumN (N z), hsumN (N w), Finset.sum_add_distrib]
        _ ≤
            ∑ v : F, (a v + (if v ∈ N z ∩ N w then a v else 0)) := by
              apply Finset.sum_le_sum
              intro v _
              by_cases hzv : v ∈ N z <;> by_cases hwv : v ∈ N w <;>
                simp [hzv, hwv]
        _ = 12 + ∑ v ∈ N z ∩ N w, a v := by
          rw [Finset.sum_add_distrib, hsum]
          rw [← hsumN (N z ∩ N w)]
    omega
  intro z
  have hz := htwo z
  by_contra hn
  have haz : a z = 2 := by omega
  have hneighbor (w : F) (hw : w ∈ N z) : a w ≤ 1 := by
    have hne : w ≠ z := by
      intro h
      subst w
      exact hself z hw
    have hnot : a w ≠ 2 := by
      intro he
      exact hpair w z hne he haz
    have hle := htwo w
    omega
  have hdegree : weightedFarDegree D a z ≤ 8 := by
    calc
      weightedFarDegree D a z ≤ ∑ _w ∈ N z, (1 : ℕ) := by
        change (∑ w ∈ N z, a w) ≤ _
        apply Finset.sum_le_sum
        exact hneighbor
      _ = 8 := by simpa [N] using hdeg z
  have hc := hcap z
  have he := heq z
  omega

/-- Binary ownership in the literal far restriction of one hypothetical
SRG. The remaining numerical inputs are the graph-derived slice obligations. -/
theorem graph_binary_owners {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (aV bV cV : V)
    (defects prismContacts : triangleFarSet G aV bV cV → ℕ)
    (hdeg : ∀ z, ((triangleFarGraph G aV bV cV).neighborFinset z).card = 8)
    (hsum : ∑ z, defects z = 12)
    (hweight : ∀ z, defects z ≤ 3)
    (hcap : ∀ z, prismContacts z + 2 * defects z ≤ 6)
    (heq : ∀ z, weightedFarDegree (triangleFarGraph G aV bV cV)
      defects z + prismContacts z = 3 * defects z + 5) :
    ∀ z, defects z ≤ 1 := by
  apply binary_owners (triangleFarGraph G aV bV cV) defects prismContacts
    hdeg ?_ hsum hweight hcap heq
  intro z w hzw
  exact triangleFar_common_neighbor_cap G h aV bV cV z w hzw

/-- The binary-owner deduction needs no separate far-degree assumption when
the three chosen roots are a triangle in the same SRG. -/
theorem graph_binary_owners_of_triangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (aV bV cV : V)
    (hab : G.Adj aV bV) (hac : G.Adj aV cV) (hbc : G.Adj bV cV)
    (defects prismContacts : triangleFarSet G aV bV cV → ℕ)
    (hsum : ∑ z, defects z = 12)
    (hweight : ∀ z, defects z ≤ 3)
    (hcap : ∀ z, prismContacts z + 2 * defects z ≤ 6)
    (heq : ∀ z, weightedFarDegree (triangleFarGraph G aV bV cV)
      defects z + prismContacts z = 3 * defects z + 5) :
    ∀ z, defects z ≤ 1 := by
  apply graph_binary_owners G h aV bV cV defects prismContacts
    (triangleFar_degree_eight G h aV bV cV hab hac hbc) hsum hweight hcap heq

/-- Twelve units of binary defect weight occupy exactly twelve far vertices. -/
theorem binary_support_card {F : Type*} [Fintype F] [DecidableEq F]
    (a : F → ℕ) (hsum : ∑ z : F, a z = 12)
    (hbinary : ∀ z, a z ≤ 1) :
    (Finset.univ.filter fun z => a z = 1).card = 12 := by
  have hrep (z : F) : a z = if a z = 1 then 1 else 0 := by
    by_cases hz : a z = 1
    · simp [hz]
    · have hle := hbinary z
      have hzero : a z = 0 := by omega
      simp [hz, hzero]
  calc
    (Finset.univ.filter fun z => a z = 1).card =
        ∑ z : F, if a z = 1 then 1 else 0 := by simp
    _ = ∑ z : F, a z := by
      apply Finset.sum_congr rfl
      intro z _
      exact (hrep z).symm
    _ = 12 := hsum

/-- The twelve units of defect weight have twelve distinct far support vertices
under the same-graph triangle, capacity, and slice hypotheses. -/
theorem graph_owner_support_card_of_triangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (aV bV cV : V)
    (hab : G.Adj aV bV) (hac : G.Adj aV cV) (hbc : G.Adj bV cV)
    (defects prismContacts : triangleFarSet G aV bV cV → ℕ)
    (hsum : ∑ z, defects z = 12)
    (hweight : ∀ z, defects z ≤ 3)
    (hcap : ∀ z, prismContacts z + 2 * defects z ≤ 6)
    (heq : ∀ z, weightedFarDegree (triangleFarGraph G aV bV cV)
      defects z + prismContacts z = 3 * defects z + 5) :
    (Finset.univ.filter fun z => defects z = 1).card = 12 := by
  exact binary_support_card defects hsum
    (graph_binary_owners_of_triangle G h aV bV cV hab hac hbc
      defects prismContacts hsum hweight hcap heq)

/-- A graph-derived contact count, in literal vertex coordinates. -/
def contactCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℤ :=
  ((G.neighborFinset v ∩ S).card : ℤ)

/-- Count the same cross incidences from either side of two vertex sets. -/
theorem contact_sum_symmetry {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    (∑ s ∈ S, contactCount G T s) =
      ∑ t ∈ T, contactCount G S t := by
  have hcount (A : Finset V) (v : V) :
      contactCount G A v = ∑ u ∈ A, if G.Adj v u then (1 : ℤ) else 0 := by
    have hf : A.filter (G.Adj v) = G.neighborFinset v ∩ A := by
      ext u
      simp [and_comm]
    rw [contactCount, ← hf]
    simp
  calc
    (∑ s ∈ S, contactCount G T s) =
        ∑ s ∈ S, ∑ t ∈ T, if G.Adj s t then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      exact hcount T s
    _ = ∑ t ∈ T, ∑ s ∈ S, if G.Adj t s then (1 : ℤ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro s _
      by_cases ha : G.Adj s t
      · have hb : G.Adj t s := (G.adj_comm s t).mp ha
        simp [ha, hb]
      · have hb : ¬ G.Adj t s := by
          intro h
          exact ha ((G.adj_comm s t).mpr h)
        simp [ha, hb]
    _ = ∑ t ∈ T, contactCount G S t := by
      apply Finset.sum_congr rfl
      intro t _
      exact (hcount S t).symm

/-- Twelve selected vertices with six contacts each in a shell give 72 shell
contacts in the opposite direction. -/
theorem shell_contact_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (O S : Finset V)
    (hOcard : O.card = 12)
    (hsix : ∀ z ∈ O, (G.neighborFinset z ∩ S).card = 6) :
    (∑ s ∈ S, contactCount G O s) = 72 := by
  rw [contact_sum_symmetry G S O]
  calc
    (∑ z ∈ O, contactCount G S z) = ∑ _z ∈ O, (6 : ℤ) := by
      apply Finset.sum_congr rfl
      intro z hz
      change (((G.neighborFinset z ∩ S).card : ℤ) = 6)
      exact_mod_cast hsix z hz
    _ = 72 := by simp [hOcard]

/-- Every selected far vertex is distinct from all three chosen roots. -/
theorem triangle_far_disjoint_roots {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (a b c : V) (O : Finset V)
    (hfar : ∀ z ∈ O, z ∈ triangleFarSet G a b c) :
    Disjoint O ({a, b, c} : Finset V) := by
  apply Finset.disjoint_left.mpr
  intro z hzO hzT
  rcases hfar z hzO with ⟨hza, hzb, hzc, _, _, _⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzT
  rcases hzT with h | h | h
  · exact hza h
  · exact hzb h
  · exact hzc h

/-- A selected subset of the graph-derived far vertices has no contacts at
any of the three roots. -/
theorem triangle_root_contact_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V) (O : Finset V)
    (hfar : ∀ z ∈ O, z ∈ triangleFarSet G a b c) :
    contactCount G O a = 0 ∧ contactCount G O b = 0 ∧
      contactCount G O c = 0 := by
  have hroot (r : V) (hn : ∀ z ∈ O, ¬ G.Adj z r) :
      contactCount G O r = 0 := by
    have hempty : G.neighborFinset r ∩ O = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      rcases Finset.mem_inter.mp hz with ⟨hzr, hzO⟩
      have hrz : G.Adj r z := by simpa using hzr
      exact hn z hzO ((G.adj_comm r z).mp hrz)
    simp [contactCount, hempty]
  refine ⟨hroot a ?_, hroot b ?_, hroot c ?_⟩
  · intro z hz
    rcases hfar z hz with ⟨_, _, _, hza, _, _⟩
    exact hza
  · intro z hz
    rcases hfar z hz with ⟨_, _, _, _, hzb, _⟩
    exact hzb
  · intro z hz
    rcases hfar z hz with ⟨_, _, _, _, _, hzc⟩
    exact hzc

/-- Every point of an SRG(99,14,1,2) has fourteen neighbors, so a selected
set of twelve points has 168 total contacts, counted over the full graph. -/
theorem contact_total {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (S : Finset V) :
    (∑ v : V, contactCount G S v) = 14 * (S.card : ℤ) := by
  have hcount (v : V) : contactCount G S v =
      ∑ u ∈ S, if G.Adj v u then (1 : ℤ) else 0 := by
    have hfilter : S.filter (G.Adj v) = G.neighborFinset v ∩ S := by
      ext u
      simp [and_comm]
    rw [contactCount, ← hfilter]
    simp
  have hdegree (u : V) : (∑ v : V, if G.Adj v u then (1 : ℤ) else 0) = 14 := by
    have hfilter : (Finset.univ.filter fun v => G.Adj v u) =
        G.neighborFinset u := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      exact G.adj_comm v u
    calc
      (∑ v : V, if G.Adj v u then (1 : ℤ) else 0) =
          ((Finset.univ.filter fun v => G.Adj v u).card : ℤ) := by simp
      _ = (G.degree u : ℤ) := by rw [hfilter]; rfl
      _ = 14 := by exact_mod_cast h.regular.degree_eq u
  calc
    (∑ v : V, contactCount G S v) =
        ∑ v : V, ∑ u ∈ S, if G.Adj v u then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro v _
          exact hcount v
    _ = ∑ u ∈ S, ∑ v : V, if G.Adj v u then (1 : ℤ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _u ∈ S, (14 : ℤ) := by
      apply Finset.sum_congr rfl
      intro u _
      exact hdegree u
    _ = 14 * (S.card : ℤ) := by simp [mul_comm]

/-- Inside contacts count each induced edge twice, with the edge set and
contact counts both restricted from the same original graph. -/
theorem contact_inside_double {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (∑ v ∈ S, contactCount G S v) =
      2 * (((G.induce (S : Set V)).edgeFinset.card : ℤ)) := by
  letI : Fintype (S : Set V) := FinsetCoe.fintype S
  have hpoint (v : {x : V // x ∈ S}) :
      contactCount G S v.1 = ((G.induce (S : Set V)).degree v : ℤ) := by
    have hm : ((G.induce (S : Set V)).neighborFinset v).map
        (.subtype (· ∈ (S : Set V))) = G.neighborFinset v.1 ∩ S := by
      ext w
      simp
    have hc := congrArg Finset.card hm
    have hn : ((G.induce (S : Set V)).neighborFinset v).card =
        (G.neighborFinset v.1 ∩ S).card := by
      simpa only [Finset.card_map, Finset.toFinset_coe] using hc
    change ((G.neighborFinset v.1 ∩ S).card : ℤ) =
      (((G.induce (S : Set V)).neighborFinset v).card : ℤ)
    exact congrArg (fun n : ℕ => (n : ℤ)) hn.symm
  have hsub : (∑ v ∈ S, contactCount G S v) =
      ∑ v : {x : V // x ∈ S}, contactCount G S v.1 :=
    Finset.sum_subtype S (fun _ => Iff.rfl) (contactCount G S)
  rw [hsub]
  simp_rw [hpoint]
  exact_mod_cast (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges

/-- The squared contact moment is computed from common-neighbor counts of
the same strongly regular graph as the contact vector. -/
theorem contact_square_moment {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (S : Finset V) :
    (∑ v : V, (contactCount G S v)^2) =
      12 * (S.card : ℤ) + 2 * (S.card : ℤ)^2 -
        ∑ u ∈ S, contactCount G S u := by
  classical
  have hcount (v : V) : contactCount G S v =
      ∑ u ∈ S, if G.Adj v u then (1 : ℤ) else 0 := by
    have hf : S.filter (G.Adj v) = G.neighborFinset v ∩ S := by
      ext u
      simp [and_comm]
    rw [contactCount, ← hf]
    simp
  have hpair (u w : V) :
      (∑ v : V, (if G.Adj v u then (1 : ℤ) else 0) *
        (if G.Adj v w then 1 else 0)) =
      ((G.neighborFinset u ∩ G.neighborFinset w).card : ℤ) := by
    have hf : (Finset.univ.filter fun v => G.Adj v u ∧ G.Adj v w) =
        G.neighborFinset u ∩ G.neighborFinset w := by
      ext v
      simp [G.adj_comm]
    calc
      _ = ∑ v : V, if G.Adj v u ∧ G.Adj v w then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hu : G.Adj v u <;> by_cases hw : G.Adj v w <;>
          simp [hu, hw]
      _ = ((Finset.univ.filter fun v => G.Adj v u ∧ G.Adj v w).card : ℤ) := by
        simp
      _ = _ := by rw [hf]
  have hcommon (u w : V) :
      ((G.neighborFinset u ∩ G.neighborFinset w).card : ℤ) =
        12 * (if u = w then 1 else 0) + 2 -
          (if G.Adj u w then 1 else 0) := by
    by_cases huw : u = w
    · subst w
      have hd : (G.neighborFinset u ∩ G.neighborFinset u).card = 14 := by
        simpa using h.regular.degree_eq u
      have hr : G.degree u = 14 := h.regular.degree_eq u
      simp [hr]
    · have hc : (G.neighborFinset u ∩ G.neighborFinset w).card =
          Fintype.card (G.commonNeighbors u w) := by
        exact common_neighbor_card G u w
      by_cases ha : G.Adj u w
      · rw [hc, h.of_adj u w ha]
        simp [huw, ha]
      · rw [hc, h.of_not_adj huw ha]
        simp [huw, ha]
  have hdouble : (∑ u ∈ S, ∑ w ∈ S,
      (if G.Adj u w then (1 : ℤ) else 0)) =
      ∑ u ∈ S, contactCount G S u := by
    apply Finset.sum_congr rfl
    intro u _
    exact (hcount u).symm
  calc
    (∑ v : V, (contactCount G S v)^2) =
        ∑ v : V, ∑ u ∈ S, ∑ w ∈ S,
          (if G.Adj v u then (1 : ℤ) else 0) *
            (if G.Adj v w then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro v _
          rw [hcount, pow_two, Finset.sum_mul_sum]
    _ = ∑ u ∈ S, ∑ w ∈ S,
        (∑ v : V, (if G.Adj v u then (1 : ℤ) else 0) *
          (if G.Adj v w then 1 else 0)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_comm]
    _ = ∑ u ∈ S, ∑ w ∈ S,
        ((G.neighborFinset u ∩ G.neighborFinset w).card : ℤ) := by
          simp_rw [hpair]
    _ = ∑ u ∈ S, ∑ w ∈ S,
        (12 * (if u = w then 1 else 0) + 2 -
          (if G.Adj u w then 1 else 0) : ℤ) := by
          simp_rw [hcommon]
    _ = 12 * (S.card : ℤ) + 2 * (S.card : ℤ)^2 -
        ∑ u ∈ S, contactCount G S u := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, hdouble]
          simp [pow_two]
          ring

/-- The integer moment obstruction behind the universal 12-point edge cap.
The graph-owned contact moments must still be supplied by an SRG bridge. -/
theorem twelve_point_edge_cap_from_moments
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (ρ : V → ℤ) (e : ℤ)
    (hcardS : S.card = 12)
    (hcardC : (Finset.univ \ S).card = 87)
    (hsumS : (∑ v ∈ S, ρ v) = 2 * e)
    (hsumC : (∑ v ∈ Finset.univ \ S, ρ v) = 168 - 2 * e)
    (hsquare : (∑ v : V, (ρ v)^2) = 432 - 2 * e) :
    e ≤ 24 := by
  have hquadS (n : ℤ) : 9 * n - 20 ≤ n^2 := by
    rcases (show n ≤ 4 ∨ 5 ≤ n by omega) with h | h
    · nlinarith [mul_nonneg (show 0 ≤ 4 - n by omega)
        (show 0 ≤ 5 - n by omega)]
    · nlinarith [mul_nonneg (show 0 ≤ n - 4 by omega)
        (show 0 ≤ n - 5 by omega)]
  have hquadC (n : ℤ) : 3 * n - 2 ≤ n^2 := by
    rcases (show n ≤ 1 ∨ 2 ≤ n by omega) with h | h
    · nlinarith [mul_nonneg (show 0 ≤ 1 - n by omega)
        (show 0 ≤ 2 - n by omega)]
    · nlinarith [mul_nonneg (show 0 ≤ n - 1 by omega)
        (show 0 ≤ n - 2 by omega)]
  have hin : (∑ v ∈ S, (9 * ρ v - 20)) ≤ ∑ v ∈ S, (ρ v)^2 := by
    apply Finset.sum_le_sum
    intro v _
    exact hquadS (ρ v)
  have hout : (∑ v ∈ Finset.univ \ S, (3 * ρ v - 2)) ≤
      ∑ v ∈ Finset.univ \ S, (ρ v)^2 := by
    apply Finset.sum_le_sum
    intro v _
    exact hquadC (ρ v)
  have hlinS : (∑ v ∈ S, (9 * ρ v - 20)) =
      9 * (∑ v ∈ S, ρ v) - 20 * S.card := by
    rw [Finset.sum_sub_distrib]
    have hm : (∑ v ∈ S, 9 * ρ v) = 9 * (∑ v ∈ S, ρ v) := by
      rw [Finset.mul_sum]
    rw [hm]
    simp [mul_comm]
  have hlinC : (∑ v ∈ Finset.univ \ S, (3 * ρ v - 2)) =
      3 * (∑ v ∈ Finset.univ \ S, ρ v) -
        2 * (Finset.univ \ S).card := by
    rw [Finset.sum_sub_distrib]
    have hm : (∑ v ∈ Finset.univ \ S, 3 * ρ v) =
        3 * (∑ v ∈ Finset.univ \ S, ρ v) := by
      rw [Finset.mul_sum]
    rw [hm]
    simp [mul_comm]
  have hsplit : (∑ v ∈ S, (ρ v)^2) +
      (∑ v ∈ Finset.univ \ S, (ρ v)^2) =
        ∑ v : V, (ρ v)^2 := by
    exact Finset.sum_add_sum_compl S (fun v => (ρ v)^2)
  rw [hlinS] at hin
  rw [hlinC] at hout
  omega

/-- The 12-point edge cap in one actual graph, reduced to its remaining
squared-contact identity. The first moments are proved from that graph. -/
theorem graph_twelve_point_edge_cap_from_square_moment
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (S : Finset V)
    (hcard : S.card = 12)
    (hsquare : (∑ v : V, (contactCount G S v)^2) =
      432 - 2 * (((G.induce (S : Set V)).edgeFinset.card : ℤ))) :
    (G.induce (S : Set V)).edgeFinset.card ≤ 24 := by
  let e : ℤ := ((G.induce (S : Set V)).edgeFinset.card : ℤ)
  have hcardC : (Finset.univ \ S).card = 87 := by
    have hs := Finset.card_sdiff_add_card_inter (Finset.univ : Finset V) S
    simp only [Finset.univ_inter, Finset.card_univ] at hs
    have hv := h.card
    omega
  have hinside : (∑ v ∈ S, contactCount G S v) = 2 * e := by
    exact contact_inside_double G S
  have htotal : (∑ v : V, contactCount G S v) = 168 := by
    rw [contact_total G h S, hcard]
    norm_num
  have houtside : (∑ v ∈ Finset.univ \ S, contactCount G S v) =
      168 - 2 * e := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ S)]
    rw [htotal, hinside]
  have he : e ≤ 24 :=
    twelve_point_edge_cap_from_moments S (contactCount G S) e
      hcard hcardC hinside houtside hsquare
  change (((G.induce (S : Set V)).edgeFinset.card : ℤ) ≤ 24) at he
  exact_mod_cast he

/-- Every twelve-vertex set in an actual SRG(99,14,1,2) has at most
twenty-four induced edges. -/
theorem graph_twelve_point_edge_cap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (S : Finset V)
    (hcard : S.card = 12) :
    (G.induce (S : Set V)).edgeFinset.card ≤ 24 := by
  apply graph_twelve_point_edge_cap_from_square_moment G h S hcard
  rw [contact_square_moment G h S, contact_inside_double G S, hcard]
  ring

/-- If twelve owners each have at least four owner neighbors, the sharp
24-edge cap makes every owner degree exactly four. -/
theorem owner_regular_from_edge_cap
    {F : Type*} [Fintype F] [DecidableEq F]
    (D : SimpleGraph F) [DecidableRel D.Adj] (O : Finset F)
    (hcard : O.card = 12)
    (hlower : ∀ z ∈ O, 4 ≤ (D.neighborFinset z ∩ O).card)
    (hbound : (∑ z ∈ O, (D.neighborFinset z ∩ O).card) ≤ 48) :
    ∀ z ∈ O, (D.neighborFinset z ∩ O).card = 4 := by
  have hbase : (∑ _z ∈ O, (4 : ℕ)) = 48 := by simp [hcard]
  intro z hz
  have hle := hlower z hz
  by_contra hn
  have hlt : 4 < (D.neighborFinset z ∩ O).card := by omega
  have hstrict : (∑ _w ∈ O, (4 : ℕ)) <
      ∑ w ∈ O, (D.neighborFinset w ∩ O).card := by
    apply Finset.sum_lt_sum hlower
    exact ⟨z, hz, hlt⟩
  omega

/-- The sharp edge cap turns a graph-derived lower owner degree bound into
four-regularity in the induced owner graph. -/
theorem graph_owner_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (O : Finset V)
    (hcard : O.card = 12)
    (hlower : ∀ z ∈ O, 4 ≤ (G.neighborFinset z ∩ O).card) :
    ∀ z ∈ O, (G.neighborFinset z ∩ O).card = 4 := by
  have hcap := graph_twelve_point_edge_cap G h O hcard
  have hdegree : ((∑ z ∈ O, (G.neighborFinset z ∩ O).card : ℕ) : ℤ) =
      2 * (((G.induce (O : Set V)).edgeFinset.card : ℕ) : ℤ) := by
    simpa only [contactCount, Nat.cast_sum] using contact_inside_double G O
  have hsumInt : ((∑ z ∈ O, (G.neighborFinset z ∩ O).card : ℕ) : ℤ) ≤ 48 := by
    omega
  have hsum : (∑ z ∈ O, (G.neighborFinset z ∩ O).card) ≤ 48 := by
    exact_mod_cast hsumInt
  exact owner_regular_from_edge_cap G O hcard hlower hsum

/-- The exact first and square contact moments outside twelve four-regular
owners and three zero-contact roots follow from the same graph's SRG moments. -/
theorem graph_outside_owner_moments
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (O T : Finset V)
    (hOcard : O.card = 12) (hTcard : T.card = 3)
    (hdisj : Disjoint O T)
    (hregular : ∀ u ∈ O, contactCount G O u = 4)
    (hroots : ∀ u ∈ T, contactCount G O u = 0) :
    ((Finset.univ \ (O ∪ T)).card = 84) ∧
      (∑ u ∈ Finset.univ \ (O ∪ T), contactCount G O u) = 120 ∧
      (∑ u ∈ Finset.univ \ (O ∪ T), (contactCount G O u)^2) = 192 := by
  have hcardUT : (O ∪ T).card = 15 := by
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  have hcardX : (Finset.univ \ (O ∪ T)).card = 84 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ (O ∪ T))]
    have hv := h.card
    simp only [Finset.card_univ]
    omega
  have hinside : (∑ u ∈ O, contactCount G O u) = 48 := by
    calc
      _ = ∑ _u ∈ O, (4 : ℤ) := by
        apply Finset.sum_congr rfl
        exact hregular
      _ = 48 := by simp [hOcard]
  have hrootSum : (∑ u ∈ T, contactCount G O u) = 0 := by
    calc
      _ = ∑ _u ∈ T, (0 : ℤ) := by
        apply Finset.sum_congr rfl
        exact hroots
      _ = 0 := by simp
  have htotal : (∑ u : V, contactCount G O u) = 168 := by
    rw [contact_total G h O, hOcard]
    norm_num
  have hXsum : (∑ u ∈ Finset.univ \ (O ∪ T), contactCount G O u) = 120 := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ (O ∪ T))]
    rw [htotal, Finset.sum_union hdisj, hinside, hrootSum]
    norm_num
  have hinsideSq : (∑ u ∈ O, (contactCount G O u)^2) = 192 := by
    calc
      _ = ∑ _u ∈ O, (16 : ℤ) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hregular u hu]
        norm_num
      _ = 192 := by simp [hOcard]
  have hrootSq : (∑ u ∈ T, (contactCount G O u)^2) = 0 := by
    calc
      _ = ∑ _u ∈ T, (0 : ℤ) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hroots u hu]
        norm_num
      _ = 0 := by simp
  have htotalSq : (∑ u : V, (contactCount G O u)^2) = 384 := by
    rw [contact_square_moment G h O, hOcard, hinside]
    norm_num
  have hXsq : (∑ u ∈ Finset.univ \ (O ∪ T), (contactCount G O u)^2) = 192 := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ (O ∪ T))]
    rw [htotalSq, Finset.sum_union hdisj, hinsideSq, hrootSq]
    norm_num
  exact ⟨hcardX, hXsum, hXsq⟩

/-- The roots of an actual triangle automatically satisfy the disjointness
and zero-contact inputs of the outside moment theorem for any far owner set. -/
theorem graph_outside_far_owner_moments
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (a b c : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (O : Finset V) (hOcard : O.card = 12)
    (hfar : ∀ z ∈ O, z ∈ triangleFarSet G a b c)
    (hregular : ∀ z ∈ O, contactCount G O z = 4) :
    ((Finset.univ \ (O ∪ ({a, b, c} : Finset V))).card = 84) ∧
      (∑ z ∈ Finset.univ \ (O ∪ ({a, b, c} : Finset V)),
        contactCount G O z) = 120 ∧
      (∑ z ∈ Finset.univ \ (O ∪ ({a, b, c} : Finset V)),
        (contactCount G O z)^2) = 192 := by
  have hTcard : ({a, b, c} : Finset V).card = 3 := by
    have habne := G.ne_of_adj hab
    have hacne := G.ne_of_adj hac
    have hbcne := G.ne_of_adj hbc
    simp [habne, hacne, hbcne]
  have hzero := triangle_root_contact_zero G a b c O hfar
  have hroots : ∀ z ∈ ({a, b, c} : Finset V), contactCount G O z = 0 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hzero.1
    · exact hzero.2.1
    · exact hzero.2.2
  exact graph_outside_owner_moments G h O {a, b, c} hOcard hTcard
    (triangle_far_disjoint_roots G a b c O hfar) hregular hroots

/-- Equality in the outside contact moments forces the 36 shell contacts to
be two and the other 48 nonroot, nonowner contacts to be one. -/
theorem exact_contact_moments
    {X : Type*} [Fintype X] [DecidableEq X]
    (S : Finset X) (ρ : X → ℤ)
    (hcardX : Fintype.card X = 84)
    (hcardS : S.card = 36)
    (hsum : (∑ z : X, ρ z) = 120)
    (hsquare : (∑ z : X, (ρ z)^2) = 192)
    (hshell : (∑ z ∈ S, ρ z) = 72) :
    (∀ z ∈ S, ρ z = 2) ∧ (∀ z ∉ S, ρ z = 1) := by
  let q : ℤ → ℤ := fun n => n^2 - 3 * n + 2
  have hq (n : ℤ) : 0 ≤ q n := by
    dsimp [q]
    rcases (show n ≤ 1 ∨ 2 ≤ n by omega) with h | h
    · nlinarith [mul_nonneg (show 0 ≤ 1 - n by omega)
        (show 0 ≤ 2 - n by omega)]
    · nlinarith [mul_nonneg (show 0 ≤ n - 1 by omega)
        (show 0 ≤ n - 2 by omega)]
  have hzero : (∑ z : X, q (ρ z)) = 0 := by
    simp only [q, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const_zero]
    simp [hsum, hsquare, hcardX]
  have hvalues (z : X) : ρ z = 1 ∨ ρ z = 2 := by
    have hz : q (ρ z) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hq (ρ w))).mp hzero z
        (Finset.mem_univ z)
    have hf : (ρ z - 1) * (ρ z - 2) = 0 := by dsimp [q] at hz; nlinarith
    rcases mul_eq_zero.mp hf with h | h
    · left; omega
    · right; omega
  have hSconst : (∑ _z ∈ S, (2 : ℤ)) = 72 := by simp [hcardS]
  have hCcard : (Finset.univ \ S).card = 48 := by
    have hs := Finset.card_sdiff_add_card_inter (Finset.univ : Finset X) S
    simp only [Finset.univ_inter, Finset.card_univ] at hs
    omega
  have hCsum : (∑ z ∈ Finset.univ \ S, ρ z) = 48 := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ S)]
    rw [hsum, hshell]
    norm_num
  have hCconst : (∑ _z ∈ Finset.univ \ S, (1 : ℤ)) = 48 := by simp [hCcard]
  constructor
  · intro z hz
    have hle : ∀ w ∈ S, ρ w ≤ 2 := by
      intro w _
      rcases hvalues w with h | h <;> omega
    by_contra hn
    have hlt : ρ z < 2 := by rcases hvalues z with h | h <;> omega
    have hstrict : (∑ w ∈ S, ρ w) < ∑ _w ∈ S, (2 : ℤ) :=
      Finset.sum_lt_sum hle ⟨z, hz, hlt⟩
    omega
  · intro z hz
    have hzC : z ∈ Finset.univ \ S := by simp [hz]
    have hle : ∀ w ∈ Finset.univ \ S, (1 : ℤ) ≤ ρ w := by
      intro w _
      rcases hvalues w with h | h <;> omega
    by_contra hn
    have hlt : (1 : ℤ) < ρ z := by rcases hvalues z with h | h <;> omega
    have hstrict : (∑ _w ∈ Finset.univ \ S, (1 : ℤ)) <
        ∑ w ∈ Finset.univ \ S, ρ w :=
      Finset.sum_lt_sum hle ⟨z, hzC, hlt⟩
    omega

/-- The contact-moment equality on a literal finite vertex set, with a
specified shell inside it. -/
theorem exact_contact_moments_on
    {V : Type*} [DecidableEq V] (X S : Finset V) (ρ : V → ℤ)
    (hSX : S ⊆ X) (hcardX : X.card = 84) (hcardS : S.card = 36)
    (hsum : (∑ z ∈ X, ρ z) = 120)
    (hsquare : (∑ z ∈ X, (ρ z)^2) = 192)
    (hshell : (∑ z ∈ S, ρ z) = 72) :
    (∀ z ∈ S, ρ z = 2) ∧ (∀ z ∈ X \ S, ρ z = 1) := by
  let q : ℤ → ℤ := fun n => n^2 - 3 * n + 2
  have hq (n : ℤ) : 0 ≤ q n := by
    dsimp [q]
    rcases (show n ≤ 1 ∨ 2 ≤ n by omega) with h | h
    · nlinarith [mul_nonneg (show 0 ≤ 1 - n by omega)
        (show 0 ≤ 2 - n by omega)]
    · nlinarith [mul_nonneg (show 0 ≤ n - 1 by omega)
        (show 0 ≤ n - 2 by omega)]
  have hzero : (∑ z ∈ X, q (ρ z)) = 0 := by
    simp only [q, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const_zero]
    simp [hsum, hsquare, hcardX]
  have hvalues (z : V) (hz : z ∈ X) : ρ z = 1 ∨ ρ z = 2 := by
    have hzeroz : q (ρ z) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hq (ρ w))).mp hzero z hz
    have hf : (ρ z - 1) * (ρ z - 2) = 0 := by
      dsimp [q] at hzeroz
      nlinarith
    rcases mul_eq_zero.mp hf with h | h
    · left; omega
    · right; omega
  have hSconst : (∑ _z ∈ S, (2 : ℤ)) = 72 := by simp [hcardS]
  have hCcard : (X \ S).card = 48 := by
    rw [Finset.card_sdiff_of_subset hSX]
    omega
  have hCsum : (∑ z ∈ X \ S, ρ z) = 48 := by
    rw [Finset.sum_sdiff_eq_sub hSX]
    omega
  have hCconst : (∑ _z ∈ X \ S, (1 : ℤ)) = 48 := by simp [hCcard]
  constructor
  · intro z hz
    have hle : ∀ w ∈ S, ρ w ≤ 2 := by
      intro w hw
      rcases hvalues w (hSX hw) with h | h <;> omega
    by_contra hn
    have hlt : ρ z < 2 := by rcases hvalues z (hSX hz) with h | h <;> omega
    have hstrict : (∑ w ∈ S, ρ w) < ∑ _w ∈ S, (2 : ℤ) :=
      Finset.sum_lt_sum hle ⟨z, hz, hlt⟩
    omega
  · intro z hz
    have hle : ∀ w ∈ X \ S, (1 : ℤ) ≤ ρ w := by
      intro w hw
      rcases hvalues w (Finset.mem_sdiff.mp hw).1 with h | h <;> omega
    by_contra hn
    have hlt : (1 : ℤ) < ρ z := by
      rcases hvalues z (Finset.mem_sdiff.mp hz).1 with h | h <;> omega
    have hstrict : (∑ _w ∈ X \ S, (1 : ℤ)) <
        ∑ w ∈ X \ S, ρ w :=
      Finset.sum_lt_sum hle ⟨z, hz, hlt⟩
    omega

/-- In the original SRG, the outside owner-contact moments and six shell
neighbors per owner determine every individual outside contact count. -/
theorem graph_exact_far_owner_contacts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (a b c : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (O S : Finset V) (hOcard : O.card = 12)
    (hfar : ∀ z ∈ O, z ∈ triangleFarSet G a b c)
    (hregular : ∀ z ∈ O, contactCount G O z = 4)
    (hSX : S ⊆ Finset.univ \ (O ∪ ({a, b, c} : Finset V)))
    (hScard : S.card = 36)
    (hsix : ∀ z ∈ O, (G.neighborFinset z ∩ S).card = 6) :
    (∀ z ∈ S, contactCount G O z = 2) ∧
      (∀ z ∈ (Finset.univ \ (O ∪ ({a, b, c} : Finset V))) \ S,
        contactCount G O z = 1) := by
  obtain ⟨hcard, hsum, hsquare⟩ :=
    graph_outside_far_owner_moments G h a b c hab hac hbc O hOcard hfar hregular
  exact exact_contact_moments_on _ S (contactCount G O) hSX hcard hScard
    hsum hsquare (shell_contact_sum G O S hOcard hsix)

/-- Final positive-definite step of the point-frame identity: the owner point
sum and triangle point coincide once their three exact pairings are known. -/
theorem owner_point_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (τ : E) {V : Type*} (O : Finset V) (p : V → E)
    (hτ : ⟪τ, τ⟫_ℝ = 4)
    (hO : ⟪∑ z ∈ O, p z, ∑ z ∈ O, p z⟫_ℝ = 4)
    (hpair : ⟪∑ z ∈ O, p z, τ⟫_ℝ = 4) :
    (∑ z ∈ O, p z) = τ := by
  have hz : ⟪(∑ z ∈ O, p z) - τ, (∑ z ∈ O, p z) - τ⟫_ℝ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    nlinarith [real_inner_comm τ (∑ z ∈ O, p z)]
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp hz)

/-- The quotient rows follow from exact owner contacts and degree eight;
instantiate `D` with the graph-derived far graph in the owned-twelve argument. -/
theorem far_quotient_from_contacts
    {F : Type*} [Fintype F] [DecidableEq F]
    (D : SimpleGraph F) [DecidableRel D.Adj] (O : Finset F)
    (hdeg : ∀ z, (D.neighborFinset z).card = 8)
    (hcontact : ∀ z, (D.neighborFinset z ∩ O).card =
      if z ∈ O then 4 else 1) :
    ∀ z, (D.neighborFinset z ∩ O).card = (if z ∈ O then 4 else 1) ∧
      (D.neighborFinset z \ O).card = (if z ∈ O then 4 else 7) := by
  intro z
  constructor
  · exact hcontact z
  · have hs := Finset.card_inter_add_card_sdiff (D.neighborFinset z) O
    have hd := hdeg z
    have hc := hcontact z
    split_ifs at hc ⊢ <;> omega

/-- Once the owner contacts are four and one, the weighted slice equation
forces every far vertex to meet four prism-shell vertices. -/
theorem prism_contacts_four
    {F : Type*} [Fintype F] [DecidableEq F]
    (D : SimpleGraph F) [DecidableRel D.Adj] (O : Finset F)
    (b : F → ℕ)
    (hcontact : ∀ z, (D.neighborFinset z ∩ O).card =
      if z ∈ O then 4 else 1)
    (hslice : ∀ z, (D.neighborFinset z ∩ O).card + b z =
      3 * (if z ∈ O then 1 else 0) + 5) :
    ∀ z, b z = 4 := by
  intro z
  have hc := hcontact z
  have hs := hslice z
  split_ifs at hc hs <;> omega

#print axioms Conway99Formal.OwnedTwelve.incident_sum
#print axioms Conway99Formal.OwnedTwelve.triangleFarGraph_adj
#print axioms Conway99Formal.OwnedTwelve.srg_common_neighbor_cap

#print axioms Conway99Formal.OwnedTwelve.common_neighbor_card
#print axioms Conway99Formal.OwnedTwelve.triangleFar_common_neighbor_cap

#print axioms Conway99Formal.OwnedTwelve.far_root_common_two

#print axioms Conway99Formal.OwnedTwelve.triangle_edge_completer_unique

#print axioms Conway99Formal.OwnedTwelve.root_contact_disjoint
#print axioms Conway99Formal.OwnedTwelve.triangleFar_degree_eight
#print axioms Conway99Formal.OwnedTwelve.binary_owners
#print axioms Conway99Formal.OwnedTwelve.graph_binary_owners
#print axioms Conway99Formal.OwnedTwelve.graph_binary_owners_of_triangle
#print axioms Conway99Formal.OwnedTwelve.binary_support_card
#print axioms Conway99Formal.OwnedTwelve.graph_owner_support_card_of_triangle
#print axioms Conway99Formal.OwnedTwelve.contact_total
#print axioms Conway99Formal.OwnedTwelve.contact_sum_symmetry
#print axioms Conway99Formal.OwnedTwelve.shell_contact_sum
#print axioms Conway99Formal.OwnedTwelve.triangle_far_disjoint_roots
#print axioms Conway99Formal.OwnedTwelve.triangle_root_contact_zero
#print axioms Conway99Formal.OwnedTwelve.contact_inside_double

#print axioms Conway99Formal.OwnedTwelve.contact_square_moment
#print axioms Conway99Formal.OwnedTwelve.twelve_point_edge_cap_from_moments
#print axioms Conway99Formal.OwnedTwelve.graph_twelve_point_edge_cap_from_square_moment

#print axioms Conway99Formal.OwnedTwelve.graph_twelve_point_edge_cap
#print axioms Conway99Formal.OwnedTwelve.owner_regular_from_edge_cap

#print axioms Conway99Formal.OwnedTwelve.graph_owner_regular
#print axioms Conway99Formal.OwnedTwelve.graph_outside_owner_moments
#print axioms Conway99Formal.OwnedTwelve.graph_outside_far_owner_moments
#print axioms Conway99Formal.OwnedTwelve.exact_contact_moments
#print axioms Conway99Formal.OwnedTwelve.exact_contact_moments_on
#print axioms Conway99Formal.OwnedTwelve.graph_exact_far_owner_contacts
#print axioms Conway99Formal.OwnedTwelve.owner_point_sum
#print axioms Conway99Formal.OwnedTwelve.far_quotient_from_contacts
#print axioms Conway99Formal.OwnedTwelve.prism_contacts_four

end Conway99Formal.OwnedTwelve

namespace Conway99Formal.OwnedTwelve

/-- The exact selected-shell owner contacts, stated using only Mathlib graph
and Finset operations. Every owner and shell premise remains explicit. -/
theorem selected_shell_contacts_20261003
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (a b c : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (O S : Finset V) (hOcard : O.card = 12)
    (hfar : ∀ z ∈ O, z ≠ a ∧ z ≠ b ∧ z ≠ c ∧
      ¬ G.Adj z a ∧ ¬ G.Adj z b ∧ ¬ G.Adj z c)
    (hregular : ∀ z ∈ O, ((G.neighborFinset z ∩ O).card : ℤ) = 4)
    (hSX : S ⊆ Finset.univ \ (O ∪ ({a, b, c} : Finset V)))
    (hScard : S.card = 36)
    (hsix : ∀ z ∈ O, (G.neighborFinset z ∩ S).card = 6) :
    (∀ z ∈ S, ((G.neighborFinset z ∩ O).card : ℤ) = 2) ∧
      (∀ z ∈ (Finset.univ \ (O ∪ ({a, b, c} : Finset V))) \ S,
        ((G.neighborFinset z ∩ O).card : ℤ) = 1) := by
  have hf : ∀ z ∈ O, z ∈ triangleFarSet G a b c := by
    intro z hz
    simpa [triangleFarSet] using hfar z hz
  have hr : ∀ z ∈ O, contactCount G O z = 4 := by
    intro z hz
    simpa [contactCount] using hregular z hz
  simpa only [contactCount] using
    (graph_exact_far_owner_contacts G h a b c hab hac hbc O S hOcard
      hf hr hSX hScard hsix)

end Conway99Formal.OwnedTwelve

theorem solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (a b c : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (O S : Finset V) (hOcard : O.card = 12)
    (hfar : ∀ z ∈ O, z ≠ a ∧ z ≠ b ∧ z ≠ c ∧
      ¬ G.Adj z a ∧ ¬ G.Adj z b ∧ ¬ G.Adj z c)
    (hregular : ∀ z ∈ O, ((G.neighborFinset z ∩ O).card : ℤ) = 4)
    (hSX : S ⊆ Finset.univ \ (O ∪ ({a, b, c} : Finset V)))
    (hScard : S.card = 36)
    (hsix : ∀ z ∈ O, (G.neighborFinset z ∩ S).card = 6) :
    (∀ z ∈ S, ((G.neighborFinset z ∩ O).card : ℤ) = 2) ∧
      (∀ z ∈ (Finset.univ \ (O ∪ ({a, b, c} : Finset V))) \ S,
        ((G.neighborFinset z ∩ O).card : ℤ) = 1) := by
  exact Conway99Formal.OwnedTwelve.selected_shell_contacts_20261003
    G h a b c hab hac hbc O S hOcard hfar hregular hSX hScard hsix

#print axioms Conway99Formal.OwnedTwelve.selected_shell_contacts_20261003
#print axioms solution
