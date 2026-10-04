-- Prove2me | solution 1 for Conway99Formal.OrdinaryEdgeLabels.repeated_distinct_negative_edges_short_kernel
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T02:25:49.985787+00:00
-- url     : https://prove2.me/submissions/3dfd8656-7052-44c8-ad17-6a2994ca43e8

import Definitions.Def_Conway99_OrdinaryEdgeLabels_20261003

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Conway99Formal.OrdinaryEdgeLabels

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The integer triangle balance and the coset lower bound leave precisely
the three unordered image metrics in the source. -/
theorem triangle_types (d : OrdinaryData G) (a b c : V)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    (d.discrepancy a b = 0 ∧ d.discrepancy b c = 0 ∧
      d.discrepancy c a = 0) ∨
    (d.discrepancy a b = -1 ∧ d.discrepancy b c = 0 ∧
      d.discrepancy c a = 1) ∨
    (d.discrepancy a b = -1 ∧ d.discrepancy b c = 1 ∧
      d.discrepancy c a = 0) ∨
    (d.discrepancy a b = 0 ∧ d.discrepancy b c = -1 ∧
      d.discrepancy c a = 1) ∨
    (d.discrepancy a b = 0 ∧ d.discrepancy b c = 1 ∧
      d.discrepancy c a = -1) ∨
    (d.discrepancy a b = 1 ∧ d.discrepancy b c = -1 ∧
      d.discrepancy c a = 0) ∨
    (d.discrepancy a b = 1 ∧ d.discrepancy b c = 0 ∧
      d.discrepancy c a = -1) ∨
    (d.discrepancy a b = -1 ∧ d.discrepancy b c = -1 ∧
      d.discrepancy c a = 2) ∨
    (d.discrepancy a b = -1 ∧ d.discrepancy b c = 2 ∧
      d.discrepancy c a = -1) ∨
    (d.discrepancy a b = 2 ∧ d.discrepancy b c = -1 ∧
      d.discrepancy c a = -1) := by
  have h₁ := d.edge_lower a b hab
  have h₂ := d.edge_lower b c hbc
  have h₃ := d.edge_lower c a hca
  have hs := d.triangle_balance a b c hab hbc hca
  have hu₁ : d.discrepancy a b ≤ 2 := by omega
  have hu₂ : d.discrepancy b c ≤ 2 := by omega
  have hu₃ : d.discrepancy c a ≤ 2 := by omega
  have hc₁ : d.discrepancy a b = -1 ∨ d.discrepancy a b = 0 ∨
      d.discrepancy a b = 1 ∨ d.discrepancy a b = 2 := by omega
  have hc₂ : d.discrepancy b c = -1 ∨ d.discrepancy b c = 0 ∨
      d.discrepancy b c = 1 ∨ d.discrepancy b c = 2 := by omega
  rcases hc₁ with h | h | h | h <;>
    rcases hc₂ with h' | h' | h' | h' <;> omega

/-- The four edge discrepancy values encode the source's four possible
image pairings on individual graph edges. -/
theorem edge_pairing_values (d : OrdinaryData G) (a b : V)
    (hab : G.Adj a b) :
    (d.discrepancy a b = -1 → inner ℝ (image d a) (image d b) = -17) ∧
    (d.discrepancy a b = 0 → inner ℝ (image d a) (image d b) = -8) ∧
    (d.discrepancy a b = 1 → inner ℝ (image d a) (image d b) = 1) ∧
    (d.discrepancy a b = 2 → inner ℝ (image d a) (image d b) = 10) := by
  have hp := d.image_edge_pairing a b hab
  change inner ℝ (image d a) (image d b) =
    -8 + 9 * (d.discrepancy a b : ℝ) at hp
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    intro he
    rw [he] at hp
    norm_num at hp
    exact hp

/-- A negative edge cannot touch the ordinary center or its neighborhood. -/
theorem negative_edge_far (d : OrdinaryData G) (a b : V)
    (hab : G.Adj a b) (hneg : d.discrepancy a b = -1) :
    a ≠ d.ordinary ∧ b ≠ d.ordinary ∧
      ¬G.Adj d.ordinary a ∧ ¬G.Adj d.ordinary b := by
  have hval (v : V) := d.label_values a b v hab hneg
  have hcenter := d.label_at_ordinary a b hab hneg
  obtain ⟨κ, henda, hendb⟩ := d.endpoint_pairings a b hab hneg
  have ha : a ≠ d.ordinary := by
    intro heq
    subst a
    have hb : pointPair G d.ordinary b = -8 := by
      simp [pointPair, hab, G.ne_of_adj hab]
    have hd : pointPair G d.ordinary d.ordinary = 28 := by simp [pointPair]
    rw [hd, hb] at hcenter
    rcases hval d.ordinary with h | h <;> omega
  have hb : b ≠ d.ordinary := by
    intro heq
    subst b
    have haa : G.Adj d.ordinary a := hab.symm
    have hpa : pointPair G d.ordinary a = -8 := by
      simp [pointPair, haa, G.ne_of_adj haa]
    have hd : pointPair G d.ordinary d.ordinary = 28 := by simp [pointPair]
    rw [hpa, hd] at hcenter
    rcases hval d.ordinary with h | h <;> omega
  have hna : ¬G.Adj d.ordinary a := by
    intro hua
    have hpa : pointPair G d.ordinary a = -8 := by simp [pointPair, ha.symm, hua]
    by_cases hub : G.Adj d.ordinary b
    · have hpb : pointPair G d.ordinary b = -8 := by simp [pointPair, hb.symm, hub]
      rw [hpa, hpb] at hcenter
      rcases hval d.ordinary with h | h <;> omega
    · have hpb : pointPair G d.ordinary b = 1 := by simp [pointPair, hb.symm, hub]
      rw [hpa, hpb] at hcenter
      rw [hpa] at henda
      rw [hpb] at hendb
      have hu : d.labelPair a b d.ordinary = 7 := by omega
      have hva : d.labelPair a b a = 7 := by
        rcases hval a with h | h
        · rcases hval b with h' | h' <;> omega
        · exact h
      exact d.label_independent a b d.ordinary a hab hneg hua hu hva
  have hnb : ¬G.Adj d.ordinary b := by
    intro hub
    have hpa : pointPair G d.ordinary a = 1 := by simp [pointPair, ha.symm, hna]
    have hpb : pointPair G d.ordinary b = -8 := by simp [pointPair, hb.symm, hub]
    rw [hpa, hpb] at hcenter
    rw [hpa] at henda
    rw [hpb] at hendb
    have hu : d.labelPair a b d.ordinary = 7 := by omega
    have hvb : d.labelPair a b b = 7 := by
      rcases hval a with h | h <;> rcases hval b with h' | h' <;> omega
    exact d.label_independent a b d.ordinary b hab hneg hub hu hvb
  exact ⟨ha, hb, hna, hnb⟩

private theorem summand_zero_of_nonneg_sum_zero {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → ℤ)
    (hnonneg : ∀ x ∈ s, 0 ≤ f x) (hsum : s.sum f = 0)
    (x : ι) (hx : x ∈ s) : f x = 0 := by
  exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum x hx

/-- Every edge incident with the marked vertex or one of its neighbors has
zero discrepancy; this uses the graph-owned vertex balance. -/
theorem edge_zero_at_near_vertex (d : OrdinaryData G) (a b : V)
    (hab : G.Adj a b)
    (hnear : a = d.ordinary ∨ G.Adj d.ordinary a) :
    d.discrepancy a b = 0 := by
  let s := Finset.univ.filter (G.Adj a)
  have hnonneg : ∀ x ∈ s, 0 ≤ d.discrepancy a x := by
    intro x hx
    have hax : G.Adj a x := (Finset.mem_filter.mp hx).2
    have hlo := d.edge_lower a x hax
    by_cases hzero : d.discrepancy a x = -1
    · obtain ⟨hfar, _, hnonadj, _⟩ := negative_edge_far d a x hax hzero
      rcases hnear with heq | hadj
      · exact False.elim (hfar heq)
      · exact False.elim (hnonadj hadj)
    · omega
  have hb : b ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
  exact summand_zero_of_nonneg_sum_zero s (d.discrepancy a)
    hnonneg (d.vertex_balance a) b hb

/-- An actual triangle touching the marked closed neighborhood has all
three edge discrepancies zero. -/
theorem nearby_triangle_edges_zero (d : OrdinaryData G) (a b c : V)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hnear : a = d.ordinary ∨ G.Adj d.ordinary a) :
    d.discrepancy a b = 0 ∧ d.discrepancy b c = 0 ∧
      d.discrepancy c a = 0 := by
  have hab0 := edge_zero_at_near_vertex d a b hab hnear
  have hac0 := edge_zero_at_near_vertex d a c hca.symm hnear
  have hca0 : d.discrepancy c a = 0 := by
    rw [d.discrepancy_symm]
    exact hac0
  have hsum := d.triangle_balance a b c hab hbc hca
  refine ⟨hab0, ?_, hca0⟩
  omega

private theorem point_inner_preserved (d : OrdinaryData G) (v : V) :
    inner ℝ (image d v) (image d v) =
      inner ℝ (d.point v) (d.point v) := by
  unfold image
  rw [d.image_norm v, d.point_gram v v]
  simp [pointPair]

private theorem edge_inner_preserved (d : OrdinaryData G) (a b : V)
    (hab : G.Adj a b) (he : d.discrepancy a b = 0) :
    inner ℝ (image d a) (image d b) =
      inner ℝ (d.point a) (d.point b) := by
  unfold image
  rw [d.image_edge_pairing a b hab, he, d.point_gram a b]
  simp [pointPair, G.ne_of_adj hab, hab]

/-- For each actual triangle touching the marked closed neighborhood, the
ordinary operator preserves every inner product within that triangle's
three-point span. This does not assert cross-span isometry. -/
theorem nearby_triangle_span_isometry (d : OrdinaryData G) (a b c : V)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hnear : a = d.ordinary ∨ G.Adj d.ordinary a) :
    ∀ x ∈ Submodule.span ℝ ({d.point a, d.point b, d.point c} : Set Space),
      ∀ y ∈ Submodule.span ℝ ({d.point a, d.point b, d.point c} : Set Space),
        inner ℝ (d.op d.ordinary x) (d.op d.ordinary y) = inner ℝ x y := by
  obtain ⟨hab0, hbc0, hca0⟩ :=
    nearby_triangle_edges_zero d a b c hab hbc hca hnear
  have hba0 : d.discrepancy b a = 0 := by
    rw [d.discrepancy_symm b a]
    exact hab0
  have hac0 : d.discrepancy a c = 0 := by
    rw [d.discrepancy_symm a c]
    exact hca0
  have hcb0 : d.discrepancy c b = 0 := by
    rw [d.discrepancy_symm c b]
    exact hbc0
  let s : Set Space := {d.point a, d.point b, d.point c}
  have hgen (x y : Space) (hx : x ∈ s) (hy : y ∈ s) :
      inner ℝ (d.op d.ordinary x) (d.op d.ordinary y) = inner ℝ x y := by
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact point_inner_preserved d a
    · exact edge_inner_preserved d a b hab hab0
    · exact edge_inner_preserved d a c hca.symm hac0
    · exact edge_inner_preserved d b a hab.symm hba0
    · exact point_inner_preserved d b
    · exact edge_inner_preserved d b c hbc hbc0
    · exact edge_inner_preserved d c a hca hca0
    · exact edge_inner_preserved d c b hbc.symm hcb0
    · exact point_inner_preserved d c
  intro x hx y hy
  change x ∈ Submodule.span ℝ s at hx
  change y ∈ Submodule.span ℝ s at hy
  refine Submodule.span_induction₂ (s := s) (t := s)
    (p := fun x y _ _ =>
      inner ℝ (d.op d.ordinary x) (d.op d.ordinary y) = inner ℝ x y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro x y hxs hys
    exact hgen x y hxs hys
  · intro y hy
    simp
  · intro x hx
    simp
  · intro x y z hx hy hz h₁ h₂
    simpa [map_add, inner_add_left] using congrArg₂ (· + ·) h₁ h₂
  · intro x y z hx hy hz h₁ h₂
    simpa [map_add, inner_add_right] using congrArg₂ (· + ·) h₁ h₂
  · intro r x y hx hy h
    simpa [map_smul, inner_smul_left] using congrArg (fun t : ℝ => r * t) h
  · intro r x y hx hy h
    simpa [map_smul, inner_smul_right] using congrArg (fun t : ℝ => r * t) h

/-- The operator's negative-edge vector belongs to the same starting lattice
for every permitted lattice choice, given preservation of its triangle lattice. -/
theorem label_vector_in_starting_lattice (d : OrdinaryData G) (a b : V) :
    labelVector d a b ∈ d.startingLattice := by
  apply d.triangle_le_starting
  apply d.triangleLattice.neg_mem
  apply d.triangleLattice.add_mem
  · exact d.op_preserves_triangle_lattice d.ordinary (d.point a)
      (d.point_in_triangle_lattice a)
  · exact d.op_preserves_triangle_lattice d.ordinary (d.point b)
      (d.point_in_triangle_lattice b)

/-- The source's divided point-difference inclusion puts the repeated-label
kernel candidate in the common starting lattice. -/
theorem repeated_vector_in_starting_lattice (d : OrdinaryData G)
    (a b c e : V) :
    repeatedKernelVector d a b c e ∈ d.startingLattice := by
  have hk : repeatedKernelVector d a b c e =
      (1 / 3 : ℝ) • (d.point a - d.point c) +
        (1 / 3 : ℝ) • (d.point b - d.point e) := by
    simp only [repeatedKernelVector]
    module
  rw [hk]
  exact d.startingLattice.add_mem
    (d.divided_point_difference_in_starting a c)
    (d.divided_point_difference_in_starting b e)

/-- Equal vector labels on two edges annihilate the divided point difference
under the same graph-owned operator. -/
theorem repeated_label_kernel (d : OrdinaryData G) (a b c e : V)
    (h : labelVector d a b = labelVector d c e) :
    d.op d.ordinary (repeatedKernelVector d a b c e) = 0 := by
  have heq : image d a + image d b = image d c + image d e := by
    exact neg_injective h
  simp only [repeatedKernelVector, map_smul, map_sub, map_add]
  have hzero : image d a + image d b - image d c - image d e = 0 := by
    calc
      _ = (image d a + image d b) - (image d c + image d e) := by module
      _ = 0 := by rw [heq, sub_self]
  change (1 / 3 : ℝ) •
    (image d a + image d b - image d c - image d e) = 0
  rw [hzero, smul_zero]

/-- The two negative edges of the third triangle type have different
operator-produced vector labels. -/
theorem third_type_distinct_labels (d : OrdinaryData G) (a b c : V)
    (hbc : G.Adj b c) (hbc₂ : d.discrepancy b c = 2) :
    labelVector d a b ≠ labelVector d a c := by
  intro hlabels
  have hsum : image d a + image d b = image d a + image d c :=
    neg_injective hlabels
  have heq : image d b = image d c := add_left_cancel hsum
  have hp := d.image_edge_pairing b c hbc
  have hn := d.image_norm b
  change inner ℝ (image d b) (image d b) = 28 at hn
  change inner ℝ (image d b) (image d c) =
    -8 + 9 * (d.discrepancy b c : ℝ) at hp
  rw [← heq, hbc₂] at hp
  norm_num at hp
  have hn' : ‖image d b‖ ^ 2 = 28 := by simpa using hn
  linarith

/-- The four possible edges joining two ordered graph edges. -/
def crossEdgeCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c e : V) : ℕ :=
  (if G.Adj a c then 1 else 0) + (if G.Adj a e then 1 else 0) +
    (if G.Adj b c then 1 else 0) + (if G.Adj b e then 1 else 0)

private theorem unique_common_neighbor (d : OrdinaryData G)
    {x y z w : V} (hxy : G.Adj x y)
    (hxz : G.Adj x z) (hyz : G.Adj y z)
    (hxw : G.Adj x w) (hyw : G.Adj y w) : z = w := by
  have hcard : Fintype.card (G.commonNeighbors x y) ≤ 1 := by
    rw [d.srg.of_adj x y hxy]
  have huniq := (Fintype.card_le_one_iff).mp hcard
  have hz : z ∈ G.commonNeighbors x y :=
    (G.mem_commonNeighbors).2 ⟨hxz, hyz⟩
  have hw : w ∈ G.commonNeighbors x y :=
    (G.mem_commonNeighbors).2 ⟨hxw, hyw⟩
  exact congrArg Subtype.val (huniq ⟨z, hz⟩ ⟨w, hw⟩)

/-- Two disjoint graph edges have at most two cross edges, since three
would create an edge with two common neighbors. -/
theorem cross_edge_count_le_two (d : OrdinaryData G) (a b c e : V)
    (hab : G.Adj a b) (hce : G.Adj c e)
    (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) :
    crossEdgeCount G a b c e ≤ 2 := by
  have h₁ : ¬(G.Adj a c ∧ G.Adj a e ∧ G.Adj b c) := by
    rintro ⟨hac', hae', hbc'⟩
    exact hbe (unique_common_neighbor d hac' hab hbc'.symm hae' hce)
  have h₂ : ¬(G.Adj a c ∧ G.Adj a e ∧ G.Adj b e) := by
    rintro ⟨hac', hae', hbe'⟩
    exact hbc (unique_common_neighbor d hae' hab hbe'.symm hac' hce.symm)
  have h₃ : ¬(G.Adj a c ∧ G.Adj b c ∧ G.Adj b e) := by
    rintro ⟨hac', hbc', hbe'⟩
    exact hae (unique_common_neighbor d hbc' hab.symm hac'.symm hbe' hce)
  have h₄ : ¬(G.Adj a e ∧ G.Adj b c ∧ G.Adj b e) := by
    rintro ⟨hae', hbc', hbe'⟩
    exact hac (unique_common_neighbor d hbe' hab.symm hae'.symm hbc' hce.symm)
  by_cases p : G.Adj a c <;> by_cases q : G.Adj a e <;>
    by_cases r : G.Adj b c <;> by_cases s : G.Adj b e <;>
    simp_all [crossEdgeCount]

/-- The exact point-Gram calculation for two vertex-disjoint graph edges. -/
theorem repeated_disjoint_norm_formula (d : OrdinaryData G) (a b c e : V)
    (hab : G.Adj a b) (hce : G.Adj c e)
    (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) :
    inner ℝ (repeatedKernelVector d a b c e)
      (repeatedKernelVector d a b c e) =
        8 + 2 * (crossEdgeCount G a b c e : ℝ) := by
  have habne := G.ne_of_adj hab
  have hcene := G.ne_of_adj hce
  have hba : b ≠ a := habne.symm
  have hca : c ≠ a := hac.symm
  have hea : e ≠ a := hae.symm
  have hcb : c ≠ b := hbc.symm
  have heb : e ≠ b := hbe.symm
  have hec : e ≠ c := hcene.symm
  unfold repeatedKernelVector
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right]
  simp_rw [d.point_gram]
  unfold crossEdgeCount
  by_cases p : G.Adj a c <;> by_cases q : G.Adj a e <;>
    by_cases r : G.Adj b c <;> by_cases s : G.Adj b e <;>
    simp_all [pointPair, G.adj_comm] <;> ring

/-- Equal labels on two vertex-disjoint negative edges give a nonzero
short kernel vector in the common starting lattice. -/
theorem repeated_disjoint_short_kernel (d : OrdinaryData G) (a b c e : V)
    (hab : G.Adj a b) (hce : G.Adj c e)
    (_hnegab : d.discrepancy a b = -1)
    (_hnegce : d.discrepancy c e = -1)
    (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e)
    (hlabels : labelVector d a b = labelVector d c e) :
    repeatedKernelVector d a b c e ∈ d.startingLattice ∧
      d.op d.ordinary (repeatedKernelVector d a b c e) = 0 ∧
      repeatedKernelVector d a b c e ≠ 0 ∧
      (‖repeatedKernelVector d a b c e‖ ^ 2 = 8 ∨
        ‖repeatedKernelVector d a b c e‖ ^ 2 = 10 ∨
        ‖repeatedKernelVector d a b c e‖ ^ 2 = 12) := by
  have hcount := cross_edge_count_le_two d a b c e hab hce hac hae hbc hbe
  have hcases : crossEdgeCount G a b c e = 0 ∨
      crossEdgeCount G a b c e = 1 ∨ crossEdgeCount G a b c e = 2 := by
    omega
  have hnorm : ‖repeatedKernelVector d a b c e‖ ^ 2 =
      8 + 2 * (crossEdgeCount G a b c e : ℝ) := by
    simpa using repeated_disjoint_norm_formula d a b c e hab hce hac hae hbc hbe
  have hvalues : ‖repeatedKernelVector d a b c e‖ ^ 2 = 8 ∨
      ‖repeatedKernelVector d a b c e‖ ^ 2 = 10 ∨
      ‖repeatedKernelVector d a b c e‖ ^ 2 = 12 := by
    rcases hcases with h | h | h
    · left; simpa [h] using hnorm
    · right; left; norm_num [h] at hnorm; exact hnorm
    · right; right; norm_num [h] at hnorm; exact hnorm
  have hnonzero : repeatedKernelVector d a b c e ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hvalues
    rcases hvalues with h | h | h <;> norm_num at h
  exact ⟨repeated_vector_in_starting_lattice d a b c e,
    repeated_label_kernel d a b c e hlabels, hnonzero, hvalues⟩

/-- In the shared-endpoint case, equal negative-edge labels force the
opposite endpoints to be nonadjacent and give squared norm six. -/
theorem repeated_shared_endpoint_short_kernel (d : OrdinaryData G) (a b e : V)
    (hab : G.Adj a b) (hae : G.Adj a e)
    (hnegab : d.discrepancy a b = -1)
    (hnegae : d.discrepancy a e = -1)
    (hbe : b ≠ e)
    (hlabels : labelVector d a b = labelVector d a e) :
    repeatedKernelVector d a b a e ∈ d.startingLattice ∧
      d.op d.ordinary (repeatedKernelVector d a b a e) = 0 ∧
      repeatedKernelVector d a b a e ≠ 0 ∧
      ‖repeatedKernelVector d a b a e‖ ^ 2 = 6 := by
  have hnbe : ¬G.Adj b e := by
    intro hbeadj
    have hea : d.discrepancy e a = -1 := by
      rw [d.discrepancy_symm e a]
      exact hnegae
    have hbalance := d.triangle_balance a b e hab hbeadj hae.symm
    have htwo : d.discrepancy b e = 2 := by omega
    exact (third_type_distinct_labels d a b e hbeadj htwo) hlabels
  have hk : repeatedKernelVector d a b a e =
      (1 / 3 : ℝ) • (d.point b - d.point e) := by
    unfold repeatedKernelVector
    module
  have hbb : inner ℝ (d.point b) (d.point b) = 28 := by
    rw [d.point_gram]
    simp [pointPair]
  have hee : inner ℝ (d.point e) (d.point e) = 28 := by
    rw [d.point_gram]
    simp [pointPair]
  have hbe' : inner ℝ (d.point b) (d.point e) = 1 := by
    rw [d.point_gram]
    simp [pointPair, hbe, hnbe]
  have heb' : inner ℝ (d.point e) (d.point b) = 1 := by
    rw [d.point_gram]
    simp [pointPair, hbe.symm, G.adj_comm, hnbe]
  have hp : inner ℝ (repeatedKernelVector d a b a e)
      (repeatedKernelVector d a b a e) = 6 := by
    rw [hk]
    simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      hbb, hee, hbe', heb', starRingEnd_apply, star_trivial]
    ring
  have hnorm : ‖repeatedKernelVector d a b a e‖ ^ 2 = 6 := by simpa using hp
  have hnonzero : repeatedKernelVector d a b a e ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  exact ⟨repeated_vector_in_starting_lattice d a b a e,
    repeated_label_kernel d a b a e hlabels, hnonzero, hnorm⟩

private theorem labelVector_comm (d : OrdinaryData G) (a b : V) :
    labelVector d a b = labelVector d b a := by
  simp [labelVector, add_comm]

/-- The full short-kernel conclusion for two distinct actual negative graph
edges with one operator-produced label, retaining the lattice bridge. -/
theorem repeated_distinct_negative_edges_short_kernel (d : OrdinaryData G)
    (a b c e : V) (hab : G.Adj a b) (hce : G.Adj c e)
    (hnegab : d.discrepancy a b = -1)
    (hnegce : d.discrepancy c e = -1)
    (hdistinct : ¬(a = c ∧ b = e) ∧ ¬(a = e ∧ b = c))
    (hlabels : labelVector d a b = labelVector d c e) :
    repeatedKernelVector d a b c e ∈ d.startingLattice ∧
      d.op d.ordinary (repeatedKernelVector d a b c e) = 0 ∧
      repeatedKernelVector d a b c e ≠ 0 ∧
      (‖repeatedKernelVector d a b c e‖ ^ 2 = 6 ∨
        ‖repeatedKernelVector d a b c e‖ ^ 2 = 8 ∨
        ‖repeatedKernelVector d a b c e‖ ^ 2 = 10 ∨
        ‖repeatedKernelVector d a b c e‖ ^ 2 = 12) := by
  by_cases hac : a = c
  · subst c
    have hbe : b ≠ e := by
      intro h
      exact hdistinct.1 ⟨rfl, h⟩
    obtain ⟨hL, hF, hNZ, hN⟩ :=
      repeated_shared_endpoint_short_kernel d a b e hab hce
        hnegab hnegce hbe hlabels
    exact ⟨hL, hF, hNZ, Or.inl hN⟩
  by_cases hae : a = e
  · subst e
    have hbc : b ≠ c := by
      intro h
      exact hdistinct.2 ⟨rfl, h⟩
    have hnegac : d.discrepancy a c = -1 := by
      rw [d.discrepancy_symm a c]
      exact hnegce
    have hl : labelVector d a b = labelVector d a c := by
      rw [labelVector_comm d a c]
      exact hlabels
    have hk : repeatedKernelVector d a b c a =
        repeatedKernelVector d a b a c := by
      unfold repeatedKernelVector
      module
    rw [hk]
    obtain ⟨hL, hF, hNZ, hN⟩ :=
      repeated_shared_endpoint_short_kernel d a b c hab hce.symm
        hnegab hnegac hbc hl
    exact ⟨hL, hF, hNZ, Or.inl hN⟩
  by_cases hbc : b = c
  · subst c
    have hae' : a ≠ e := by
      intro h
      exact hdistinct.2 ⟨h, rfl⟩
    have hnegba : d.discrepancy b a = -1 := by
      rw [d.discrepancy_symm b a]
      exact hnegab
    have hl : labelVector d b a = labelVector d b e := by
      rw [labelVector_comm d b a]
      exact hlabels
    have hk : repeatedKernelVector d a b b e =
        repeatedKernelVector d b a b e := by
      unfold repeatedKernelVector
      module
    rw [hk]
    obtain ⟨hL, hF, hNZ, hN⟩ :=
      repeated_shared_endpoint_short_kernel d b a e hab.symm hce
        hnegba hnegce hae' hl
    exact ⟨hL, hF, hNZ, Or.inl hN⟩
  by_cases hbe : b = e
  · subst e
    have hac' : a ≠ c := by
      intro h
      exact hdistinct.1 ⟨h, rfl⟩
    have hnegba : d.discrepancy b a = -1 := by
      rw [d.discrepancy_symm b a]
      exact hnegab
    have hnegbc : d.discrepancy b c = -1 := by
      rw [d.discrepancy_symm b c]
      exact hnegce
    have hl : labelVector d b a = labelVector d b c := by
      calc
        _ = labelVector d a b := labelVector_comm d b a
        _ = labelVector d c b := hlabels
        _ = labelVector d b c := (labelVector_comm d b c).symm
    have hk : repeatedKernelVector d a b c b =
        repeatedKernelVector d b a b c := by
      unfold repeatedKernelVector
      module
    rw [hk]
    obtain ⟨hL, hF, hNZ, hN⟩ :=
      repeated_shared_endpoint_short_kernel d b a c hab.symm hce.symm
        hnegba hnegbc hac' hl
    exact ⟨hL, hF, hNZ, Or.inl hN⟩
  obtain ⟨hL, hF, hNZ, hN⟩ :=
    repeated_disjoint_short_kernel d a b c e hab hce hnegab hnegce
      hac hae hbc hbe hlabels
  exact ⟨hL, hF, hNZ, Or.inr hN⟩

#print axioms Conway99Formal.OrdinaryEdgeLabels.triangle_types
#print axioms Conway99Formal.OrdinaryEdgeLabels.edge_pairing_values
#print axioms Conway99Formal.OrdinaryEdgeLabels.negative_edge_far
#print axioms Conway99Formal.OrdinaryEdgeLabels.edge_zero_at_near_vertex
#print axioms Conway99Formal.OrdinaryEdgeLabels.nearby_triangle_edges_zero
#print axioms Conway99Formal.OrdinaryEdgeLabels.nearby_triangle_span_isometry
#print axioms Conway99Formal.OrdinaryEdgeLabels.label_vector_in_starting_lattice
#print axioms Conway99Formal.OrdinaryEdgeLabels.repeated_vector_in_starting_lattice
#print axioms Conway99Formal.OrdinaryEdgeLabels.repeated_label_kernel
#print axioms Conway99Formal.OrdinaryEdgeLabels.third_type_distinct_labels
#print axioms Conway99Formal.OrdinaryEdgeLabels.cross_edge_count_le_two
#print axioms Conway99Formal.OrdinaryEdgeLabels.repeated_disjoint_norm_formula
#print axioms Conway99Formal.OrdinaryEdgeLabels.repeated_disjoint_short_kernel
#print axioms Conway99Formal.OrdinaryEdgeLabels.repeated_shared_endpoint_short_kernel
#print axioms Conway99Formal.OrdinaryEdgeLabels.repeated_distinct_negative_edges_short_kernel

end Conway99Formal.OrdinaryEdgeLabels

open Conway99Formal.OrdinaryEdgeLabels in
theorem solution
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (d : OrdinaryData G)
    (a b c e : V) (hab : G.Adj a b) (hce : G.Adj c e)
    (hnegab : d.discrepancy a b = -1)
    (hnegce : d.discrepancy c e = -1)
    (hdistinct : ¬(a = c ∧ b = e) ∧ ¬(a = e ∧ b = c))
    (hlabels : labelVector d a b = labelVector d c e) :
    repeatedKernelVector d a b c e ∈ d.startingLattice ∧
      d.op d.ordinary (repeatedKernelVector d a b c e) = 0 ∧
      repeatedKernelVector d a b c e ≠ 0 ∧
      (‖repeatedKernelVector d a b c e‖ ^ 2 = 6 ∨
        ‖repeatedKernelVector d a b c e‖ ^ 2 = 8 ∨
        ‖repeatedKernelVector d a b c e‖ ^ 2 = 10 ∨
        ‖repeatedKernelVector d a b c e‖ ^ 2 = 12) := by
  exact Conway99Formal.OrdinaryEdgeLabels.repeated_distinct_negative_edges_short_kernel d a b c e hab hce hnegab hnegce hdistinct hlabels

#print axioms solution
