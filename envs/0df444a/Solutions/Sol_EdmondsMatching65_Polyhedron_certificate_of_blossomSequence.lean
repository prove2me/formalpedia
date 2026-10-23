-- Prove2me | solution 1 for EdmondsMatching65.Polyhedron.certificate_of_blossomSequence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:04:16.795332+00:00
-- url     : https://prove2.me/submissions/3bf56c11-8741-44f5-9074-aa2444528601

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_DualProgram
import Definitions.Def_EdmondsMatching65_Polyhedron_BlossomSequence



namespace EdmondsMatching65.Polyhedron

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

set_option linter.unusedSectionVars false

lemma cb_ends_rep (G : Graph V E) (e : E) : ∃ a b : V, a ≠ b ∧ G.ends e = s(a, b) := by
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
  refine ⟨a, b, ?_, hab.symm⟩
  intro h
  apply G.loopless e
  rw [← hab, h]
  exact Sym2.mk_isDiag_iff.mpr rfl

lemma cb_mem_sym2 {S : Finset V} {a b : V} : s(a, b) ∈ S.sym2 ↔ a ∈ S ∧ b ∈ S := by
  rw [Finset.mk_mem_sym2_iff]

lemma cb_sym2_singleton (G : Graph V E) (e : E) (v : V) : G.ends e ∉ ({v} : Finset V).sym2 := by
  obtain ⟨a, b, hab, he⟩ := cb_ends_rep G e
  rw [he, cb_mem_sym2]
  simp only [Finset.mem_singleton]
  rintro ⟨rfl, rfl⟩
  exact hab rfl

lemma cb_succ_mod (N j : ℕ) (hj : j < N) :
    (j + 1) % N = j + 1 ∨ ((j + 1) % N = 0 ∧ j + 1 = N) := by
  rcases Nat.lt_or_ge (j + 1) N with h | h
  · left; exact Nat.mod_eq_of_lt h
  · right
    have h' : j + 1 = N := by omega
    exact ⟨by rw [h', Nat.mod_self], h'⟩

section Seq

variable {G : Graph V E} {c : E → ℝ} {M : Finset E} (s : BlossomSequence G c M)

/-- the union of the blossom blocks at level `i` -/
def BlossomSequence.U (i : ℕ) : Finset V := (Finset.range (2 * s.a i + 1)).biUnion (s.X i)

/-- the minimum node weight on the blossom `Bᵢ` -/
noncomputable def BlossomSequence.m (i : ℕ) : ℝ :=
  (Finset.range (2 * s.a i + 1)).inf' (by simp) (fun j => s.wN i (s.X i j))

/-- the drop of the weight at the shrunk node -/
noncomputable def BlossomSequence.δ (i : ℕ) : ℝ := s.m i - s.wN (i + 1) (s.U i)

/-- the edges of `M` inside a node set -/
def BlossomSequence.inside (Y : Finset V) : Finset E := M.filter (fun e => G.ends e ∈ Y.sym2)

lemma cb_mem_U {i : ℕ} {v : V} : v ∈ s.U i ↔ ∃ j < 2 * s.a i + 1, v ∈ s.X i j := by
  simp [BlossomSequence.U, Finset.mem_biUnion, Finset.mem_range]

lemma cb_X_subset_U {i j : ℕ} (hj : j < 2 * s.a i + 1) : s.X i j ⊆ s.U i := by
  intro v hv; exact (cb_mem_U s).mpr ⟨j, hj, hv⟩

lemma cb_δ_nonneg {i : ℕ} (hi : i < s.n) : 0 ≤ s.δ i := by
  have := s.wN_new_le i hi
  simp only [BlossomSequence.δ, BlossomSequence.m, BlossomSequence.U]
  linarith

lemma cb_m_le {i j : ℕ} (hj : j < 2 * s.a i + 1) : s.m i ≤ s.wN i (s.X i j) := by
  unfold BlossomSequence.m
  exact Finset.inf'_le _ (by simpa using hj)

lemma cb_a_pos {i : ℕ} (hi : i < s.n) : 1 ≤ s.a i := by
  by_contra h
  push_neg at h
  have ha : s.a i = 0 := by omega
  have h0 : 0 < 2 * s.a i + 1 := by omega
  have hj := s.f_joins i hi 0 h0
  have hc := s.f_edge i hi 0 h0
  rw [ha] at hj
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mod_self] at hj
  obtain ⟨a, ha', b, hb', hab⟩ := hj
  apply hc (s.X i 0) (s.X_mem i hi 0 h0)
  rw [hab, cb_mem_sym2]
  exact ⟨ha', hb'⟩

lemma cb_blocks_succ_mem {i : ℕ} (hi : i < s.n) {Y : Finset V} :
    Y ∈ s.blocks (i + 1) ↔ Y = s.U i ∨ (Y ∈ s.blocks i ∧ ∀ j < 2 * s.a i + 1, Y ≠ s.X i j) := by
  rw [s.blocks_succ i hi, Finset.mem_insert, Finset.mem_filter]
  rfl

lemma cb_U_mem {i : ℕ} (hi : i < s.n) : s.U i ∈ s.blocks (i + 1) :=
  (cb_blocks_succ_mem s hi).mpr (Or.inl rfl)

/-- partition invariant: disjointness and covering -/
lemma cb_partition : ∀ i ≤ s.n,
    (∀ Y ∈ s.blocks i, ∀ Z ∈ s.blocks i, Y ≠ Z → Disjoint Y Z) ∧
    (∀ v : V, ∃ Y ∈ s.blocks i, v ∈ Y) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [s.blocks_zero]
    constructor
    · intro Y hY Z hZ hYZ
      simp only [singletonBlocks, Finset.mem_image, Finset.mem_univ, true_and] at hY hZ
      obtain ⟨v, rfl⟩ := hY
      obtain ⟨w, rfl⟩ := hZ
      rw [Finset.disjoint_singleton]
      intro h; apply hYZ; rw [h]
    · intro v
      exact ⟨{v}, by simp [singletonBlocks], by simp⟩
  | succ i ih =>
    intro hi
    have hi' : i < s.n := by omega
    obtain ⟨ihd, ihc⟩ := ih (le_of_lt hi')
    constructor
    · intro Y hY Z hZ hYZ
      rw [cb_blocks_succ_mem s hi'] at hY hZ
      rcases hY with rfl | ⟨hY, hYX⟩ <;> rcases hZ with rfl | ⟨hZ, hZX⟩
      · exact absurd rfl hYZ
      · rw [BlossomSequence.U, Finset.disjoint_biUnion_left]
        intro j hj
        rw [Finset.mem_range] at hj
        exact ihd _ (s.X_mem i hi' j hj) _ hZ (fun h => hZX j hj h.symm)
      · rw [BlossomSequence.U, Finset.disjoint_biUnion_right]
        intro j hj
        rw [Finset.mem_range] at hj
        exact ihd _ hY _ (s.X_mem i hi' j hj) (fun h => hYX j hj h)
      · exact ihd Y hY Z hZ hYZ
    · intro v
      obtain ⟨Y, hY, hvY⟩ := ihc v
      by_cases h : ∃ j < 2 * s.a i + 1, Y = s.X i j
      · obtain ⟨j, hj, rfl⟩ := h
        exact ⟨s.U i, cb_U_mem s hi', (cb_mem_U s).mpr ⟨j, hj, hvY⟩⟩
      · push_neg at h
        exact ⟨Y, (cb_blocks_succ_mem s hi').mpr (Or.inr ⟨hY, h⟩), hvY⟩

lemma cb_block_eq {i : ℕ} (hi : i ≤ s.n) {Y Z : Finset V} (hY : Y ∈ s.blocks i)
    (hZ : Z ∈ s.blocks i) {v : V} (hvY : v ∈ Y) (hvZ : v ∈ Z) : Y = Z := by
  by_contra h
  exact Finset.disjoint_left.mp ((cb_partition s i hi).1 Y hY Z hZ h) hvY hvZ

lemma cb_cover {i : ℕ} (hi : i ≤ s.n) (v : V) : ∃ Y ∈ s.blocks i, v ∈ Y :=
  (cb_partition s i hi).2 v

lemma cb_X_ne {i : ℕ} (hi : i < s.n) {j j' : ℕ} (hj : j < 2 * s.a i + 1)
    (hj' : j' < 2 * s.a i + 1) (h : j ≠ j') : Disjoint (s.X i j) (s.X i j') :=
  (cb_partition s i (le_of_lt hi)).1 _ (s.X_mem i hi j hj) _ (s.X_mem i hi j' hj')
    (fun h' => h (s.X_injective i hi j hj j' hj' h'))

/-- a block of level `i` lies inside a block of level `k ≥ i` -/
lemma cb_coarser {i k : ℕ} (hik : i ≤ k) (hk : k ≤ s.n) :
    ∀ Y ∈ s.blocks i, ∃ Z ∈ s.blocks k, Y ⊆ Z := by
  induction k, hik using Nat.le_induction with
  | base => intro Y hY; exact ⟨Y, hY, subset_rfl⟩
  | succ k hik ih =>
    intro Y hY
    have hk' : k < s.n := by omega
    obtain ⟨Z, hZ, hYZ⟩ := ih (le_of_lt hk') Y hY
    by_cases h : ∃ j < 2 * s.a k + 1, Z = s.X k j
    · obtain ⟨j, hj, rfl⟩ := h
      exact ⟨s.U k, cb_U_mem s hk', hYZ.trans (cb_X_subset_U s hj)⟩
    · push_neg at h
      exact ⟨Z, (cb_blocks_succ_mem s hk').mpr (Or.inr ⟨hZ, h⟩), hYZ⟩

/-- two nodes of one block of level `i` are together in or out of every later blossom -/
lemma cb_lam {i k : ℕ} (hik : i ≤ k) (hk : k < s.n) {Z : Finset V} (hZ : Z ∈ s.blocks i)
    {a b : V} (ha : a ∈ Z) (hb : b ∈ Z) : a ∈ s.U k ↔ b ∈ s.U k := by
  obtain ⟨Z', hZ', hZZ'⟩ := cb_coarser s hik (le_of_lt hk) Z hZ
  have key : ∀ x y : V, x ∈ Z → y ∈ Z → x ∈ s.U k → y ∈ s.U k := by
    intro x y hx hy hxU
    obtain ⟨j, hj, hxj⟩ := (cb_mem_U s).mp hxU
    have := cb_block_eq s (le_of_lt hk) hZ' (s.X_mem k hk j hj) (hZZ' hx) hxj
    exact (cb_mem_U s).mpr ⟨j, hj, this ▸ hZZ' hy⟩
  exact ⟨key a b ha hb, key b a hb ha⟩

lemma cb_contracted_mono {i : ℕ} (hi : i < s.n) {e : E}
    (h : IsContractedEdge G (s.blocks (i + 1)) e) : IsContractedEdge G (s.blocks i) e := by
  intro Y hY
  obtain ⟨Z, hZ, hYZ⟩ := cb_coarser s (Nat.le_succ i) hi Y hY
  exact fun hm => h Z hZ (Finset.sym2_mono hYZ hm)

lemma cb_mat_eq : ∀ i ≤ s.n, s.mat i = M.filter (fun e => IsContractedEdge G (s.blocks i) e) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [s.mat_zero, s.blocks_zero]
    symm
    apply Finset.filter_true_of_mem
    intro e _ Y hY
    simp only [singletonBlocks, Finset.mem_image, Finset.mem_univ, true_and] at hY
    obtain ⟨v, rfl⟩ := hY
    exact cb_sym2_singleton G e v
  | succ i ih =>
    intro hi
    have hi' : i < s.n := by omega
    rw [s.mat_succ i hi', ih (le_of_lt hi'), Finset.filter_filter]
    apply Finset.filter_congr
    intro e _
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨cb_contracted_mono s hi' h, h⟩

lemma cb_mem_mat {i : ℕ} (hi : i ≤ s.n) {e : E} :
    e ∈ s.mat i ↔ e ∈ M ∧ IsContractedEdge G (s.blocks i) e := by
  rw [cb_mat_eq s i hi, Finset.mem_filter]

lemma cb_f_meets {i j : ℕ} (hi : i < s.n) (hj : j < 2 * s.a i + 1) :
    Meets G (s.f i j) (s.X i j) ∧ Meets G (s.f i j) (s.X i ((j + 1) % (2 * s.a i + 1))) := by
  obtain ⟨a, ha, b, hb, hab⟩ := s.f_joins i hi j hj
  exact ⟨⟨a, ha, by rw [hab]; simp⟩, ⟨b, hb, by rw [hab]; simp⟩⟩

lemma cb_succ_mod_lt {i j : ℕ} (hj : j < 2 * s.a i + 1) :
    (j + 1) % (2 * s.a i + 1) < 2 * s.a i + 1 := Nat.mod_lt _ (by omega)

/-- the blossom edges are pairwise distinct -/
lemma cb_f_inj {i : ℕ} (hi : i < s.n) {j j' : ℕ} (hj : j < 2 * s.a i + 1)
    (hj' : j' < 2 * s.a i + 1) (h : s.f i j = s.f i j') : j = j' := by
  have hN := cb_a_pos s hi
  obtain ⟨a, ha, b, hb, hab⟩ := s.f_joins i hi j hj
  obtain ⟨a', ha', b', hb', hab'⟩ := s.f_joins i hi j' hj'
  rw [h, hab'] at hab
  rw [Sym2.eq_iff] at hab
  have hs := cb_succ_mod (2 * s.a i + 1) j hj
  have hs' := cb_succ_mod (2 * s.a i + 1) j' hj'
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact s.X_injective i hi j hj j' hj'
      (cb_block_eq s (le_of_lt hi) (s.X_mem i hi j hj) (s.X_mem i hi j' hj') ha ha')
  · have h1 := s.X_injective i hi j hj _ (cb_succ_mod_lt s hj')
      (cb_block_eq s (le_of_lt hi) (s.X_mem i hi j hj) (s.X_mem i hi _ (cb_succ_mod_lt s hj'))
        ha hb')
    have h2 := s.X_injective i hi _ (cb_succ_mod_lt s hj) j' hj'
      (cb_block_eq s (le_of_lt hi) (s.X_mem i hi _ (cb_succ_mod_lt s hj)) (s.X_mem i hi j' hj')
        hb ha')
    omega

/-- an edge of `Mᵢ` joining two blossom nodes is a blossom edge (no chords) -/
lemma cb_no_chord {i : ℕ} (hi : i < s.n) {e : E} (he : e ∈ s.mat i) {p q : ℕ}
    (hp : p < 2 * s.a i + 1) (hq : q < 2 * s.a i + 1) (hpq : p ≠ q)
    (hep : Meets G e (s.X i p)) (heq : Meets G e (s.X i q)) :
    ∃ j < 2 * s.a i + 1, e = s.f i j := by
  by_contra hno
  push_neg at hno
  set N := 2 * s.a i + 1 with hN
  set J := (Finset.range N).filter (fun j => s.f i j ∈ s.mat i) with hJ
  have hJcard : J.card = s.a i := s.f_mat_card i hi
  set J' := J.image (fun j => (j + 1) % N) with hJ'
  have hJ'card : J'.card = s.a i := by
    rw [hJ', Finset.card_image_of_injOn, hJcard]
    intro x hx y hy hxy
    simp only [hJ, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx hy
    have := cb_succ_mod N x hx.1
    have := cb_succ_mod N y hy.1
    simp only at hxy
    omega
  -- pairwise disjointness
  have hmeet : ∀ j ∈ J, ∀ k < N, Meets G (s.f i j) (s.X i k) → k = j ∨ k = (j + 1) % N := by
    intro j hj k hk hm
    simp only [hJ, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨a, ha, b, hb, hab⟩ := s.f_joins i hi j hj.1
    obtain ⟨v, hvk, hv⟩ := hm
    rw [hab] at hv
    simp only [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · left
      exact s.X_injective i hi k hk j hj.1 (cb_block_eq s (le_of_lt hi) (s.X_mem i hi k hk)
        (s.X_mem i hi j hj.1) hvk ha)
    · right
      exact s.X_injective i hi k hk _ (cb_succ_mod_lt s hj.1) (cb_block_eq s (le_of_lt hi)
        (s.X_mem i hi k hk) (s.X_mem i hi _ (cb_succ_mod_lt s hj.1)) hvk hb)
  have hdisjJ : Disjoint J J' := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [hJ', Finset.mem_image] at hj'
    obtain ⟨j', hj'J, hjj'⟩ := hj'
    have hjm := hj; have hj'm := hj'J
    simp only [hJ, Finset.mem_filter, Finset.mem_range] at hjm hj'm
    by_cases hfe : s.f i j = s.f i j'
    · have := cb_f_inj s hi hjm.1 hj'm.1 hfe
      subst this
      have := cb_succ_mod N j hjm.1
      omega
    · apply s.mat_matching i (le_of_lt hi) _ hjm.2 _ hj'm.2 hfe _ (s.X_mem i hi j hjm.1)
      refine ⟨(cb_f_meets s hi hjm.1).1, ?_⟩
      rw [← hjj']
      exact (cb_f_meets s hi hj'm.1).2
  have hpJ : p ∉ J ∪ J' := by
    intro hpm
    have hef : ∀ j ∈ J, Meets G (s.f i j) (s.X i p) → False := by
      intro j hj hm
      have hjm := hj
      simp only [hJ, Finset.mem_filter, Finset.mem_range] at hjm
      exact s.mat_matching i (le_of_lt hi) _ he _ hjm.2 (hno j hjm.1) _ (s.X_mem i hi p hp)
        ⟨hep, hm⟩
    rw [Finset.mem_union] at hpm
    rcases hpm with hpm | hpm
    · exact hef p hpm (cb_f_meets s hi hp).1
    · simp only [hJ', Finset.mem_image] at hpm
      obtain ⟨j, hj, hjp⟩ := hpm
      have hjm := hj
      simp only [hJ, Finset.mem_filter, Finset.mem_range] at hjm
      apply hef j hj
      rw [← hjp]
      exact (cb_f_meets s hi hjm.1).2
  have hqJ : q ∉ J ∪ J' := by
    intro hqm
    have hef : ∀ j ∈ J, Meets G (s.f i j) (s.X i q) → False := by
      intro j hj hm
      have hjm := hj
      simp only [hJ, Finset.mem_filter, Finset.mem_range] at hjm
      exact s.mat_matching i (le_of_lt hi) _ he _ hjm.2 (hno j hjm.1) _ (s.X_mem i hi q hq)
        ⟨heq, hm⟩
    rw [Finset.mem_union] at hqm
    rcases hqm with hqm | hqm
    · exact hef q hqm (cb_f_meets s hi hq).1
    · simp only [hJ', Finset.mem_image] at hqm
      obtain ⟨j, hj, hjq⟩ := hqm
      have hjm := hj
      simp only [hJ, Finset.mem_filter, Finset.mem_range] at hjm
      apply hef j hj
      rw [← hjq]
      exact (cb_f_meets s hi hjm.1).2
  have hsub : (J ∪ J') ∪ {p, q} ⊆ Finset.range N := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]
    rcases hx with (hx | hx) | hx | hx
    · simp only [hJ, Finset.mem_filter, Finset.mem_range] at hx; exact hx.1
    · simp only [hJ', Finset.mem_image] at hx
      obtain ⟨j, _, rfl⟩ := hx
      exact Nat.mod_lt _ (by omega)
    · subst hx; exact hp
    · subst hx; exact hq
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint hdisjJ,
    hJcard, hJ'card, Finset.card_pair hpq] at hcard
  · omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · exact hpJ hx
    · exact hqJ hx

end Seq

/-- the edges of `M` with both ends in `Y` -/
def cbInside (G : Graph V E) (M : Finset E) (Y : Finset V) : Finset E :=
  M.filter (fun e => G.ends e ∈ Y.sym2)

lemma cb_mem_inside {G : Graph V E} {M : Finset E} {Y : Finset V} {e : E} :
    e ∈ cbInside G M Y ↔ e ∈ M ∧ G.ends e ∈ Y.sym2 := by
  rw [cbInside, Finset.mem_filter]

lemma cb_card_two (S : Finset V) (z : Sym2 V) (hz : ¬ z.IsDiag) (hS : z ∈ S.sym2) :
    (S.filter (fun v => v ∈ z)).card = 2 := by
  induction z using Sym2.ind with
  | h a b =>
    simp only [Sym2.mk_isDiag_iff] at hz
    rw [Finset.mk_mem_sym2_iff] at hS
    have : S.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext v; simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro (rfl | rfl)
        · exact ⟨hS.1, Or.inl rfl⟩
        · exact ⟨hS.2, Or.inr rfl⟩
    rw [this, Finset.card_pair hz]

/-- the nodes covered by the edges of `M` inside `Y` number twice those edges -/
lemma cb_card_cov {G : Graph V E} {M : Finset E} (hM : IsMatching G M) (Y : Finset V) :
    ((cbInside G M Y).biUnion (fun e => Y.filter (fun v => v ∈ G.ends e))).card
      = 2 * (cbInside G M Y).card := by
  rw [Finset.card_biUnion]
  · rw [Finset.sum_const_nat (m := 2)]
    · ring
    intro e he
    rw [cb_mem_inside] at he
    exact cb_card_two Y _ (G.loopless e) he.2
  · intro e he f hf hef
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    rw [Finset.mem_filter] at hv hv'
    rw [Finset.mem_coe, cb_mem_inside] at he hf
    exact hM e he.1 f hf.1 hef v hv.2 hv'.2

section Seq2

variable {G : Graph V E} {c : E → ℝ} {M : Finset E} (s : BlossomSequence G c M)

lemma cb_card_U {i : ℕ} (hi : i < s.n) :
    (s.U i).card = ∑ j ∈ Finset.range (2 * s.a i + 1), (s.X i j).card := by
  rw [BlossomSequence.U, Finset.card_biUnion]
  intro j hj j' hj' hjj'
  rw [Finset.mem_coe, Finset.mem_range] at hj hj'
  rw [Function.onFun]
  exact cb_X_ne s hi hj hj' hjj'

/-- the edges of `M` inside the blossom union: those inside one blossom node, plus the
blossom edges of `Mᵢ` -/
lemma cb_inside_U (hM : IsMatching G M) {i : ℕ} (hi : i < s.n) :
    (cbInside G M (s.U i)).card =
      ∑ j ∈ Finset.range (2 * s.a i + 1), (cbInside G M (s.X i j)).card + s.a i := by
  set N := 2 * s.a i + 1 with hN
  set A := (Finset.range N).biUnion (fun j => cbInside G M (s.X i j)) with hA
  set B := ((Finset.range N).filter (fun j => s.f i j ∈ s.mat i)).image (s.f i) with hB
  have hAcard : A.card = ∑ j ∈ Finset.range N, (cbInside G M (s.X i j)).card := by
    rw [hA, Finset.card_biUnion]
    intro j hj j' hj' hjj'
    rw [Finset.mem_coe, Finset.mem_range] at hj hj'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    rw [cb_mem_inside] at he he'
    obtain ⟨a, b, -, hab⟩ := cb_ends_rep G e
    rw [hab, cb_mem_sym2] at he he'
    exact Finset.disjoint_left.mp (cb_X_ne s hi hj hj' hjj') he.2.1 he'.2.1
  have hBcard : B.card = s.a i := by
    rw [hB, Finset.card_image_of_injOn, s.f_mat_card i hi]
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx hy
    exact cb_f_inj s hi hx.1 hy.1 hxy
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    rw [hA, Finset.mem_biUnion] at heA
    rw [hB, Finset.mem_image] at heB
    obtain ⟨j, hj, hej⟩ := heA
    obtain ⟨j', hj', rfl⟩ := heB
    rw [Finset.mem_range] at hj
    rw [Finset.mem_filter, Finset.mem_range] at hj'
    rw [cb_mem_inside] at hej
    exact s.f_edge i hi j' hj'.1 _ (s.X_mem i hi j hj) hej.2
  have hset : cbInside G M (s.U i) = A ∪ B := by
    ext e
    rw [Finset.mem_union, cb_mem_inside]
    constructor
    · rintro ⟨heM, heU⟩
      obtain ⟨a, b, hab, he⟩ := cb_ends_rep G e
      rw [he, cb_mem_sym2] at heU
      obtain ⟨p, hp, hap⟩ := (cb_mem_U s).mp heU.1
      obtain ⟨q, hq, hbq⟩ := (cb_mem_U s).mp heU.2
      by_cases hpq : p = q
      · left
        subst hpq
        rw [hA, Finset.mem_biUnion]
        exact ⟨p, Finset.mem_range.mpr hp, cb_mem_inside.mpr ⟨heM, by rw [he, cb_mem_sym2]; exact ⟨hap, hbq⟩⟩⟩
      · right
        have hcontr : IsContractedEdge G (s.blocks i) e := by
          intro Z hZ hZe
          rw [he, cb_mem_sym2] at hZe
          have h1 := cb_block_eq s (le_of_lt hi) hZ (s.X_mem i hi p hp) hZe.1 hap
          have h2 := cb_block_eq s (le_of_lt hi) hZ (s.X_mem i hi q hq) hZe.2 hbq
          exact hpq (s.X_injective i hi p hp q hq (h1.symm.trans h2))
        have hemat : e ∈ s.mat i := (cb_mem_mat s (le_of_lt hi)).mpr ⟨heM, hcontr⟩
        obtain ⟨j, hj, rfl⟩ := cb_no_chord s hi hemat hp hq hpq ⟨a, hap, by rw [he]; simp⟩
          ⟨b, hbq, by rw [he]; simp⟩
        rw [hB, Finset.mem_image]
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hemat⟩, rfl⟩
    · rintro (heA | heB)
      · rw [hA, Finset.mem_biUnion] at heA
        obtain ⟨j, hj, hej⟩ := heA
        rw [Finset.mem_range] at hj
        rw [cb_mem_inside] at hej
        exact ⟨hej.1, Finset.sym2_mono (cb_X_subset_U s hj) hej.2⟩
      · rw [hB, Finset.mem_image] at heB
        obtain ⟨j, hj, rfl⟩ := heB
        rw [Finset.mem_filter, Finset.mem_range] at hj
        refine ⟨((cb_mem_mat s (le_of_lt hi)).mp hj.2).1, ?_⟩
        obtain ⟨a, ha, b, hb, hab⟩ := s.f_joins i hi j hj.1
        rw [hab, cb_mem_sym2]
        exact ⟨cb_X_subset_U s hj.1 ha, cb_X_subset_U s (cb_succ_mod_lt s hj.1) hb⟩
  rw [hset, Finset.card_union_of_disjoint hdisj, hAcard, hBcard]

/-- every block has an odd number of nodes, all but one covered by the edges of `M` inside -/
lemma cb_count (hM : IsMatching G M) : ∀ i ≤ s.n, ∀ Y ∈ s.blocks i,
    Y.card = 2 * (cbInside G M Y).card + 1 := by
  intro i
  induction i with
  | zero =>
    intro _ Y hY
    rw [s.blocks_zero] at hY
    simp only [singletonBlocks, Finset.mem_image, Finset.mem_univ, true_and] at hY
    obtain ⟨v, rfl⟩ := hY
    have : cbInside G M {v} = ∅ := by
      ext e
      rw [cb_mem_inside]
      simp only [Finset.notMem_empty, iff_false]
      exact fun h => cb_sym2_singleton G e v h.2
    rw [this]; simp
  | succ i ih =>
    intro hi Y hY
    have hi' : i < s.n := by omega
    rw [cb_blocks_succ_mem s hi'] at hY
    rcases hY with rfl | ⟨hY, -⟩
    · rw [cb_card_U s hi', cb_inside_U s hM hi']
      rw [Finset.sum_congr rfl (fun j hj => ih (le_of_lt hi') (s.X i j)
        (s.X_mem i hi' j (Finset.mem_range.mp hj)))]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
      simp only [smul_eq_mul, mul_one]
      ring
    · exact ih (le_of_lt hi') Y hY

/-- a block containing a node not covered by `M` meets no edge of `Mᵢ` -/
lemma cb_exposed (hM : IsMatching G M) {i : ℕ} (hi : i ≤ s.n) {Y : Finset V}
    (hY : Y ∈ s.blocks i) {a : V} (ha : a ∈ Y) (hun : ∀ e ∈ M, a ∉ G.ends e) :
    ∀ e ∈ s.mat i, ¬ Meets G e Y := by
  intro e he ⟨a', ha'Y, ha'e⟩
  rw [cb_mem_mat s hi] at he
  have hne : a ≠ a' := fun h => hun e he.1 (h ▸ ha'e)
  set cov := (cbInside G M Y).biUnion (fun e => Y.filter (fun v => v ∈ G.ends e)) with hcovdef
  have hcov : cov.card = 2 * (cbInside G M Y).card := cb_card_cov hM Y
  have hcount := cb_count s hM i hi Y hY
  have hsub : cov ⊆ Y := by
    intro v hv
    rw [hcovdef, Finset.mem_biUnion] at hv
    obtain ⟨e, _, hv⟩ := hv
    exact (Finset.mem_filter.mp hv).1
  have hacov : a ∉ cov := by
    intro h
    rw [hcovdef, Finset.mem_biUnion] at h
    obtain ⟨f, hf, hv⟩ := h
    rw [Finset.mem_filter] at hv
    rw [cb_mem_inside] at hf
    exact hun f hf.1 hv.2
  have ha'cov : a' ∉ cov := by
    intro h
    rw [hcovdef, Finset.mem_biUnion] at h
    obtain ⟨f, hf, hv⟩ := h
    rw [Finset.mem_filter] at hv
    rw [cb_mem_inside] at hf
    have hfe : f ≠ e := by
      rintro rfl
      exact he.2 Y hY hf.2
    exact hM f hf.1 e he.1 hfe a' hv.2 ha'e
  have hpair : ({a, a'} : Finset V) ⊆ Y \ cov := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rw [Finset.mem_sdiff]
    rcases hv with rfl | rfl
    · exact ⟨ha, hacov⟩
    · exact ⟨ha'Y, ha'cov⟩
  have h2 := Finset.card_le_card hpair
  rw [Finset.card_pair hne, Finset.card_sdiff_of_subset hsub, hcov, hcount] at h2
  omega

lemma cb_U_card_ge {i : ℕ} (hi : i < s.n) : 3 ≤ (s.U i).card := by
  rw [cb_card_U s hi]
  have hN := cb_a_pos s hi
  have : ∀ j ∈ Finset.range (2 * s.a i + 1), 1 ≤ (s.X i j).card := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨a, ha, -, -, -⟩ := s.f_joins i hi j hj
    exact Finset.card_pos.mpr ⟨a, ha⟩
  calc 3 ≤ ∑ _j ∈ Finset.range (2 * s.a i + 1), 1 := by simp; omega
    _ ≤ _ := Finset.sum_le_sum this

lemma cb_U_odd (hM : IsMatching G M) {i : ℕ} (hi : i < s.n) : s.U i ∈ oddSets := by
  have h1 := cb_count s hM (i + 1) hi (s.U i) (cb_U_mem s hi)
  have h2 := cb_U_card_ge s hi
  classical
  unfold oddSets
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (cbInside G M (s.U i)).card, by omega, h1⟩

end Seq2

section Seq3

variable {G : Graph V E} {c : E → ℝ} {M : Finset E} (s : BlossomSequence G c M)

lemma cb_new_block {i : ℕ} (hi : i < s.n) {a : V} (haU : a ∈ s.U i) {Y' : Finset V}
    (hY' : Y' ∈ s.blocks (i + 1)) (ha' : a ∈ Y') : Y' = s.U i :=
  cb_block_eq s hi hY' (cb_U_mem s hi) ha' haU

lemma cb_old_block {i : ℕ} (hi : i < s.n) {a : V} (haU : a ∉ s.U i) {Y Y' : Finset V}
    (hY : Y ∈ s.blocks i) (hY' : Y' ∈ s.blocks (i + 1)) (ha : a ∈ Y) (ha' : a ∈ Y') : Y' = Y := by
  rw [cb_blocks_succ_mem s hi] at hY'
  rcases hY' with rfl | ⟨hY'b, -⟩
  · exact absurd ha' haU
  · exact cb_block_eq s (le_of_lt hi) hY'b hY ha' ha

/-- the dual node variables -/
noncomputable def BlossomSequence.yD (a : V) : ℝ :=
  s.wN 0 {a} - ∑ k ∈ Finset.range s.n, if a ∈ s.U k then s.δ k else 0

/-- the dual odd-set variables -/
noncomputable def BlossomSequence.zD (S : Finset V) : ℝ :=
  ∑ k ∈ Finset.range s.n, if s.U k = S then 2 * s.δ k else 0

/-- the partial node value at level `i` -/
noncomputable def BlossomSequence.h (i : ℕ) (Y : Finset V) (a : V) : ℝ :=
  s.wN i Y - ∑ k ∈ Finset.Ico i s.n, if a ∈ s.U k then s.δ k else 0

lemma cb_h (hM : IsMatching G M) : ∀ d i, i + d = s.n → ∀ Y ∈ s.blocks i, ∀ a ∈ Y,
    0 ≤ s.h i Y a ∧ ((∀ e ∈ M, a ∉ G.ends e) → s.h i Y a = 0) := by
  intro d
  induction d with
  | zero =>
    intro i hi Y hY a ha
    have hin : i = s.n := by omega
    subst hin
    simp only [BlossomSequence.h, Finset.Ico_self, Finset.sum_empty, sub_zero]
    exact ⟨s.wN_nonneg _ le_rfl Y hY,
      fun hun => s.exposed_zero Y hY (cb_exposed s hM le_rfl hY ha hun)⟩
  | succ d ih =>
    intro i hi Y hY a ha
    have hi' : i < s.n := by omega
    obtain ⟨Y', hY', haY'⟩ := cb_cover s (by omega : i + 1 ≤ s.n) a
    have ih' := ih (i + 1) (by omega) Y' hY' a haY'
    have hsplit : s.h i Y a = s.wN i Y - (if a ∈ s.U i then s.δ i else 0) -
        ∑ k ∈ Finset.Ico (i + 1) s.n, (if a ∈ s.U k then s.δ k else 0) := by
      rw [BlossomSequence.h, Finset.sum_eq_sum_Ico_succ_bot hi']; ring
    unfold BlossomSequence.h at ih'
    by_cases haU : a ∈ s.U i
    · obtain ⟨j, hj, haj⟩ := (cb_mem_U s).mp haU
      have hYj : Y = s.X i j := cb_block_eq s (le_of_lt hi') hY (s.X_mem i hi' j hj) ha haj
      have hY'U : Y' = s.U i := cb_new_block s hi' haU hY' haY'
      rw [hsplit, if_pos haU]
      rw [hY'U] at ih'
      have hm := cb_m_le s hj
      have hδ : s.δ i = s.m i - s.wN (i + 1) (s.U i) := rfl
      refine ⟨by rw [hYj]; linarith [ih'.1], fun hun => ?_⟩
      have hexp := cb_exposed s hM (le_of_lt hi') hY ha hun
      rw [hYj] at hexp
      have hmin : s.wN i (s.X i j) ≤ s.m i := by
        unfold BlossomSequence.m
        apply Finset.le_inf'
        intro j' hj'
        exact s.exposed_min i hi' j hj hexp j' (Finset.mem_range.mp hj')
      have := ih'.2 hun
      rw [hYj]; linarith
    · have hY'Y : Y' = Y := cb_old_block s hi' haU hY hY' ha haY'
      have hw : s.wN (i + 1) Y = s.wN i Y :=
        s.wN_succ i hi' Y (by rw [← hY'Y]; exact hY') (fun h => haU (by unfold BlossomSequence.U; rw [← h]; exact ha))
      rw [hsplit, if_neg haU, sub_zero, ← hw]
      rw [hY'Y] at ih'
      exact ih'

lemma cb_singleton_mem (a : V) : ({a} : Finset V) ∈ s.blocks 0 := by
  rw [s.blocks_zero]; simp [singletonBlocks]

lemma cb_y_eq (a : V) : s.yD a = s.h 0 {a} a := by
  simp only [BlossomSequence.yD, BlossomSequence.h, Finset.range_eq_Ico]

lemma cb_y_nonneg (hM : IsMatching G M) (a : V) : 0 ≤ s.yD a := by
  rw [cb_y_eq]
  exact (cb_h s hM s.n 0 (by simp) {a} (cb_singleton_mem s a) a (by simp)).1

lemma cb_y_zero (hM : IsMatching G M) (a : V) (hun : ∀ e ∈ M, a ∉ G.ends e) : s.yD a = 0 := by
  rw [cb_y_eq]
  exact (cb_h s hM s.n 0 (by simp) {a} (cb_singleton_mem s a) a (by simp)).2 hun

lemma cb_z_nonneg (S : Finset V) : 0 ≤ s.zD S := by
  unfold BlossomSequence.zD
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · linarith [cb_δ_nonneg s (Finset.mem_range.mp hk)]
  · exact le_rfl

/-- indicator of membership in the blossom union -/
noncomputable def BlossomSequence.ind (a : V) (k : ℕ) : ℝ := if a ∈ s.U k then 1 else 0

/-- the reduced slack of an edge at level `i` -/
noncomputable def BlossomSequence.R (i : ℕ) (e : E) (a b : V) (Y1 Y2 : Finset V) : ℝ :=
  s.wN i Y1 + s.wN i Y2 - s.wE i e -
    ∑ k ∈ Finset.Ico i s.n, (s.ind a k + s.ind b k - 2 * (s.ind a k * s.ind b k)) * s.δ k

lemma cb_R_step {i : ℕ} (hi : i < s.n) {e : E} {a b : V} (hab : G.ends e = s(a, b))
    (hc : IsContractedEdge G (s.blocks (i + 1)) e)
    {Y1 Y2 : Finset V} (hY1 : Y1 ∈ s.blocks i) (hY2 : Y2 ∈ s.blocks i) (ha : a ∈ Y1) (hb : b ∈ Y2)
    {Y1' Y2' : Finset V} (hY1' : Y1' ∈ s.blocks (i + 1)) (hY2' : Y2' ∈ s.blocks (i + 1))
    (ha' : a ∈ Y1') (hb' : b ∈ Y2') :
    s.R i e a b Y1 Y2 = s.R (i + 1) e a b Y1' Y2' := by
  unfold BlossomSequence.R
  rw [Finset.sum_eq_sum_Ico_succ_bot hi]
  have hnot : ¬ (a ∈ s.U i ∧ b ∈ s.U i) := by
    rintro ⟨haU, hbU⟩
    apply hc (s.U i) (cb_U_mem s hi)
    rw [hab, cb_mem_sym2]
    exact ⟨haU, hbU⟩
  have hδ : s.δ i = s.m i - s.wN (i + 1) (s.U i) := rfl
  by_cases haU : a ∈ s.U i
  · have hbU : b ∉ s.U i := fun h => hnot ⟨haU, h⟩
    obtain ⟨j, hj, haj⟩ := (cb_mem_U s).mp haU
    have hY1j : Y1 = s.X i j := cb_block_eq s (le_of_lt hi) hY1 (s.X_mem i hi j hj) ha haj
    have hY1'U : Y1' = s.U i := cb_new_block s hi haU hY1' ha'
    have hY2'2 : Y2' = Y2 := cb_old_block s hi hbU hY2 hY2' hb hb'
    have hw2 : s.wN (i + 1) Y2 = s.wN i Y2 :=
      s.wN_succ i hi Y2 (by rw [← hY2'2]; exact hY2') (fun h => hbU (by unfold BlossomSequence.U; rw [← h]; exact hb))
    have hwe : s.wE (i + 1) e = s.wE i e - s.wN i (s.X i j) + s.m i := by
      have := s.wE_new i hi e hc j hj ⟨a, haj, by rw [hab]; simp⟩
      rw [this]; rfl
    simp only [BlossomSequence.ind, if_pos haU, if_neg hbU]
    rw [hY1j, hY1'U, hY2'2, hw2, hwe]
    linarith
  · by_cases hbU : b ∈ s.U i
    · obtain ⟨j, hj, hbj⟩ := (cb_mem_U s).mp hbU
      have hY2j : Y2 = s.X i j := cb_block_eq s (le_of_lt hi) hY2 (s.X_mem i hi j hj) hb hbj
      have hY2'U : Y2' = s.U i := cb_new_block s hi hbU hY2' hb'
      have hY1'1 : Y1' = Y1 := cb_old_block s hi haU hY1 hY1' ha ha'
      have hw1 : s.wN (i + 1) Y1 = s.wN i Y1 :=
        s.wN_succ i hi Y1 (by rw [← hY1'1]; exact hY1') (fun h => haU (by unfold BlossomSequence.U; rw [← h]; exact ha))
      have hwe : s.wE (i + 1) e = s.wE i e - s.wN i (s.X i j) + s.m i := by
        have := s.wE_new i hi e hc j hj ⟨b, hbj, by rw [hab]; simp⟩
        rw [this]; rfl
      simp only [BlossomSequence.ind, if_pos hbU, if_neg haU]
      rw [hY2j, hY2'U, hY1'1, hw1, hwe]
      linarith
    · have hY1'1 : Y1' = Y1 := cb_old_block s hi haU hY1 hY1' ha ha'
      have hY2'2 : Y2' = Y2 := cb_old_block s hi hbU hY2 hY2' hb hb'
      have hw1 : s.wN (i + 1) Y1 = s.wN i Y1 :=
        s.wN_succ i hi Y1 (by rw [← hY1'1]; exact hY1') (fun h => haU (by unfold BlossomSequence.U; rw [← h]; exact ha))
      have hw2 : s.wN (i + 1) Y2 = s.wN i Y2 :=
        s.wN_succ i hi Y2 (by rw [← hY2'2]; exact hY2') (fun h => hbU (by unfold BlossomSequence.U; rw [← h]; exact hb))
      have hwe : s.wE (i + 1) e = s.wE i e := by
        apply s.wE_succ i hi e hc
        rintro ⟨v, hvU, hv⟩
        rw [hab] at hv
        simp only [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · exact haU hvU
        · exact hbU hvU
      simp only [BlossomSequence.ind, if_neg haU, if_neg hbU]
      rw [hY1'1, hY2'2, hw1, hw2, hwe]
      ring

lemma cb_contracted_zero (e : E) : IsContractedEdge G (s.blocks 0) e := by
  intro Y hY
  rw [s.blocks_zero] at hY
  simp only [singletonBlocks, Finset.mem_image, Finset.mem_univ, true_and] at hY
  obtain ⟨v, rfl⟩ := hY
  exact cb_sym2_singleton G e v

lemma cb_R_main (hM : IsMatching G M) : ∀ d i, i + d = s.n → ∀ (e : E) (a b : V),
    G.ends e = s(a, b) → IsContractedEdge G (s.blocks i) e →
    ∀ Y1 ∈ s.blocks i, ∀ Y2 ∈ s.blocks i, a ∈ Y1 → b ∈ Y2 →
    0 ≤ s.R i e a b Y1 Y2 ∧ (e ∈ M → s.R i e a b Y1 Y2 = 0) := by
  intro d
  induction d with
  | zero =>
    intro i hi e a b hab hc Y1 hY1 Y2 hY2 ha hb
    have hin : i = s.n := by omega
    subst hin
    simp only [BlossomSequence.R, Finset.Ico_self, Finset.sum_empty, sub_zero]
    have hjoin : Joins G e Y1 Y2 := ⟨a, ha, b, hb, hab⟩
    constructor
    · linarith [s.edge_le _ le_rfl e hc Y1 hY1 Y2 hY2 hjoin]
    · intro heM
      have := s.mat_tight e ((cb_mem_mat s le_rfl).mpr ⟨heM, hc⟩) Y1 hY1 Y2 hY2 hjoin
      linarith
  | succ d ih =>
    intro i hi e a b hab hc Y1 hY1 Y2 hY2 ha hb
    have hi' : i < s.n := by omega
    by_cases hc' : IsContractedEdge G (s.blocks (i + 1)) e
    · obtain ⟨Y1', hY1', ha'⟩ := cb_cover s (by omega : i + 1 ≤ s.n) a
      obtain ⟨Y2', hY2', hb'⟩ := cb_cover s (by omega : i + 1 ≤ s.n) b
      rw [cb_R_step s hi' hab hc' hY1 hY2 ha hb hY1' hY2' ha' hb']
      exact ih (i + 1) (by omega) e a b hab hc' Y1' hY1' Y2' hY2' ha' hb'
    · unfold IsContractedEdge at hc'
      push_neg at hc'
      obtain ⟨Z, hZ, hZe⟩ := hc'
      rw [hab, cb_mem_sym2] at hZe
      have hZU : Z = s.U i := by
        rw [cb_blocks_succ_mem s hi'] at hZ
        rcases hZ with rfl | ⟨hZb, -⟩
        · rfl
        · exfalso
          apply hc Z hZb
          rw [hab, cb_mem_sym2]
          exact hZe
      rw [hZU] at hZe
      obtain ⟨p, hp, hap⟩ := (cb_mem_U s).mp hZe.1
      obtain ⟨q, hq, hbq⟩ := (cb_mem_U s).mp hZe.2
      have hY1p : Y1 = s.X i p := cb_block_eq s (le_of_lt hi') hY1 (s.X_mem i hi' p hp) ha hap
      have hY2q : Y2 = s.X i q := cb_block_eq s (le_of_lt hi') hY2 (s.X_mem i hi' q hq) hb hbq
      have hpq : p ≠ q := by
        intro hpq'
        subst hpq'
        apply hc Y1 hY1
        rw [hab, cb_mem_sym2]
        refine ⟨ha, ?_⟩
        rw [hY1p, ← hY2q]
        exact hb
      have hsum : ∑ k ∈ Finset.Ico i s.n,
          (s.ind a k + s.ind b k - 2 * (s.ind a k * s.ind b k)) * s.δ k = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_Ico] at hk
        have hiff : a ∈ s.U k ↔ b ∈ s.U k := by
          rcases eq_or_lt_of_le hk.1 with rfl | hlt
          · exact ⟨fun _ => hZe.2, fun _ => hZe.1⟩
          · exact cb_lam s hlt hk.2 (cb_U_mem s hi') hZe.1 hZe.2
        unfold BlossomSequence.ind
        by_cases haU : a ∈ s.U k
        · have hbU : b ∈ s.U k := hiff.mp haU
          rw [if_pos haU, if_pos hbU]; ring
        · have hbU : b ∉ s.U k := fun h => haU (hiff.mpr h)
          rw [if_neg haU, if_neg hbU]; ring
      unfold BlossomSequence.R
      rw [hsum, sub_zero]
      have hjoin : Joins G e Y1 Y2 := ⟨a, ha, b, hb, hab⟩
      constructor
      · linarith [s.edge_le i (le_of_lt hi') e hc Y1 hY1 Y2 hY2 hjoin]
      · intro heM
        have hemat : e ∈ s.mat i := (cb_mem_mat s (le_of_lt hi')).mpr ⟨heM, hc⟩
        obtain ⟨j, hj, hej⟩ := cb_no_chord s hi' hemat hp hq hpq ⟨a, hap, by rw [hab]; simp⟩
          ⟨b, hbq, by rw [hab]; simp⟩
        have htight := s.blossom_tight i hi' j hj
        obtain ⟨a', ha', b', hb', hab'⟩ := s.f_joins i hi' j hj
        rw [← hej] at htight hab'
        rw [hab, Sym2.eq_iff] at hab'
        rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have h1 := cb_block_eq s (le_of_lt hi') hY1 (s.X_mem i hi' j hj) ha ha'
          have h2 := cb_block_eq s (le_of_lt hi') hY2 (s.X_mem i hi' _ (cb_succ_mod_lt s hj)) hb hb'
          rw [h1, h2]; linarith
        · have h1 := cb_block_eq s (le_of_lt hi') hY1 (s.X_mem i hi' _ (cb_succ_mod_lt s hj)) ha hb'
          have h2 := cb_block_eq s (le_of_lt hi') hY2 (s.X_mem i hi' j hj) hb ha'
          rw [h1, h2]; linarith

lemma cb_z_sum (F : Finset (Finset V)) :
    ∑ S ∈ F, s.zD S = ∑ k ∈ Finset.range s.n, if s.U k ∈ F then 2 * s.δ k else 0 := by
  unfold BlossomSequence.zD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_ite_eq]

lemma cb_L (hM : IsMatching G M) (e : E) (a b : V) (hab : G.ends e = s(a, b)) :
    edgeDual G s.yD s.zD e - c e = s.R 0 e a b {a} {b} := by
  unfold edgeDual
  rw [hab, Sym2.lift_mk, cb_z_sum]
  simp only [BlossomSequence.R, BlossomSequence.yD, s.wE_zero, Finset.range_eq_Ico]
  have hF : ∀ k ∈ Finset.Ico 0 s.n,
      (if s.U k ∈ oddSets.filter (fun S : Finset V => s(a, b) ∈ S.sym2) then 2 * s.δ k else 0)
        = if a ∈ s.U k ∧ b ∈ s.U k then 2 * s.δ k else 0 := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hodd := cb_U_odd s hM hk.2
    by_cases h : a ∈ s.U k ∧ b ∈ s.U k
    · rw [if_pos h, if_pos]
      rw [Finset.mem_filter, cb_mem_sym2]
      exact ⟨hodd, h⟩
    · rw [if_neg h, if_neg]
      rw [Finset.mem_filter, cb_mem_sym2]
      exact fun h' => h h'.2
  rw [Finset.sum_congr rfl hF]
  have hT : ∑ k ∈ Finset.Ico 0 s.n,
      (s.ind a k + s.ind b k - 2 * (s.ind a k * s.ind b k)) * s.δ k =
      ∑ k ∈ Finset.Ico 0 s.n, (if a ∈ s.U k then s.δ k else 0) +
      ∑ k ∈ Finset.Ico 0 s.n, (if b ∈ s.U k then s.δ k else 0) -
      ∑ k ∈ Finset.Ico 0 s.n, (if a ∈ s.U k ∧ b ∈ s.U k then 2 * s.δ k else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    unfold BlossomSequence.ind
    by_cases haU : a ∈ s.U k <;> by_cases hbU : b ∈ s.U k
    · rw [if_pos haU, if_pos hbU, if_pos haU, if_pos hbU, if_pos ⟨haU, hbU⟩]; ring
    · rw [if_pos haU, if_neg hbU, if_pos haU, if_neg hbU, if_neg (fun h => hbU h.2)]; ring
    · rw [if_neg haU, if_pos hbU, if_neg haU, if_pos hbU, if_neg (fun h => haU h.1)]; ring
    · rw [if_neg haU, if_neg hbU, if_neg haU, if_neg hbU, if_neg (fun h => haU h.1)]; ring
  rw [hT]
  ring

theorem cert_core (G : Graph V E) (c : E → ℝ) (M : Finset E)
    (hM : IsMatching G M) (s : BlossomSequence G c M) :
    ∃ (y : V → ℝ) (z : Finset V → ℝ), DualFeasible G c y z ∧ CompSlack G c M y z := by
  refine ⟨s.yD, s.zD, ⟨cb_y_nonneg s hM, fun S _ => cb_z_nonneg s S, ?_⟩,
    ⟨fun v hv => cb_y_zero s hM v hv, ?_, ?_⟩⟩
  · intro e
    obtain ⟨a, b, -, hab⟩ := cb_ends_rep G e
    have h1 := cb_L s hM e a b hab
    have h2 := (cb_R_main s hM s.n 0 (by simp) e a b hab (cb_contracted_zero s e)
      {a} (cb_singleton_mem s a) {b} (cb_singleton_mem s b) (by simp) (by simp)).1
    linarith
  · intro e heM
    obtain ⟨a, b, -, hab⟩ := cb_ends_rep G e
    have h1 := cb_L s hM e a b hab
    have h2 := (cb_R_main s hM s.n 0 (by simp) e a b hab (cb_contracted_zero s e)
      {a} (cb_singleton_mem s a) {b} (cb_singleton_mem s b) (by simp) (by simp)).2 heM
    linarith
  · intro S _ hS
    have hex : ∃ k ∈ Finset.range s.n, s.U k = S := by
      by_contra hno
      push_neg at hno
      have : s.zD S = 0 := by
        unfold BlossomSequence.zD
        apply Finset.sum_eq_zero
        intro k hk
        rw [if_neg (hno k hk)]
      linarith
    obtain ⟨k, hk, rfl⟩ := hex
    rw [Finset.mem_range] at hk
    have hcount := cb_count s hM (k + 1) hk (s.U k) (cb_U_mem s hk)
    unfold rOf
    rw [hcount]
    unfold cbInside
    push_cast
    ring

end Seq3

end EdmondsMatching65.Polyhedron

open EdmondsMatching65.Polyhedron


theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (c : E → ℝ) (M : Finset E)
    (hM : IsMatching G M) (s : BlossomSequence G c M) :
    ∃ (y : V → ℝ) (z : Finset V → ℝ), DualFeasible G c y z ∧ CompSlack G c M y z := by
  exact cert_core G c M hM s
