-- Prove2me | solution 1 for BoundedDegreeST.PlusOne.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:47:33.263364+00:00
-- url     : https://prove2.me/submissions/56198aef-2dcb-4ef1-9a0f-7542cbb68f86

import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm



namespace BoundedDegreeST.PlusOne

open Finset

section
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false

lemma mem_internal' {E : Finset (Sym2 V)} {S : Finset V} {e : Sym2 V} :
    e ∈ internal E S ↔ e ∈ E ∧ ∀ v ∈ e, v ∈ S := by
  unfold internal; simp

lemma mem_cut' {E : Finset (Sym2 V)} {S : Finset V} {e : Sym2 V} :
    e ∈ cut E S ↔ e ∈ E ∧ ∃ v ∈ e, v ∈ S ∧ ∃ w ∈ e, w ∉ S := by
  unfold cut; simp

lemma mem_support' {E : Finset (Sym2 V)} {x : Sym2 V → ℝ} {e : Sym2 V} :
    e ∈ support E x ↔ e ∈ E ∧ x e ≠ 0 := by
  unfold support; simp

noncomputable def compF (F : Finset (Sym2 V)) (a : V) : Finset V := by
  classical
  exact Finset.univ.filter
    (fun w => (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable a w)

lemma mem_compF {F : Finset (Sym2 V)} {a w : V} :
    w ∈ compF F a ↔ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable a w := by
  unfold compF; simp

lemma card_compF_le (F : Finset (Sym2 V)) (a : V) :
    (compF F a).card ≤ (internal F (compF F a)).card + 1 := by
  classical
  let G := SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))
  let C := G.connectedComponentMk a
  have hconn := C.connected_toSimpleGraph
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  have hsupp : ∀ w, w ∈ C.supp ↔ w ∈ compF F a := by
    intro w
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, mem_compF,
      SimpleGraph.ConnectedComponent.eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hc1 : Nat.card C.supp = (compF F a).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hsupp)
  have hc2 : Nat.card C.toSimpleGraph.edgeSet ≤ (internal F (compF F a)).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective
      (fun e => ⟨Sym2.map Subtype.val e.1, ?_⟩) ?_
    · obtain ⟨e, he⟩ := e
      induction e using Sym2.ind with
      | h p q =>
        have hadj : C.toSimpleGraph.Adj p q := he
        have hadj' : G.Adj p.1 q.1 := hadj
        rw [SimpleGraph.fromEdgeSet_adj] at hadj'
        rw [Sym2.map_mk, mem_internal']
        refine ⟨hadj'.1, ?_⟩
        intro v hv
        rw [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · exact (hsupp _).1 p.2
        · exact (hsupp _).1 q.2
    · intro e1 e2 h
      have h' : Sym2.map Subtype.val e1.1 = Sym2.map Subtype.val e2.1 := by
        simpa using congrArg Subtype.val h
      exact Subtype.ext (Sym2.map.injective Subtype.val_injective h')
  have hc1' : Nat.card C = (compF F a).card := hc1
  omega


lemma self_mem_compF (F : Finset (Sym2 V)) (a : V) : a ∈ compF F a :=
  mem_compF.2 (SimpleGraph.Reachable.refl a)

lemma compF_eq_or_disjoint (F : Finset (Sym2 V)) (a b : V) :
    compF F a = compF F b ∨ Disjoint (compF F a) (compF F b) := by
  by_cases h : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable a b
  · left; ext w; simp only [mem_compF]
    exact ⟨fun hw => h.symm.trans hw, fun hw => h.trans hw⟩
  · right; rw [Finset.disjoint_left]; intro w hwa hwb
    rw [mem_compF] at hwa hwb; exact h (hwa.trans hwb.symm)

lemma compatible_union (F : Finset (Sym2 V)) (a b : V) :
    Compatible F (compF F a ∪ compF F b) := by
  intro C hC
  obtain ⟨v, rfl⟩ := hC
  by_cases h : ∃ w, w ∈ component F v ∧ w ∈ (↑(compF F a ∪ compF F b) : Set V)
  · left
    obtain ⟨w, hw1, hw2⟩ := h
    intro u hu
    have hvw : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable v w := hw1
    have hvu : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable v u := hu
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, mem_compF] at hw2 ⊢
    rcases hw2 with h | h
    · left; exact h.trans (hvw.symm.trans hvu)
    · right; exact h.trans (hvw.symm.trans hvu)
  · right
    rw [Set.disjoint_left]; intro u hu hu'; exact h ⟨u, hu, hu'⟩

lemma card_le_internal_union (F : Finset (Sym2 V)) (a b : V) :
    (compF F a ∪ compF F b).card ≤ (internal F (compF F a ∪ compF F b)).card + 2 := by
  rcases compF_eq_or_disjoint F a b with h | h
  · rw [h, Finset.union_self]; have := card_compF_le F b; omega
  · rw [Finset.card_union_of_disjoint h]
    have hA := card_compF_le F a
    have hB := card_compF_le F b
    have hsub : internal F (compF F a) ∪ internal F (compF F b) ⊆
        internal F (compF F a ∪ compF F b) := by
      intro e he
      rw [Finset.mem_union, mem_internal', mem_internal'] at he
      rw [mem_internal']
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, fun v hv => Finset.mem_union_left _ (h2 v hv)⟩
      · exact ⟨h1, fun v hv => Finset.mem_union_right _ (h2 v hv)⟩
    have hdisj : Disjoint (internal F (compF F a)) (internal F (compF F b)) := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      rw [mem_internal'] at h1 h2
      induction e using Sym2.ind with
      | h p q =>
        exact Finset.disjoint_left.1 h (h1.2 p (Sym2.mem_mk_left p q))
          (h2.2 p (Sym2.mem_mk_left p q))
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at this
    omega

lemma x_le_one (I : Instance V) (x : Sym2 V → ℝ)
    (hfeas : Feasible I.E I.B I.W I.F x) {e : Sym2 V} (he : e ∈ I.E) : x e ≤ 1 := by
  induction e using Sym2.ind with
  | h a b =>
    have hne : (compF I.F a ∪ compF I.F b).Nonempty :=
      ⟨a, Finset.mem_union_left _ (self_mem_compF _ _)⟩
    have h1 := hfeas.2.2.1 _ hne (compatible_union _ _ _)
    have h2 := card_le_internal_union I.F a b
    have hmem : s(a, b) ∈ internal I.E (compF I.F a ∪ compF I.F b) := by
      rw [mem_internal']
      refine ⟨he, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact Finset.mem_union_left _ (self_mem_compF _ _)
      · exact Finset.mem_union_right _ (self_mem_compF _ _)
    have h3 : x s(a, b) ≤ edgeSum x (internal I.E (compF I.F a ∪ compF I.F b)) := by
      unfold edgeSum
      exact Finset.single_le_sum
        (fun e he' => hfeas.2.2.2.2 e (mem_internal'.1 he').1) hmem
    have h2' : ((compF I.F a ∪ compF I.F b).card : ℝ) ≤
        ((internal I.F (compF I.F a ∪ compF I.F b)).card : ℝ) + 2 := by
      exact_mod_cast h2
    linarith


noncomputable def chP (L : Finset (Finset V)) (P : Finset V → Prop) : Finset (Finset V) := by
  classical
  exact L.filter (fun R => P R ∧ ∀ R' ∈ L, R ⊂ R' → ¬ P R')

lemma mem_chP {L : Finset (Finset V)} {P : Finset V → Prop} {R : Finset V} :
    R ∈ chP L P ↔ R ∈ L ∧ P R ∧ ∀ R' ∈ L, R ⊂ R' → ¬ P R' := by
  unfold chP; simp

lemma chP_subset (L : Finset (Finset V)) (P : Finset V → Prop) : chP L P ⊆ L :=
  fun _ h => (mem_chP.1 h).1

lemma laminar_nested {L : Finset (Finset V)} (hlam : Laminar L) {R1 R2 : Finset V}
    (h1 : R1 ∈ L) (h2 : R2 ∈ L) (hne : (R1 ∩ R2).Nonempty) : R1 ⊆ R2 ∨ R2 ⊆ R1 := by
  have := hlam R1 h1 R2 h2
  unfold Intersecting at this
  by_cases hA : (R1 \ R2).Nonempty
  · right
    have hB : ¬ (R2 \ R1).Nonempty := fun hB => this ⟨hne, hA, hB⟩
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hB
    exact hB
  · left
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hA
    exact hA

lemma chP_disj {L : Finset (Finset V)} (hlam : Laminar L) {P : Finset V → Prop}
    {R1 R2 : Finset V} (h1 : R1 ∈ chP L P) (h2 : R2 ∈ chP L P) (hne : R1 ≠ R2) :
    Disjoint R1 R2 := by
  rw [mem_chP] at h1 h2
  by_contra hd
  rw [Finset.not_disjoint_iff_nonempty_inter] at hd
  rcases laminar_nested hlam h1.1 h2.1 hd with h | h
  · exact h1.2.2 R2 h2.1 (Finset.ssubset_iff_subset_ne.2 ⟨h, hne⟩) h2.2.1
  · exact h2.2.2 R1 h1.1 (Finset.ssubset_iff_subset_ne.2 ⟨h, fun h' => hne h'.symm⟩) h1.2.1

lemma chP_exists {L : Finset (Finset V)} {P : Finset V → Prop} {R : Finset V}
    (hR : R ∈ L) (hP : P R) : ∃ R' ∈ chP L P, R ⊆ R' := by
  classical
  obtain ⟨M, hM, hmax⟩ := (L.filter (fun R' => R ⊆ R' ∧ P R')).exists_max_image
    Finset.card ⟨R, Finset.mem_filter.2 ⟨hR, subset_refl _, hP⟩⟩
  rw [Finset.mem_filter] at hM
  refine ⟨M, mem_chP.2 ⟨hM.1, hM.2.2, fun R' hR' hss hP' => ?_⟩, hM.2.1⟩
  have := hmax R' (Finset.mem_filter.2 ⟨hR', hM.2.1.trans hss.subset, hP'⟩)
  have := Finset.card_lt_card hss
  omega

lemma internal_mono {E : Finset (Sym2 V)} {S R : Finset V} (h : R ⊆ S) {e : Sym2 V}
    (he : e ∈ internal E R) : e ∈ internal E S := by
  rw [mem_internal'] at he ⊢
  exact ⟨he.1, fun v hv => h (he.2 v hv)⟩

open Classical in
lemma sum_chP {E : Finset (Sym2 V)} {L : Finset (Finset V)} (hlam : Laminar L)
    (P : Finset V → Prop) (e : Sym2 V) :
    (∑ R ∈ chP L P, (if e ∈ internal E R then (1:ℝ) else 0)) =
      if (∃ R ∈ L, P R ∧ e ∈ internal E R) then 1 else 0 := by
  classical
  rw [Finset.sum_boole]
  split_ifs with h
  · obtain ⟨R, hR, hP, he⟩ := h
    obtain ⟨R', hR', hsub⟩ := chP_exists hR hP
    have he' : e ∈ internal E R' := internal_mono hsub he
    have : (chP L P).filter (fun R => e ∈ internal E R) = {R'} := by
      ext R''
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        by_contra hne
        have hd := chP_disj hlam h1 hR' hne
        rw [mem_internal'] at h2 he'
        induction e using Sym2.ind with
        | h p q =>
          exact Finset.disjoint_left.1 hd (h2.2 p (Sym2.mem_mk_left p q))
            (he'.2 p (Sym2.mem_mk_left p q))
      · rintro rfl; exact ⟨hR', he'⟩
    rw [this]; simp
  · have : (chP L P).filter (fun R => e ∈ internal E R) = ∅ := by
      ext R''
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro h1 h2
      exact h ⟨R'', (mem_chP.1 h1).1, (mem_chP.1 h1).2.1, h2⟩
    rw [this]; simp

lemma indep_coeffs {E : Finset (Sym2 V)} {x : Sym2 V → ℝ} {L : Finset (Finset V)}
    {T : Finset V}
    (hli : LinearIndependent ℝ (fun i : Sum {S : Finset V // S ∈ L} {v : V // v ∈ T} =>
      match i with
      | .inl S => indicatorOnSupport E x (internal E S.val)
      | .inr v => indicatorOnSupport E x (cut E {v.val})))
    (a : Finset V → ℝ) (b : V → ℝ)
    (h : ∀ e ∈ support E x, (∑ S ∈ L, a S * (if e ∈ internal E S then 1 else 0)) +
      ∑ v ∈ T, b v * (if e ∈ cut E {v} then 1 else 0) = 0) :
    (∀ S ∈ L, a S = 0) ∧ (∀ v ∈ T, b v = 0) := by
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (Sum.elim (fun S => a S.1) (fun v => b v.1)) ?_
  · exact ⟨fun S hS => key (.inl ⟨S, hS⟩), fun v hv => key (.inr ⟨v, hv⟩)⟩
  · funext e
    rw [Finset.sum_apply, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, indicatorOnSupport,
      Pi.zero_apply]
    have := h e.1 e.2
    rw [Finset.sum_coe_sort L (fun S => a S * if e.1 ∈ internal E S then 1 else 0),
      Finset.sum_coe_sort T (fun v => b v * if e.1 ∈ cut E {v} then 1 else 0)]
    exact this


lemma internal_subset (E : Finset (Sym2 V)) (S : Finset V) : internal E S ⊆ E :=
  fun _ he => (mem_internal'.1 he).1

lemma cut_subset (E : Finset (Sym2 V)) (S : Finset V) : cut E S ⊆ E :=
  fun _ he => (mem_cut'.1 he).1

lemma edgeSum_eq_supp {E : Finset (Sym2 V)} {x : Sym2 V → ℝ} {A : Finset (Sym2 V)}
    (hA : A ⊆ E) :
    edgeSum x A = ∑ e ∈ support E x, x e * (if e ∈ A then 1 else 0) := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  unfold edgeSum
  symm
  apply Finset.sum_subset
  · intro e he; exact (Finset.mem_filter.1 he).2
  · intro e heA hn
    by_contra hx
    exact hn (Finset.mem_filter.2 ⟨mem_support'.2 ⟨hA heA, hx⟩, heA⟩)

lemma mem_cut_single {E : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ E) (hd : ¬ e.IsDiag)
    (v : V) : e ∈ cut E {v} ↔ v ∈ e := by
  rw [mem_cut']
  induction e using Sym2.ind with
  | h p q =>
    have hpq : p ≠ q := fun h => hd (Sym2.mk_isDiag_iff.2 h)
    constructor
    · rintro ⟨_, u, hu, hu', _⟩
      rw [Finset.mem_singleton] at hu'; subst hu'; exact hu
    · intro hv
      refine ⟨he, v, hv, Finset.mem_singleton_self v, ?_⟩
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact ⟨q, Sym2.mem_mk_right _ _, by rw [Finset.mem_singleton]; exact hpq.symm⟩
      · exact ⟨p, Sym2.mem_mk_left _ _, by rw [Finset.mem_singleton]; exact hpq⟩

theorem false_core (I : Instance V) (x : Sym2 V → ℝ) (L : Finset (Finset V)) (T : Finset V)
    (hvalid : Valid I) (hfeas : Feasible I.E I.B I.W I.F x)
    (hbasis : DefinesBasis I.E I.B I.W I.F x L T)
    (hnoone : ∀ e ∈ support I.E x, x e ≠ 1)
    (hnosmall : ∀ w ∈ I.W, (degree (support I.E x) w : ℤ) > I.B w + 1) : False := by
  classical
  obtain ⟨hLne, hlam, _, hTW, hLt, hTt, _, hli, hcard⟩ := hbasis
  set Es := support I.E x with hEs_def
  have hEsE : ∀ e ∈ Es, e ∈ I.E := fun e he => (mem_support'.1 he).1
  have hxpos : ∀ e ∈ Es, 0 < x e := fun e he =>
    lt_of_le_of_ne (hfeas.2.2.2.2 e (hEsE e he)) (Ne.symm (mem_support'.1 he).2)
  have hxlt : ∀ e ∈ Es, x e < 1 := fun e he =>
    lt_of_le_of_ne (x_le_one I x hfeas (hEsE e he)) (hnoone e he)
  let own : Finset V → Sym2 V → Prop := fun S e =>
    e ∈ internal I.E S ∧ ¬ ∃ R ∈ L, R ⊂ S ∧ e ∈ internal I.E R
  have hpt : ∀ S, ∀ e, (if e ∈ internal I.E S then (1:ℝ) else 0) =
      (if own S e then 1 else 0) +
      ∑ R ∈ chP L (fun R => R ⊂ S), (if e ∈ internal I.E R then (1:ℝ) else 0) := by
    intro S e
    rw [sum_chP hlam]
    by_cases h1 : e ∈ internal I.E S <;> by_cases h2 : ∃ R ∈ L, R ⊂ S ∧ e ∈ internal I.E R
    · rw [if_pos h1, if_neg (fun h => h.2 h2), if_pos h2]; ring
    · rw [if_pos h1, if_pos ⟨h1, h2⟩, if_neg h2]; ring
    · exfalso; obtain ⟨R, _, hRS, he⟩ := h2; exact h1 (internal_mono hRS.subset he)
    · rw [if_neg h1, if_neg (fun h => h1 h.1), if_neg h2]; ring
  -- Step A
  have hA : ∀ S ∈ L, (1:ℝ) ≤ ∑ e ∈ Es, x e * (if own S e then 1 else 0) := by
    intro S hS
    have hid : edgeSum x (internal I.E S) = ∑ e ∈ Es, x e * (if own S e then 1 else 0) +
        ∑ R ∈ chP L (fun R => R ⊂ S), edgeSum x (internal I.E R) := by
      rw [edgeSum_eq_supp (internal_subset _ _)]
      simp_rw [edgeSum_eq_supp (internal_subset _ _)]
      rw [Finset.sum_comm (s := chP L (fun R => R ⊂ S)), ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      rw [hpt S e, mul_add, Finset.mul_sum]
    have hR_t : ∀ R ∈ chP L (fun R => R ⊂ S), edgeSum x (internal I.E R) =
        (R.card:ℝ) - (internal I.F R).card - 1 :=
      fun R hR => hLt R (chP_subset _ _ hR)
    rw [Finset.sum_congr rfl hR_t, hLt S hS] at hid
    have hown : ∃ e ∈ Es, own S e := by
      by_contra hno
      push_neg at hno
      have hSch : S ∉ chP L (fun R => R ⊂ S) := fun h =>
        absurd (mem_chP.1 h).2.1 (ssubset_irrefl S)
      have := (indep_coeffs hli
        (fun R => (if R = S then 1 else 0) - (if R ∈ chP L (fun R => R ⊂ S) then 1 else 0))
        (fun _ => 0) ?_).1 S hS
      · simp [hSch] at this
      · intro e he
        simp only [zero_mul, Finset.sum_const_zero, add_zero, sub_mul,
          Finset.sum_sub_distrib, ite_mul, one_mul]
        rw [Finset.sum_ite_eq' L S, if_pos hS, ← Finset.sum_filter,
          Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (chP_subset _ _), hpt S e,
          if_neg (hno e he)]
        ring
    obtain ⟨e0, he0, hown0⟩ := hown
    have hpos : 0 < ∑ e ∈ Es, x e * (if own S e then 1 else 0) := by
      have := Finset.single_le_sum (f := fun e => x e * (if own S e then (1:ℝ) else 0))
        (fun e he => mul_nonneg (hxpos e he).le (by split_ifs <;> norm_num)) he0
      simp only [if_pos hown0, mul_one] at this
      linarith [hxpos e0 he0]
    set k : ℤ := (S.card:ℤ) - (internal I.F S).card - 1 -
      ∑ R ∈ chP L (fun R => R ⊂ S), ((R.card:ℤ) - (internal I.F R).card - 1) with hk
    have hkr : (k:ℝ) = ∑ e ∈ Es, x e * (if own S e then 1 else 0) := by
      rw [hk]; push_cast; linarith [hid]
    have hk0 : (0:ℝ) < k := by rw [hkr]; exact hpos
    have hk1 : 1 ≤ k := by exact_mod_cast hk0
    rw [← hkr]; exact_mod_cast hk1
  -- Step C
  have hC : ∀ v ∈ T, (2:ℝ) ≤
      ∑ e ∈ Es, (1 - x e) * (if e ∈ cut I.E {v} then 1 else 0) := by
    intro v hv
    have h1 : ∑ e ∈ Es, x e * (if e ∈ cut I.E {v} then 1 else 0) = I.B v := by
      rw [← edgeSum_eq_supp (cut_subset _ _)]; exact hTt v hv
    have h2 : ∑ e ∈ Es, (if e ∈ cut I.E {v} then (1:ℝ) else 0) = (degree Es v : ℝ) := by
      rw [Finset.sum_boole]
      unfold degree
      congr 2
      apply Finset.filter_congr
      intro e he
      exact mem_cut_single (hEsE e he) (hvalid.1 e (hEsE e he)) v
    have h3 := hnosmall v (hTW hv)
    have h3' : (degree Es v : ℝ) ≥ I.B v + 2 := by
      have : (degree Es v:ℤ) ≥ I.B v + 2 := by omega
      exact_mod_cast this
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
    rw [h1, h2]; linarith
  -- counting
  let cnt : Sym2 V → ℝ := fun e => ∑ S ∈ L, (if own S e then (1:ℝ) else 0)
  let t : Sym2 V → ℝ := fun e => ∑ v ∈ T, (if e ∈ cut I.E {v} then (1:ℝ) else 0)
  have hcnt : ∀ e ∈ Es, cnt e ≤ 1 := by
    intro e _
    simp only [cnt]
    rw [Finset.sum_boole]
    have : (L.filter (fun S => own S e)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro S1 h1 S2 h2
      rw [Finset.mem_filter] at h1 h2
      by_contra hne
      have hnei : (S1 ∩ S2).Nonempty := by
        have a1 := (mem_internal'.1 h1.2.1).2
        have a2 := (mem_internal'.1 h2.2.1).2
        induction e using Sym2.ind with
        | h p q =>
          exact ⟨p, Finset.mem_inter.2 ⟨a1 p (Sym2.mem_mk_left p q),
            a2 p (Sym2.mem_mk_left p q)⟩⟩
      rcases laminar_nested hlam h1.1 h2.1 hnei with h | h
      · exact h2.2.2 ⟨S1, h1.1, Finset.ssubset_iff_subset_ne.2 ⟨h, hne⟩, h1.2.1⟩
      · exact h1.2.2 ⟨S2, h2.1, Finset.ssubset_iff_subset_ne.2 ⟨h, fun h' => hne h'.symm⟩,
          h2.2.1⟩
    exact_mod_cast this
  have hcnt0 : ∀ e, 0 ≤ cnt e := fun e =>
    Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have ht : ∀ e ∈ Es, t e ≤ 2 := by
    intro e _
    simp only [t]
    rw [Finset.sum_boole]
    have : (T.filter (fun v => e ∈ cut I.E {v})).card ≤ 2 := by
      induction e using Sym2.ind with
      | h p q =>
        have hsub : T.filter (fun v => s(p, q) ∈ cut I.E {v}) ⊆ {p, q} := by
          intro v hv
          rw [Finset.mem_filter, mem_cut'] at hv
          obtain ⟨_, u, hu, hu', _⟩ := hv.2
          rw [Finset.mem_singleton] at hu'
          subst hu'
          rcases Sym2.mem_iff.1 hu with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    exact_mod_cast this
  have ht0 : ∀ e, 0 ≤ t e := fun e =>
    Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hL : (L.card:ℝ) ≤ ∑ e ∈ Es, x e * cnt e := by
    calc (L.card:ℝ) = ∑ S ∈ L, (1:ℝ) := by simp
      _ ≤ ∑ S ∈ L, ∑ e ∈ Es, x e * (if own S e then 1 else 0) := Finset.sum_le_sum hA
      _ = ∑ e ∈ Es, x e * cnt e := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro e _
        simp only [cnt]; rw [Finset.mul_sum]
  have hT : 2 * (T.card:ℝ) ≤ ∑ e ∈ Es, (1 - x e) * t e := by
    calc 2 * (T.card:ℝ) = ∑ v ∈ T, (2:ℝ) := by simp; ring
      _ ≤ ∑ v ∈ T, ∑ e ∈ Es, (1 - x e) * (if e ∈ cut I.E {v} then 1 else 0) :=
          Finset.sum_le_sum hC
      _ = ∑ e ∈ Es, (1 - x e) * t e := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro e _
        simp only [t]; rw [Finset.mul_sum]
  have hcardr : (Es.card:ℝ) = L.card + T.card := by exact_mod_cast hcard
  have hle : ∀ e ∈ Es, x e * cnt e + (1 - x e) * t e / 2 ≤ 1 := by
    intro e he
    have h1 := mul_le_mul_of_nonneg_left (hcnt e he) (hxpos e he).le
    have h2 := mul_le_mul_of_nonneg_left (ht e he) (sub_nonneg.2 (hxlt e he).le)
    nlinarith
  have hsum : ∑ e ∈ Es, (x e * cnt e + (1 - x e) * t e / 2) = ∑ e ∈ Es, (1:ℝ) := by
    apply le_antisymm (Finset.sum_le_sum hle)
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcardr]; linarith
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hsum
  have hcov : ∀ e ∈ Es, ∃ S ∈ L, e ∈ internal I.E S := by
    intro e he
    have h1 := heq e he
    have h2 := ht e he
    have hc : 1 ≤ cnt e := by
      by_contra hc; push_neg at hc
      have := hxpos e he
      have := hxlt e he
      nlinarith [mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 (hxlt e he).le),
        mul_lt_mul_of_pos_left hc (hxpos e he)]
    by_contra hno
    push_neg at hno
    have : cnt e = 0 := Finset.sum_eq_zero (fun S hS => if_neg (fun h => hno S hS h.1))
    linarith
  have ht2 : ∀ e ∈ Es, t e = 2 := by
    intro e he
    have h1 := heq e he
    have h2 := ht e he
    by_contra hc
    have hc' : t e < 2 := lt_of_le_of_ne h2 hc
    nlinarith [mul_le_mul_of_nonneg_left (hcnt e he) (hxpos e he).le,
      mul_lt_mul_of_pos_left hc' (sub_pos.2 (hxlt e he))]
  have key := (indep_coeffs hli
    (fun R => if R ∈ chP L (fun _ => True) then 2 else 0) (fun _ => -1) ?_).1
  · obtain ⟨R0, hR0⟩ := hLne
    obtain ⟨R', hR', _⟩ := chP_exists (P := fun _ => True) hR0 trivial
    have := key R' (chP_subset _ _ hR')
    simp [hR'] at this
  · intro e he
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.2 (chP_subset _ _), ← Finset.mul_sum, sum_chP hlam]
    obtain ⟨S, hS, heS⟩ := hcov e he
    rw [if_pos ⟨S, hS, trivial, heS⟩]
    have h2 := ht2 e he
    simp only [t] at h2
    simp only [neg_one_mul, Finset.sum_neg_distrib]
    rw [h2]; ring

end
end BoundedDegreeST.PlusOne

open BoundedDegreeST.PlusOne


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (I : Instance V) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) (S : Finset V)
    (hvalid : Valid I) (hbasic : Basic I.E I.B I.W I.F x)
    (hnotree : ¬ IsSpanningTree I.F)
    (hbasis : DefinesBasis I.E I.B I.W I.F x L T)
    (hnoone : ∀ e ∈ support I.E x, x e ≠ 1)
    (hnosmall : ∀ w ∈ I.W, (degree (support I.E x) w : ℤ) > I.B w + 1)
    (hroot : S ∈ L) :
    2 * (T ∩ S).card +
      2 * (L.filter (fun R => R ⊂ S)).card + 4 ≤
      ∑ v ∈ S, degree (support I.E x) v := by
  exact (false_core I x L T hvalid hbasic.1 hbasis hnoone hnosmall).elim
