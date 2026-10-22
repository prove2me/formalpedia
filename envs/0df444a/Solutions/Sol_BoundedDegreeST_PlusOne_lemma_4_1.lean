-- Prove2me | solution 1 for BoundedDegreeST.PlusOne.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:00:29.261323+00:00
-- url     : https://prove2.me/submissions/8027d4d2-97bf-440a-9989-b2e76ab4ae7e

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


lemma acyclic_bound {W : Type*} [Finite W] [Nonempty W] (H : SimpleGraph W)
    (h : H.IsAcyclic) : Nat.card H.edgeSet + 1 ≤ Nat.card W := by
  obtain ⟨H', hle, hmax⟩ := SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic
    (G := ⊤) le_top h
  have hT : H'.IsTree :=
    (SimpleGraph.connected_top.maximal_le_isAcyclic_iff_isTree le_top).1 hmax
  have h1 := (SimpleGraph.isTree_iff_connected_and_card.1 hT).2
  have h2 : Nat.card H.edgeSet ≤ Nat.card H'.edgeSet :=
    Nat.card_mono (Set.toFinite _) (SimpleGraph.edgeSet_subset_edgeSet.2 hle)
  omega

lemma forest_card_lt (F : Finset (Sym2 V)) (hF : IsForest F) (hnt : ¬ IsSpanningTree F)
    [Nonempty V] : F.card + 2 ≤ Fintype.card V := by
  classical
  set G := SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V)) with hG
  have hnc : ¬ G.Connected := fun hc => hnt ⟨hF.1, ⟨hc, hF.2⟩⟩
  rw [SimpleGraph.connected_iff] at hnc
  have hnp : ¬ G.Preconnected := fun hp => hnc ⟨hp, inferInstance⟩
  unfold SimpleGraph.Preconnected at hnp
  push_neg at hnp
  obtain ⟨a, b, hab⟩ := hnp
  have hne : a ≠ b := fun h => hab (h ▸ SimpleGraph.Reachable.refl a)
  have hnotin : s(a, b) ∉ F := by
    intro h
    exact hab (SimpleGraph.Adj.reachable (by
      rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨h, hne⟩))
  have hacyc : (G ⊔ SimpleGraph.edge a b).IsAcyclic := hF.2.sup_edge_of_not_reachable hab
  have hbd := acyclic_bound _ hacyc
  have hes : (G ⊔ SimpleGraph.edge a b).edgeSet = ↑(insert s(a, b) F) := by
    rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge, hG,
      SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_union, Set.mem_sdiff, Finset.mem_coe, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.coe_insert]
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact Or.inr h
      · exact Or.inl (by simp at h; exact h.1)
    · rintro (h | h)
      · right; simp [h, hne]
      · left; refine ⟨h, ?_⟩
        exact hF.1 e h
  rw [hes, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_insert_of_notMem hnotin,
    Nat.card_eq_fintype_card] at hbd
  omega

lemma support_nonempty (I : Instance V) (x : Sym2 V → ℝ) (hvalid : Valid I)
    (hfeas : Feasible I.E I.B I.W I.F x) (hnt : ¬ IsSpanningTree I.F) :
    (support I.E x).Nonempty ∧ Nonempty V := by
  have hV : Nonempty V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    have h1 := hfeas.2.1
    have hE : I.E = ∅ := Finset.eq_empty_of_forall_notMem (fun e _ => by
      induction e using Sym2.ind with | h p q => exact hV.false p)
    rw [hE] at h1
    unfold edgeSum at h1
    simp [Fintype.card_eq_zero] at h1
    linarith [show (0:ℝ) ≤ I.F.card from Nat.cast_nonneg _]
  refine ⟨?_, hV⟩
  have hc := forest_card_lt I.F hvalid.2.1 hnt
  have h1 := hfeas.2.1
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have : edgeSum x I.E = 0 := by
    unfold edgeSum
    apply Finset.sum_eq_zero
    intro e he
    by_contra hx
    have : e ∈ support I.E x := mem_support'.2 ⟨he, hx⟩
    rw [hne] at this; simp at this
  have hc' : (I.F.card : ℝ) + 2 ≤ Fintype.card V := by exact_mod_cast hc
  linarith


lemma compat_inter {F : Finset (Sym2 V)} {S R : Finset V} (hS : Compatible F S)
    (hR : Compatible F R) : Compatible F (S ∩ R) := by
  intro C hC
  rcases hS C hC with h1 | h1 <;> rcases hR C hC with h2 | h2
  · left; rw [Finset.coe_inter]; exact Set.subset_inter h1 h2
  · right; rw [Finset.coe_inter]; exact h2.mono_right Set.inter_subset_right
  · right; rw [Finset.coe_inter]; exact h1.mono_right Set.inter_subset_left
  · right; rw [Finset.coe_inter]; exact h1.mono_right Set.inter_subset_left

lemma compat_union {F : Finset (Sym2 V)} {S R : Finset V} (hS : Compatible F S)
    (hR : Compatible F R) : Compatible F (S ∪ R) := by
  intro C hC
  rcases hS C hC with h1 | h1 <;> rcases hR C hC with h2 | h2
  · left; rw [Finset.coe_union]; exact h1.trans Set.subset_union_left
  · left; rw [Finset.coe_union]; exact h1.trans Set.subset_union_left
  · left; rw [Finset.coe_union]; exact h2.trans Set.subset_union_right
  · right; rw [Finset.coe_union]; exact Set.disjoint_union_right.2 ⟨h1, h2⟩

lemma compat_closed {F : Finset (Sym2 V)} {S : Finset V} (hS : Compatible F S) {p q : V}
    (hp : p ∈ S) (he : s(p, q) ∈ F) : q ∈ S := by
  have hreach : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable p q := by
    by_cases hpq : p = q
    · subst hpq; exact SimpleGraph.Reachable.refl p
    · exact SimpleGraph.Adj.reachable (by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨he, hpq⟩)
  rcases hS (component F p) ⟨p, rfl⟩ with h | h
  · exact h hreach
  · exact absurd hp (Set.disjoint_left.1 h (SimpleGraph.Reachable.refl p))

lemma internal_inter (E : Finset (Sym2 V)) (S R : Finset V) :
    internal E (S ∩ R) = internal E S ∩ internal E R := by
  ext e
  simp only [mem_internal', Finset.mem_inter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun v hv => (h2 v hv).1⟩,
      ⟨h1, fun v hv => (h2 v hv).2⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨_, h3⟩⟩; exact ⟨h1, fun v hv => ⟨h2 v hv, h3 v hv⟩⟩

lemma internal_F_union {F : Finset (Sym2 V)} {S R : Finset V} (hS : Compatible F S)
    (hR : Compatible F R) : internal F (S ∪ R) = internal F S ∪ internal F R := by
  ext e
  simp only [Finset.mem_union]
  constructor
  · intro he
    rw [mem_internal'] at he
    induction e using Sym2.ind with
    | h p q =>
      have hp := he.2 p (Sym2.mem_mk_left p q)
      rcases Finset.mem_union.1 hp with hp | hp
      · left; rw [mem_internal']; refine ⟨he.1, fun v hv => ?_⟩
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact hp
        · exact compat_closed hS hp he.1
      · right; rw [mem_internal']; refine ⟨he.1, fun v hv => ?_⟩
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact hp
        · exact compat_closed hR hp he.1
  · rintro (h | h)
    · exact internal_mono Finset.subset_union_left h
    · exact internal_mono Finset.subset_union_right h

/-- tight compatible set -/
def Tight (E F : Finset (Sym2 V)) (x : Sym2 V → ℝ) (S : Finset V) : Prop :=
  S.Nonempty ∧ Compatible F S ∧
    edgeSum x (internal E S) = (S.card : ℝ) - ((internal F S).card : ℝ) - 1

lemma uncross {E F : Finset (Sym2 V)} {B : V → ℤ} {W : Finset V} {x : Sym2 V → ℝ}
    (hfeas : Feasible E B W F x) {S R : Finset V}
    (hS : Tight E F x S) (hR : Tight E F x R) (hne : (S ∩ R).Nonempty) :
    Tight E F x (S ∩ R) ∧ Tight E F x (S ∪ R) ∧
      indicatorOnSupport E x (internal E S) + indicatorOnSupport E x (internal E R) =
      indicatorOnSupport E x (internal E (S ∩ R)) +
        indicatorOnSupport E x (internal E (S ∪ R)) := by
  classical
  have hci := compat_inter hS.2.1 hR.2.1
  have hcu := compat_union hS.2.1 hR.2.1
  have hneu : (S ∪ R).Nonempty := hS.1.mono Finset.subset_union_left
  have hfi := hfeas.2.2.1 _ hne hci
  have hfu := hfeas.2.2.1 _ hneu hcu
  have hcard1 := Finset.card_union_add_card_inter S R
  have hcard2 := Finset.card_union_add_card_inter (internal F S) (internal F R)
  rw [← internal_F_union hS.2.1 hR.2.1, ← internal_inter] at hcard2
  have hcard1' : ((S ∪ R).card : ℝ) + (S ∩ R).card = S.card + R.card := by exact_mod_cast hcard1
  have hcard2' : ((internal F (S ∪ R)).card : ℝ) + (internal F (S ∩ R)).card =
      (internal F S).card + (internal F R).card := by exact_mod_cast hcard2
  -- pointwise
  let d : Sym2 V → ℝ := fun e =>
    (if e ∈ internal E (S ∩ R) then 1 else 0) + (if e ∈ internal E (S ∪ R) then 1 else 0) -
    (if e ∈ internal E S then 1 else 0) - (if e ∈ internal E R then 1 else 0)
  have hd0 : ∀ e, 0 ≤ d e := by
    intro e
    simp only [d]
    have hsu : e ∈ internal E S → e ∈ internal E (S ∪ R) := internal_mono Finset.subset_union_left
    have hru : e ∈ internal E R → e ∈ internal E (S ∪ R) :=
      internal_mono Finset.subset_union_right
    rw [internal_inter]
    by_cases h1 : e ∈ internal E S <;> by_cases h2 : e ∈ internal E R <;>
      by_cases h3 : e ∈ internal E (S ∪ R) <;> simp_all
  have hsum : ∑ e ∈ support E x, x e * d e =
      edgeSum x (internal E (S ∩ R)) + edgeSum x (internal E (S ∪ R)) -
      edgeSum x (internal E S) - edgeSum x (internal E R) := by
    rw [edgeSum_eq_supp (internal_subset _ _), edgeSum_eq_supp (internal_subset _ _),
      edgeSum_eq_supp (internal_subset _ _), edgeSum_eq_supp (internal_subset _ _),
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro e _; simp only [d]; ring
  have hxpos : ∀ e ∈ support E x, 0 < x e := fun e he =>
    lt_of_le_of_ne (hfeas.2.2.2.2 e (mem_support'.1 he).1) (Ne.symm (mem_support'.1 he).2)
  have hnn : 0 ≤ ∑ e ∈ support E x, x e * d e :=
    Finset.sum_nonneg (fun e he => mul_nonneg (hxpos e he).le (hd0 e))
  have hS3 := hS.2.2
  have hR3 := hR.2.2
  have hz : ∑ e ∈ support E x, x e * d e = 0 := by linarith
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg
    (fun e he => mul_nonneg (hxpos e he).le (hd0 e))).1 hz
  refine ⟨⟨hne, hci, by linarith⟩, ⟨hneu, hcu, by linarith⟩, ?_⟩
  funext e
  have := hz' e.1 e.2
  have hde : d e.1 = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hxpos e.1 e.2).ne'
    · exact h
  simp only [d] at hde
  simp only [Pi.add_apply, indicatorOnSupport]
  linarith


lemma intersecting_symm {S R : Finset V} (h : Intersecting S R) : Intersecting R S :=
  ⟨by rw [Finset.inter_comm]; exact h.1, h.2.2, h.2.1⟩

open Classical in
lemma cross_inter {L : Finset (Finset V)} (hlam : Laminar L) {S R : Finset V} (hR : R ∈ L)
    (hSR : Intersecting S R) :
    (L.filter (fun R' => Intersecting (S ∩ R) R')).card <
      (L.filter (fun R' => Intersecting S R')).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨R, Finset.mem_filter.2 ⟨hR, hSR⟩, fun h => ?_⟩
    obtain ⟨y, hy⟩ := (Finset.mem_filter.1 h).2.2.1
    simp at hy; tauto
  · intro R' h
    rw [Finset.mem_filter] at h ⊢
    obtain ⟨hR', h1, h2, h3⟩ := h
    refine ⟨hR', ?_⟩
    have hn : (R' ∩ R).Nonempty := by
      obtain ⟨y, hy⟩ := h1; exact ⟨y, by simp at hy ⊢; tauto⟩
    rcases laminar_nested hlam hR' hR hn with hsub | hsub
    · refine ⟨?_, ?_, ?_⟩
      · obtain ⟨y, hy⟩ := h1; exact ⟨y, by simp at hy ⊢; tauto⟩
      · obtain ⟨y, hy⟩ := h2; exact ⟨y, by simp at hy ⊢; tauto⟩
      · obtain ⟨y, hy⟩ := h3; refine ⟨y, ?_⟩; simp at hy ⊢; have := hsub hy.1; tauto
    · exfalso; obtain ⟨y, hy⟩ := h2; simp at hy; exact hy.2 (hsub hy.1.2)

open Classical in
lemma cross_union {L : Finset (Finset V)} (hlam : Laminar L) {S R : Finset V} (hR : R ∈ L)
    (hSR : Intersecting S R) :
    (L.filter (fun R' => Intersecting (S ∪ R) R')).card <
      (L.filter (fun R' => Intersecting S R')).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨R, Finset.mem_filter.2 ⟨hR, hSR⟩, fun h => ?_⟩
    obtain ⟨y, hy⟩ := (Finset.mem_filter.1 h).2.2.2
    simp at hy; tauto
  · intro R' h
    rw [Finset.mem_filter] at h ⊢
    obtain ⟨hR', h1, h2, h3⟩ := h
    refine ⟨hR', ?_⟩
    by_cases hn : (R' ∩ R).Nonempty
    · rcases laminar_nested hlam hR' hR hn with hsub | hsub
      · exfalso; obtain ⟨y, hy⟩ := h3; simp at hy; exact hy.2.2 (hsub hy.1)
      · refine ⟨?_, ?_, ?_⟩
        · obtain ⟨y, hy⟩ := hSR.1; refine ⟨y, ?_⟩; simp at hy ⊢; exact ⟨hy.1, hsub hy.2⟩
        · obtain ⟨y, hy⟩ := h2; refine ⟨y, ?_⟩; simp at hy ⊢
          have : y ∉ R := fun h => hy.2 (hsub h)
          tauto
        · obtain ⟨y, hy⟩ := h3; refine ⟨y, ?_⟩; simp at hy ⊢; tauto
    · rw [Finset.not_nonempty_iff_eq_empty] at hn
      have hdis : ∀ y, y ∈ R' → y ∉ R := fun y h1 h2 => by
        have : y ∈ R' ∩ R := Finset.mem_inter.2 ⟨h1, h2⟩
        rw [hn] at this; simp at this
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨y, hy⟩ := h1; refine ⟨y, ?_⟩; simp at hy ⊢; have := hdis y hy.2; tauto
      · obtain ⟨y, hy⟩ := hSR.1; refine ⟨y, ?_⟩; simp at hy ⊢
        exact ⟨hy.1, fun h => hdis y h hy.2⟩
      · obtain ⟨y, hy⟩ := h3; refine ⟨y, ?_⟩; simp at hy ⊢; tauto

lemma exists_max_laminar (TT : Finset (Finset V)) :
    ∃ L ⊆ TT, Laminar L ∧ ∀ S ∈ TT, S ∉ L → ∃ R ∈ L, Intersecting S R := by
  classical
  obtain ⟨L, hL, hmax⟩ := (TT.powerset.filter (fun L => Laminar L)).exists_max_image
    Finset.card ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by simp [Laminar]⟩⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hL
  refine ⟨L, hL.1, hL.2, fun S hS hSL => ?_⟩
  by_contra hno
  push_neg at hno
  have hlam' : Laminar (insert S L) := by
    intro A hA C hC
    rw [Finset.mem_insert] at hA hC
    rcases hA with rfl | hA <;> rcases hC with rfl | hC
    · intro h; obtain ⟨y, hy⟩ := h.2.1; simp at hy
    · exact hno C hC
    · intro h; exact hno A hA (intersecting_symm h)
    · exact hL.2 A hA C hC
  have := hmax (insert S L) (Finset.mem_filter.2
    ⟨Finset.mem_powerset.2 (Finset.insert_subset hS hL.1), hlam'⟩)
  rw [Finset.card_insert_of_notMem hSL] at this
  omega

open Classical in
lemma span_tight {E F : Finset (Sym2 V)} {B : V → ℤ} {W : Finset V} {x : Sym2 V → ℝ}
    (hfeas : Feasible E B W F x)
    (L : Finset (Finset V)) (hlam : Laminar L) (hLT : ∀ R ∈ L, Tight E F x R)
    (hmax : ∀ S, Tight E F x S → S ∉ L → ∃ R ∈ L, Intersecting S R) :
    ∀ S, Tight E F x S → indicatorOnSupport E x (internal E S) ∈
      Submodule.span ℝ ((fun R => indicatorOnSupport E x (internal E R)) ''
        (↑L : Set (Finset V))) := by
  classical
  suffices h : ∀ n, ∀ S, Tight E F x S → (L.filter (fun R' => Intersecting S R')).card = n →
      indicatorOnSupport E x (internal E S) ∈
      Submodule.span ℝ ((fun R => indicatorOnSupport E x (internal E R)) ''
        (↑L : Set (Finset V))) from fun S hS => h _ S hS rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS hn
    by_cases hSL : S ∈ L
    · exact Submodule.subset_span ⟨S, hSL, rfl⟩
    · obtain ⟨R, hR, hSR⟩ := hmax S hS hSL
      obtain ⟨hi, hu, hid⟩ := uncross hfeas hS (hLT R hR) hSR.1
      have h1 := ih _ (hn ▸ cross_inter hlam hR hSR) (S ∩ R) hi rfl
      have h2 := ih _ (hn ▸ cross_union hlam hR hSR) (S ∪ R) hu rfl
      have h3 : indicatorOnSupport E x (internal E R) ∈
          Submodule.span ℝ ((fun R => indicatorOnSupport E x (internal E R)) ''
          (↑L : Set (Finset V))) := Submodule.subset_span ⟨R, hR, rfl⟩
      have : indicatorOnSupport E x (internal E S) =
          indicatorOnSupport E x (internal E (S ∩ R)) +
          indicatorOnSupport E x (internal E (S ∪ R)) -
          indicatorOnSupport E x (internal E R) := by
        rw [← hid]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.add_mem _ h1 h2) h3


theorem lemma_4_3_core (I : Instance V) (x : Sym2 V → ℝ)
    (hvalid : Valid I) (hbasic : Basic I.E I.B I.W I.F x)
    (hnotree : ¬ IsSpanningTree I.F) :
    ∃ (L : Finset (Finset V)) (T : Finset V), DefinesBasis I.E I.B I.W I.F x L T := by
  classical
  have hfeas := hbasic.1
  obtain ⟨hEsne, hV⟩ := support_nonempty I x hvalid hfeas hnotree
  let χ : Finset (Sym2 V) → ({e // e ∈ support I.E x} → ℝ) := indicatorOnSupport I.E x
  let TT : Finset (Finset V) := Finset.univ.filter (fun S => Tight I.E I.F x S)
  let D : Finset V := I.W.filter (fun v => edgeSum x (cut I.E {v}) = (I.B v : ℝ))
  have hintE : internal I.E Finset.univ = I.E := by ext e; simp [mem_internal']
  have huniv : Tight I.E I.F x Finset.univ := by
    refine ⟨Finset.univ_nonempty, fun C _ => Or.inl (by simp), ?_⟩
    have h2 : internal I.F Finset.univ = I.F := by ext e; simp [mem_internal']
    rw [hintE, h2, Finset.card_univ]; exact hfeas.2.1
  obtain ⟨L, hLTT, hlam, hmax⟩ := exists_max_laminar TT
  have hLT : ∀ R ∈ L, Tight I.E I.F x R := fun R hR => (Finset.mem_filter.1 (hLTT hR)).2
  have hmax' : ∀ S, Tight I.E I.F x S → S ∉ L → ∃ R ∈ L, Intersecting S R :=
    fun S hS hSL => hmax S (Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩) hSL
  have hunivL : Finset.univ ∈ L := by
    by_contra h
    obtain ⟨R, _, hR⟩ := hmax' _ huniv h
    obtain ⟨y, hy⟩ := hR.2.2; simp at hy
  have hspanL := span_tight hfeas L hlam hLT hmax'
  let gens : Set ({e // e ∈ support I.E x} → ℝ) :=
    ((fun R => indicatorOnSupport I.E x (internal I.E R)) '' (↑L : Set (Finset V))) ∪
      ((fun v => χ (cut I.E {v})) '' (↑D : Set V))
  have htop : Submodule.span ℝ gens = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hker⟩ :=
      (Submodule.span ℝ gens).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
    let c : {e // e ∈ support I.E x} → ℝ := fun e => f (fun j => if e = j then 1 else 0)
    have hf : ∀ w, f w = ∑ e, w e * c e := by
      intro w
      conv_lhs => rw [pi_eq_sum_univ w]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [map_smul, smul_eq_mul]
    have hfz : ∀ w ∈ gens, f w = 0 := fun w hw => hker (Submodule.subset_span hw)
    let c' : Sym2 V → ℝ := fun e => if h : e ∈ support I.E x then c ⟨e, h⟩ else 0
    let y : Sym2 V → ℝ := fun e => x e + c' e
    have hc'0 : ∀ e, e ∉ support I.E x → c' e = 0 := fun e he => dif_neg he
    have hkey : ∀ A, A ⊆ I.E → edgeSum y A = edgeSum x A + f (χ A) := by
      intro A _
      have h1 : edgeSum y A = edgeSum x A + ∑ e ∈ A, c' e := by
        unfold edgeSum; rw [← Finset.sum_add_distrib]
      have h2 : ∑ e ∈ A, c' e = ∑ e ∈ support I.E x, c' e * (if e ∈ A then 1 else 0) := by
        simp only [mul_ite, mul_one, mul_zero]
        rw [← Finset.sum_filter]
        symm; apply Finset.sum_subset
        · intro e he; exact (Finset.mem_filter.1 he).2
        · intro e heA hn
          apply hc'0
          intro hs; exact hn (Finset.mem_filter.2 ⟨hs, heA⟩)
      have h3 : f (χ A) = ∑ e ∈ support I.E x, c' e * (if e ∈ A then 1 else 0) := by
        rw [hf]
        rw [← Finset.sum_coe_sort (support I.E x) (fun e => c' e * (if e ∈ A then 1 else 0))]
        apply Finset.sum_congr rfl
        intro e _
        simp only [χ, indicatorOnSupport, c', dif_pos e.2]
        ring
      rw [h1, h2, h3]
    have hy := hbasic.2 y ?_ ?_ ?_ ?_ ?_
    · apply hf0
      apply LinearMap.ext
      intro w
      rw [hf w, LinearMap.zero_apply]
      apply Finset.sum_eq_zero
      intro e _
      have h0 : c' e.1 = 0 := by
        have := congrFun hy e.1
        simp only [y] at this; linarith
      simp only [c', dif_pos e.2] at h0
      rw [h0, mul_zero]
    · intro e he
      have hns : e ∉ support I.E x := fun h => he (mem_support'.1 h).1
      simp only [y, hc'0 e hns, hfeas.1 e he, add_zero]
    · have := hkey I.E (subset_refl _)
      have hz : f (χ I.E) = 0 := by
        apply hfz; left; exact ⟨Finset.univ, hunivL, by simp only [χ]; rw [hintE]⟩
      rw [this, hz, add_zero]; exact hfeas.2.1
    · intro S hSne hSc hSt
      have hT : Tight I.E I.F x S := ⟨hSne, hSc, hSt⟩
      rw [hkey _ (internal_subset _ _)]
      have : f (χ (internal I.E S)) = 0 :=
        hker (Submodule.span_mono Set.subset_union_left (hspanL S hT))
      rw [this, add_zero]; exact hSt
    · intro v hv hvt
      rw [hkey _ (cut_subset _ _)]
      have : f (χ (cut I.E {v})) = 0 :=
        hfz _ (Or.inr ⟨v, Finset.mem_filter.2 ⟨hv, hvt⟩, rfl⟩)
      rw [this, add_zero]; exact hvt
    · intro e _ hx0
      have hns : e ∉ support I.E x := fun h => (mem_support'.1 h).2 hx0
      simp only [y, hc'0 e hns, hx0, add_zero]
  -- extraction
  let vec : Sum (Finset V) V → ({e // e ∈ support I.E x} → ℝ) :=
    Sum.elim (fun S => χ (internal I.E S)) (fun v => χ (cut I.E {v}))
  let t : Set (Sum (Finset V) V) := Sum.inl '' (↑L : Set (Finset V)) ∪ Sum.inr '' (↑D : Set V)
  have hs : LinearIndepOn ℝ vec {Sum.inl Finset.univ} := by
    rw [linearIndepOn_singleton_iff]
    obtain ⟨e0, he0⟩ := hEsne
    intro h
    have := congrFun h ⟨e0, he0⟩
    simp only [vec, Sum.elim_inl, χ, indicatorOnSupport, Pi.zero_apply] at this
    rw [if_pos (by rw [mem_internal']; exact ⟨(mem_support'.1 he0).1,
      fun v _ => Finset.mem_univ v⟩)] at this
    exact one_ne_zero this
  obtain ⟨b, hbt, hsb, hspan_b, hbli⟩ := exists_linearIndepOn_extension (t := t) hs (by
    intro i hi; rw [Set.mem_singleton_iff] at hi; subst hi
    exact Or.inl ⟨_, hunivL, rfl⟩)
  let L' := L.filter (fun S => Sum.inl S ∈ b)
  let T' := D.filter (fun v => Sum.inr v ∈ b)
  let fam : Sum {S : Finset V // S ∈ L'} {v : V // v ∈ T'} →
      ({e // e ∈ support I.E x} → ℝ) := fun i =>
    match i with
    | .inl S => indicatorOnSupport I.E x (internal I.E S.val)
    | .inr v => indicatorOnSupport I.E x (cut I.E {v.val})
  let φ : Sum {S : Finset V // S ∈ L'} {v : V // v ∈ T'} → b := fun i =>
    match i with
    | .inl S => ⟨Sum.inl S.1, (Finset.mem_filter.1 S.2).2⟩
    | .inr v => ⟨Sum.inr v.1, (Finset.mem_filter.1 v.2).2⟩
  have hφ : Function.Injective φ := by
    intro i j h
    rcases i with ⟨S, hS⟩ | ⟨v, hv⟩ <;> rcases j with ⟨S', hS'⟩ | ⟨v', hv'⟩ <;>
      simp [φ] at h ⊢ <;> exact h
  have hfam : LinearIndependent ℝ fam := by
    have heq : fam = (fun i : b => vec i) ∘ φ := by
      funext i; rcases i with S | v <;> rfl
    rw [heq]; exact LinearIndependent.comp hbli φ hφ
  have hrange : Submodule.span ℝ (Set.range fam) = ⊤ := by
    rw [eq_top_iff, ← htop]
    apply Submodule.span_le.2
    have hb_sub : vec '' b ⊆ Set.range fam := by
      rintro _ ⟨i, hi, rfl⟩
      rcases hbt hi with ⟨S, hS, rfl⟩ | ⟨v, hv, rfl⟩
      · exact ⟨Sum.inl ⟨S, Finset.mem_filter.2 ⟨hS, hi⟩⟩, rfl⟩
      · exact ⟨Sum.inr ⟨v, Finset.mem_filter.2 ⟨hv, hi⟩⟩, rfl⟩
    have ht_sub : vec '' t ⊆ Submodule.span ℝ (Set.range fam) :=
      hspan_b.trans (Submodule.span_mono hb_sub)
    rintro w (⟨R, hR, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact ht_sub ⟨Sum.inl R, Or.inl ⟨R, hR, rfl⟩, rfl⟩
    · exact ht_sub ⟨Sum.inr v, Or.inr ⟨v, hv, rfl⟩, rfl⟩
  have hcard : (support I.E x).card = L'.card + T'.card := by
    have h1 := finrank_span_eq_card hfam
    rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_coe, Fintype.card_coe, Fintype.card_coe] at h1
    exact h1
  have hxeq : ∀ A ⊆ I.E, (∑ e : {e // e ∈ support I.E x},
      if e.val ∈ A then x e.val else 0) = edgeSum x A := by
    intro A hA
    rw [edgeSum_eq_supp hA,
      ← Finset.sum_coe_sort (support I.E x) (fun e => x e * if e ∈ A then 1 else 0)]
    apply Finset.sum_congr rfl; intro e _; split_ifs <;> simp
  have huniq : ∀ y : {e // e ∈ support I.E x} → ℝ,
      (∀ S ∈ L', (∑ e, if e.val ∈ internal I.E S then y e else 0) =
        (S.card : ℝ) - ((internal I.F S).card : ℝ) - 1) →
      (∀ v ∈ T', (∑ e, if e.val ∈ cut I.E {v} then y e else 0) = (I.B v : ℝ)) →
      y = fun e => x e.val := by
    intro y hyL hyT
    let d : {e // e ∈ support I.E x} → ℝ := fun e => y e - x e.val
    let Λ : ({e // e ∈ support I.E x} → ℝ) →ₗ[ℝ] ℝ := ∑ e, d e • LinearMap.proj e
    have hΛ : ∀ u, Λ u = ∑ e, d e * u e := by intro u; simp [Λ]
    have hsplit : ∀ A : Finset (Sym2 V), (∑ e, d e * (if e.val ∈ A then (1:ℝ) else 0)) =
        (∑ e : {e // e ∈ support I.E x}, if e.val ∈ A then y e else 0) -
        (∑ e : {e // e ∈ support I.E x}, if e.val ∈ A then x e.val else 0) := by
      intro A
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro e _
      simp only [d]; split_ifs <;> ring
    have hz : ∀ i, Λ (fam i) = 0 := by
      rintro (⟨S, hS⟩ | ⟨v, hv⟩)
      · have hSL := (Finset.mem_filter.1 hS).1
        rw [hΛ]
        simp only [fam, indicatorOnSupport]
        rw [hsplit, hyL S hS, hxeq _ (internal_subset _ _), (hLT S hSL).2.2]; ring
      · have hvD := (Finset.mem_filter.1 hv).1
        rw [hΛ]
        simp only [fam, indicatorOnSupport]
        rw [hsplit, hyT v hv, hxeq _ (cut_subset _ _), (Finset.mem_filter.1 hvD).2]; ring
    have hker : Submodule.span ℝ (Set.range fam) ≤ LinearMap.ker Λ :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz i)
    rw [hrange] at hker
    funext e
    have := hker (Submodule.mem_top (x := Pi.single e 1))
    rw [LinearMap.mem_ker, hΛ] at this
    simp [Pi.single_apply, d] at this
    linarith
  refine ⟨L', T', ⟨Finset.univ, Finset.mem_filter.2 ⟨hunivL, hsb rfl⟩⟩, ?_, ?_, ?_, ?_, ?_,
    huniq, hfam, hcard⟩
  · intro S hS R hR
    exact hlam S (Finset.mem_filter.1 hS).1 R (Finset.mem_filter.1 hR).1
  · intro S hS
    have := hLT S (Finset.mem_filter.1 hS).1
    exact ⟨this.1, this.2.1⟩
  · intro v hv
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 hv).1).1
  · intro S hS
    exact (hLT S (Finset.mem_filter.1 hS).1).2.2
  · intro v hv
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 hv).1).2


theorem lemma_4_1_core (I : Instance V) (x : Sym2 V → ℝ)
    (hvalid : Valid I) (hbasic : Basic I.E I.B I.W I.F x)
    (hnotree : ¬ IsSpanningTree I.F) :
    (∃ e ∈ I.E, x e = 1) ∨
    (∃ w ∈ I.W, (degree (support I.E x) w : ℤ) ≤ I.B w + 1) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨L, T, hb⟩ := lemma_4_3_core I x hvalid hbasic hnotree
  exact false_core I x L T hvalid hbasic.1 hb
    (fun e he hx => h1 ⟨e, (mem_support'.1 he).1, hx⟩)
    (fun w hw => lt_of_not_ge (fun hle => h2 ⟨w, hw, hle⟩))

end
end BoundedDegreeST.PlusOne

open BoundedDegreeST.PlusOne


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (I : Instance V) (x : Sym2 V → ℝ)
    (hvalid : Valid I) (hbasic : Basic I.E I.B I.W I.F x)
    (hnotree : ¬ IsSpanningTree I.F) :
    (∃ e ∈ I.E, x e = 1) ∨
    (∃ w ∈ I.W, (degree (support I.E x) w : ℤ) ≤ I.B w + 1) := by
  exact lemma_4_1_core I x hvalid hbasic hnotree
