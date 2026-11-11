-- Prove2me | solution 1 for CombOpt.TutteBerge.tutte_berge_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T04:17:50.764128+00:00
-- url     : https://prove2.me/submissions/fb3342f7-22ce-4a15-a604-fe288ded1e54

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMatching
import Definitions.Def_CombOpt_TutteBerge_Multigraph_tutteBergeBound

set_option autoImplicit false

namespace TBAux
open CombOpt.TutteBerge

/-- Mathlib's odd-component count of `S - A`, as used in `SimpleGraph.IsTutteViolator`. -/
noncomputable def oc {V : Type*} (S : SimpleGraph V) (A : Set V) : ℕ :=
  ((⊤ : S.Subgraph).deleteVerts A).coe.oddComponents.ncard

theorem iso_oc_ncard {V W : Type*} [Finite V] [Finite W] {G₁ : SimpleGraph V}
    {G₂ : SimpleGraph W} (φ : G₁ ≃g G₂) : G₁.oddComponents.ncard = G₂.oddComponents.ncard := by
  have hs : ∀ c : G₁.ConnectedComponent,
      (φ.connectedComponentEquiv c).supp.ncard = c.supp.ncard := by
    intro c
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact (Nat.card_congr (SimpleGraph.ConnectedComponent.isoEquivSupp φ c)).symm
  refine Set.ncard_congr (fun c _ => φ.connectedComponentEquiv c) ?_ ?_ ?_
  · intro c hc
    simp only [SimpleGraph.oddComponents, Set.mem_setOf_eq] at hc ⊢
    rw [hs]; exact hc
  · intro a b _ _ h
    exact φ.connectedComponentEquiv.injective h
  · intro d hd
    refine ⟨φ.connectedComponentEquiv.symm d, ?_, by simp⟩
    simp only [SimpleGraph.oddComponents, Set.mem_setOf_eq] at hd ⊢
    rw [← hs]; simpa using hd

theorem del_ends_iff {V E : Type*} (G : Multigraph V E) (A : Set V) (u v : {v : V // v ∉ A}) :
    (∃ e, (G.deleteNodes A).ends e = s(u, v)) ↔ ∃ e, G.ends e = s(u.1, v.1) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.1, ?_⟩
    have := congrArg (Sym2.map Subtype.val) he
    simpa [Multigraph.deleteNodes] using this
  · rintro ⟨e, he⟩
    refine ⟨⟨e, by rw [he]; simp [u.2, v.2]⟩, ?_⟩
    apply Sym2.map.injective Subtype.val_injective
    simp [Multigraph.deleteNodes, he]

theorem oc_eq {V E : Type*} [Finite V] (G : Multigraph V E) (A : Set V) :
    (G.deleteNodes A).oddComponentCount = oc G.toSimple A := by
  unfold Multigraph.oddComponentCount oc
  apply iso_oc_ncard
  let f : {v : V // v ∉ A} → ((⊤ : G.toSimple.Subgraph).deleteVerts A).verts :=
    fun v => ⟨v.1, by simp [v.2]⟩
  have hinj : Function.Injective f := by
    intro x y h
    simp only [f, Subtype.mk.injEq] at h
    exact Subtype.ext h
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    exact ⟨⟨x, by simpa using hx⟩, rfl⟩
  exact
    { toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩
      map_rel_iff' := by
        intro u v
        have hu := u.2
        have hv := v.2
        simp only [Equiv.ofBijective_apply, SimpleGraph.Subgraph.coe_adj,
          SimpleGraph.Subgraph.deleteVerts_adj, SimpleGraph.Subgraph.top_adj,
          SimpleGraph.Subgraph.verts_top, Set.mem_univ, true_and, f]
        simp only [Multigraph.toSimple, SimpleGraph.fromRel_adj]
        rw [del_ends_iff, del_ends_iff]
        simp only [ne_eq, Subtype.ext_iff]
        tauto }

open SimpleGraph in
theorem edge_eq_of_mem {V : Type*} {S : SimpleGraph V} {H : S.Subgraph} (hH : H.IsMatching)
    {z z' : Sym2 V} (hz : z ∈ H.edgeSet) (hz' : z' ∈ H.edgeSet) {v : V} (hv : v ∈ z)
    (hv' : v ∈ z') : z = z' := by
  obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.mp hv
  obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp hv'
  rw [Subgraph.mem_edgeSet] at hz hz'
  rw [hH.eq_of_adj_left hz hz']

open SimpleGraph in
theorem verts_ncard {V : Type*} [Finite V] {S : SimpleGraph V} {H : S.Subgraph}
    (hH : H.IsMatching) : H.verts.ncard = 2 * H.edgeSet.ncard := by
  have hpair : ∀ e ∈ H.edgeSet, (e : Set V).ncard = 2 := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [Subgraph.mem_edgeSet] at he
      have hne : u ≠ v := (H.adj_sub he).ne
      have hset : ((s(u, v) : Sym2 V) : Set V) = {u, v} := by
        ext x; simp
      rw [hset, Set.ncard_pair hne]
  have hdisj : H.edgeSet.PairwiseDisjoint (fun e : Sym2 V => (e : Set V)) := by
    intro z hz z' hz' hne
    rw [Function.onFun, Set.disjoint_left]
    intro v hv hv'
    exact hne (edge_eq_of_mem hH hz hz' hv hv')
  have h2 : ∑ᶠ e ∈ H.edgeSet, (e : Set V).ncard = ∑ᶠ e ∈ H.edgeSet, (2 : ℕ) :=
    finsum_mem_congr rfl hpair
  rw [hH.verts_eq_biUnion_edgeSet,
    Set.Finite.ncard_biUnion (Set.toFinite _) (fun _ _ => Set.toFinite _) hdisj, h2,
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_const, smul_eq_mul,
    Set.ncard_eq_toFinset_card _ (Set.toFinite _), mul_comm]

open SimpleGraph in
theorem L1 {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E) (M : Set E)
    (hM : G.IsMatching M) :
    ∃ H : G.toSimple.Subgraph, H.IsMatching ∧ H.verts.ncard = 2 * M.ncard := by
  classical
  obtain ⟨hM1, hM2⟩ := hM
  let H : G.toSimple.Subgraph :=
    { verts := {v | ∃ e ∈ M, v ∈ G.ends e}
      Adj := fun u v => ∃ e ∈ M, G.ends e = s(u, v)
      adj_sub := by
        rintro u v ⟨e, he, huv⟩
        have hnd := hM1 e he
        rw [huv, Sym2.mk_isDiag_iff] at hnd
        simp only [Multigraph.toSimple, SimpleGraph.fromRel_adj]
        exact ⟨hnd, Or.inl ⟨e, huv⟩⟩
      edge_vert := by
        rintro u v ⟨e, he, huv⟩
        exact ⟨e, he, by rw [huv]; exact Sym2.mem_mk_left u v⟩
      symm := by
        constructor
        rintro u v ⟨e, he, huv⟩
        exact ⟨e, he, by rw [huv, Sym2.eq_swap]⟩ }
  have hH : H.IsMatching := by
    rintro v ⟨e, he, hv⟩
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hv
    refine ⟨w, ⟨e, he, hw⟩, ?_⟩
    rintro w' ⟨e', he', hw'⟩
    have hee : e' = e := hM2 e' he' e he v (by rw [hw']; exact Sym2.mem_mk_left _ _) hv
    rw [hee, hw] at hw'
    exact (Sym2.congr_right.mp hw').symm
  refine ⟨H, hH, ?_⟩
  rw [verts_ncard hH]
  congr 1
  have hes : H.edgeSet = G.ends '' M := by
    ext z
    induction z using Sym2.ind with
    | h u v =>
      rw [Subgraph.mem_edgeSet]
      constructor
      · rintro ⟨e, he, h⟩; exact ⟨e, he, h⟩
      · rintro ⟨e, he, h⟩; exact ⟨e, he, h⟩
  rw [hes, Set.InjOn.ncard_image]
  intro e he f hf hef
  obtain ⟨v, hv⟩ : ∃ v, v ∈ G.ends e :=
    Sym2.ind (f := fun z => ∃ v, v ∈ z) (fun a b => ⟨a, Sym2.mem_mk_left a b⟩) (G.ends e)
  exact hM2 e he f hf v hv (hef ▸ hv)

open SimpleGraph in
theorem L2 {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E) (H : G.toSimple.Subgraph)
    (hH : H.IsMatching) : ∃ M : Set E, G.IsMatching M ∧ 2 * M.ncard = H.verts.ncard := by
  classical
  have hex : ∀ z : H.edgeSet, ∃ e, G.ends e = z.1 := by
    rintro ⟨z, hz⟩
    induction z using Sym2.ind with
    | h u v =>
      rw [Subgraph.mem_edgeSet] at hz
      have h := H.adj_sub hz
      simp only [Multigraph.toSimple, SimpleGraph.fromRel_adj] at h
      rcases h.2 with ⟨e, he⟩ | ⟨e, he⟩
      · exact ⟨e, he⟩
      · exact ⟨e, by rw [he, Sym2.eq_swap]⟩
  choose c hc using hex
  have hcinj : Function.Injective c := by
    intro z z' h
    apply Subtype.ext
    rw [← hc z, ← hc z', h]
  refine ⟨Set.range c, ?_, ?_⟩
  · unfold Multigraph.IsMatching
    refine ⟨?_, ?_⟩
    · rintro _ ⟨z, rfl⟩
      rw [hc z]
      exact G.toSimple.not_isDiag_of_mem_edgeSet (H.edgeSet_subset z.2)
    · rintro _ ⟨z, rfl⟩ _ ⟨z', rfl⟩ v hv hv'
      rw [hc z] at hv
      rw [hc z'] at hv'
      have : z = z' := Subtype.ext (edge_eq_of_mem hH z.2 z'.2 hv hv')
      rw [this]
  · rw [Set.ncard_range_of_injective hcinj, verts_ncard hH, Nat.card_coe_set_eq]

/-- `S` padded with `d` new vertices adjacent to every other vertex. -/
def pad {V : Type*} (S : SimpleGraph V) (d : ℕ) : SimpleGraph (V ⊕ Fin d) where
  Adj x y := x ≠ y ∧ ∀ a b, x = Sum.inl a → y = Sum.inl b → S.Adj a b
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, fun a b ha hb => (h.2 b a hb ha).symm⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

theorem pad_adj_inl {V : Type*} {S : SimpleGraph V} {d : ℕ} {a b : V} :
    (pad S d).Adj (Sum.inl a) (Sum.inl b) ↔ S.Adj a b := by
  constructor
  · intro h; exact h.2 a b rfl rfl
  · intro h
    refine ⟨fun e => h.ne (Sum.inl_injective e), fun a' b' ha hb => ?_⟩
    rw [← Sum.inl_injective ha, ← Sum.inl_injective hb]
    exact h

theorem pad_adj_inr {V : Type*} {S : SimpleGraph V} {d : ℕ} {i : Fin d} {y : V ⊕ Fin d} :
    (pad S d).Adj (Sum.inr i) y ↔ Sum.inr i ≠ y := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun a b ha _ => by simp at ha⟩

/-- The inclusion of `S` into its padding. -/
def inlHom {V : Type*} (S : SimpleGraph V) (d : ℕ) : S →g pad S d :=
  ⟨Sum.inl, fun h => pad_adj_inl.2 h⟩

theorem ncard_inl_union {V : Type*} [Finite V] {d : ℕ} (A : Set V) :
    (Sum.inl '' A ∪ Set.range Sum.inr : Set (V ⊕ Fin d)).ncard = A.ncard + d := by
  rw [Set.ncard_union_eq, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_range_of_injective Sum.inr_injective, Nat.card_fin]
  rw [Set.disjoint_left]
  rintro _ ⟨a, _, rfl⟩ ⟨i, hi⟩
  simp at hi

open SimpleGraph in
theorem oc_pad {V : Type*} [Finite V] (S : SimpleGraph V) (d : ℕ) (A : Set V) :
    oc (pad S d) (Sum.inl '' A ∪ Set.range Sum.inr) = oc S A := by
  unfold oc
  symm
  apply iso_oc_ncard
  let f : ((⊤ : S.Subgraph).deleteVerts A).verts →
      ((⊤ : (pad S d).Subgraph).deleteVerts (Sum.inl '' A ∪ Set.range Sum.inr)).verts :=
    fun v => ⟨Sum.inl v.1, by
      have h := v.2
      simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_diff, Set.mem_univ,
        true_and] at h ⊢
      simp [h]⟩
  have hinj : Function.Injective f := fun x y h =>
    Subtype.ext (Sum.inl_injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rcases x with a | i
    · refine ⟨⟨a, ?_⟩, rfl⟩
      simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_diff, Set.mem_univ,
        true_and] at hx ⊢
      simpa using hx
    · exfalso
      simp at hx
  exact
    { toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩
      map_rel_iff' := by
        intro u v
        show ((⊤ : (pad S d).Subgraph).deleteVerts (Sum.inl '' A ∪ Set.range Sum.inr)).coe.Adj
            (f u) (f v) ↔ ((⊤ : S.Subgraph).deleteVerts A).coe.Adj u v
        have hu := u.2
        have hv := v.2
        simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_diff, Set.mem_univ,
          true_and] at hu hv
        simp only [Subgraph.coe_adj, Subgraph.deleteVerts_adj, Subgraph.top_adj,
          Subgraph.verts_top, Set.mem_univ, true_and, f, pad_adj_inl]
        simp [hu, hv, RelIso.coe_fn_mk, Equiv.ofBijective_apply, f, pad_adj_inl] }

open SimpleGraph in
theorem oc_pad_le_one {V : Type*} [Finite V] (S : SimpleGraph V) (d : ℕ) (u : Set (V ⊕ Fin d))
    (i : Fin d) (hi : Sum.inr i ∉ u) : oc (pad S d) u ≤ 1 := by
  unfold oc
  have hix : Sum.inr i ∈ ((⊤ : (pad S d).Subgraph).deleteVerts u).verts := by simp [hi]
  let z : ((⊤ : (pad S d).Subgraph).deleteVerts u).verts := ⟨Sum.inr i, hix⟩
  have hz : ∀ w, w ≠ z → ((⊤ : (pad S d).Subgraph).deleteVerts u).coe.Adj z w := by
    intro w hw
    have hw2 := w.2
    simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_diff, Set.mem_univ,
      true_and] at hw2
    simp only [Subgraph.coe_adj, Subgraph.deleteVerts_adj, Subgraph.top_adj, Subgraph.verts_top,
      Set.mem_univ, true_and, z]
    exact ⟨hi, hw2, pad_adj_inr.2 (fun h => hw (Subtype.ext h.symm))⟩
  have hp : ((⊤ : (pad S d).Subgraph).deleteVerts u).coe.Preconnected := by
    intro x y
    by_cases hx : x = z
    · by_cases hy : y = z
      · rw [hx, hy]
      · rw [hx]; exact (hz y hy).reachable
    · by_cases hy : y = z
      · rw [hy]; exact (hz x hx).reachable.symm
      · exact (hz x hx).reachable.symm.trans (hz y hy).reachable
  haveI := hp.subsingleton_connectedComponent
  exact (Set.ncard_le_one_iff (Set.toFinite _)).mpr (fun _ _ => Subsingleton.elim _ _)

open SimpleGraph in
theorem oc_parity {V : Type*} [Finite V] (S : SimpleGraph V) (A : Set V) :
    (oc S A + A.ncard + Nat.card V) % 2 = 0 := by
  have h1 := odd_ncard_oddComponents (G := ((⊤ : S.Subgraph).deleteVerts A).coe)
  have h2 : Nat.card ((⊤ : S.Subgraph).deleteVerts A).verts + A.ncard = Nat.card V := by
    rw [Nat.card_coe_set_eq, Subgraph.deleteVerts_verts, Subgraph.verts_top,
      ← Set.compl_eq_univ_diff, add_comm, Set.ncard_add_ncard_compl]
  rw [Nat.odd_iff, Nat.odd_iff] at h1
  unfold oc
  omega

open SimpleGraph in
theorem SW {V : Type*} [Finite V] (S : SimpleGraph V) (H : S.Subgraph) (hH : H.IsMatching)
    (A : Set V) : H.verts.ncard + oc S A ≤ Nat.card V + A.ncard := by
  classical
  set X : Set V := H.vertsᶜ with hX
  set d := Nat.card X with hd
  let e : X ≃ Fin d := Finite.equivFin X
  let s : Set (V ⊕ Fin d) := Sum.inl '' X
  let t : Set (V ⊕ Fin d) := Set.range Sum.inr
  have hst : Disjoint s t := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, _, rfl⟩ ⟨i, hi⟩
    simp at hi
  let φ : s ≃ t := (Equiv.Set.image Sum.inl X Sum.inl_injective).symm.trans
    (e.trans (Equiv.ofInjective Sum.inr Sum.inr_injective))
  have hadj : ∀ v : s, (pad S d).Adj v (φ v) := by
    intro v
    obtain ⟨w, hw⟩ := (φ v).2
    rw [← hw, (pad S d).adj_comm, pad_adj_inr]
    obtain ⟨a, _, ha⟩ := v.2
    rw [← ha]
    simp
  obtain ⟨M2, hM2v, hM2⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hst φ hadj
  let M1 := H.map (inlHom S d)
  have hM1 : M1.IsMatching := hH.map (inlHom S d) Sum.inl_injective
  have hM1v : M1.verts = Sum.inl '' H.verts := rfl
  have hdisj : Disjoint M1.support M2.support := by
    rw [hM1.support_eq_verts, hM2.support_eq_verts, hM1v, hM2v, Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hb
    rcases hb with ⟨b, hb, hab⟩ | ⟨i, hi⟩
    · have := Sum.inl_injective hab
      subst this
      exact hb ha
    · simp at hi
  have hP : (M1 ⊔ M2).IsPerfectMatching := by
    refine ⟨hM1.sup hM2 hdisj, ?_⟩
    intro x
    rw [Subgraph.verts_sup, hM1v, hM2v]
    rcases x with a | i
    · by_cases ha : a ∈ H.verts
      · exact Or.inl ⟨a, ha, rfl⟩
      · exact Or.inr (Or.inl ⟨a, ha, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
  have hnv := not_isTutteViolator_of_isPerfectMatching hP (Sum.inl '' A ∪ Set.range Sum.inr)
  unfold IsTutteViolator at hnv
  push_neg at hnv
  have h1 := ncard_inl_union (d := d) A
  have h2 : oc S A ≤ A.ncard + d := by
    rw [← oc_pad S d A, ← h1]
    exact hnv
  have h3 : H.verts.ncard + d = Nat.card V := by
    rw [hd, Nat.card_coe_set_eq, hX, Set.ncard_add_ncard_compl]
  omega

open SimpleGraph in
theorem SS {V : Type*} [Finite V] (S : SimpleGraph V) :
    ∃ H : S.Subgraph, H.IsMatching ∧ ∃ A : Set V, Nat.card V + A.ncard ≤ H.verts.ncard + oc S A := by
  classical
  haveI := Fintype.ofFinite V
  obtain ⟨A₀, -, hA₀⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Set V))
    Finset.univ_nonempty (fun A => oc S A - A.ncard)
  set d := (Finset.univ : Finset (Set V)).sup (fun A => oc S A - A.ncard) with hd
  have hle : ∀ A : Set V, oc S A - A.ncard ≤ d := fun A =>
    Finset.le_sup (f := fun A => oc S A - A.ncard) (Finset.mem_univ A)
  have hpar0 : (Nat.card V + d) % 2 = 0 := by
    have h1 := oc_parity S A₀
    have h2 := oc_parity S ∅
    have h3 := hle ∅
    rw [Set.ncard_empty] at h2 h3
    omega
  have hnv : ∀ u, ¬ (pad S d).IsTutteViolator u := by
    intro u hu
    unfold IsTutteViolator at hu
    by_cases hall : ∀ i : Fin d, Sum.inr i ∈ u
    · set A := Sum.inl ⁻¹' u with hA
      have hu' : u = Sum.inl '' A ∪ Set.range Sum.inr := by
        ext x
        rcases x with a | i
        · simp [hA]
        · simp [hall i]
      rw [hu'] at hu
      have h1 := ncard_inl_union (d := d) A
      have h2 := oc_pad S d A
      unfold oc at h2
      rw [h1, h2] at hu
      have := hle A
      unfold oc at this
      omega
    · push_neg at hall
      obtain ⟨i, hi⟩ := hall
      have h1 := oc_pad_le_one S d u i hi
      unfold oc at h1
      have hu0 : u = ∅ := by
        have : u.ncard = 0 := by omega
        exact (Set.ncard_eq_zero (Set.toFinite u)).mp this
      subst hu0
      have key := odd_ncard_oddComponents
        (G := ((⊤ : (pad S d).Subgraph).deleteVerts (∅ : Set (V ⊕ Fin d))).coe)
      rw [Nat.odd_iff, Nat.odd_iff] at key
      have hn : Nat.card ((⊤ : (pad S d).Subgraph).deleteVerts (∅ : Set (V ⊕ Fin d))).verts =
          Nat.card V + d := by
        rw [Nat.card_coe_set_eq, Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.diff_empty,
          Set.ncard_univ, Nat.card_sum, Nat.card_fin]
      rw [hn] at key
      rw [Set.ncard_empty] at hu
      have := key.mp (by omega)
      omega
  obtain ⟨P, hP⟩ := (SimpleGraph.tutte (G := pad S d)).mpr hnv
  let H : S.Subgraph :=
    { verts := {v | ∃ w, P.Adj (Sum.inl v) (Sum.inl w)}
      Adj := fun v w => P.Adj (Sum.inl v) (Sum.inl w)
      adj_sub := by
        intro v w h
        exact pad_adj_inl.mp (P.adj_sub h)
      edge_vert := by
        intro v w h
        exact ⟨w, h⟩
      symm := by
        constructor
        intro v w h
        exact h.symm }
  have hH : H.IsMatching := by
    intro v hv
    obtain ⟨w, hw⟩ := hv
    refine ⟨w, hw, fun w' hw' => ?_⟩
    exact Sum.inl_injective (hP.1.eq_of_adj_left hw' hw)
  have hcount : Nat.card V ≤ H.verts.ncard + d := by
    have hex : ∀ y : ↥(H.verts)ᶜ, ∃ i : Fin d, P.Adj (Sum.inl y.1) (Sum.inr i) := by
      intro y
      obtain ⟨w, hw, -⟩ := Subgraph.isPerfectMatching_iff.mp hP (Sum.inl y.1)
      rcases w with a | i
      · exact (y.2 ⟨a, hw⟩).elim
      · exact ⟨i, hw⟩
    choose g hg using hex
    have hginj : Function.Injective g := by
      intro y y' h
      have h2 := hg y'
      rw [← h] at h2
      exact Subtype.ext (Sum.inl_injective (hP.1.eq_of_adj_right (hg y) h2))
    have h5 := Nat.card_le_card_of_injective g hginj
    rw [Nat.card_fin, Nat.card_coe_set_eq] at h5
    have h4 := Set.ncard_add_ncard_compl H.verts
    omega
  refine ⟨H, hH, ?_⟩
  by_cases hd0 : d = 0
  · exact ⟨∅, by rw [Set.ncard_empty]; omega⟩
  · exact ⟨A₀, by omega⟩

end TBAux

open TBAux in
open CombOpt.TutteBerge in
theorem solution {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E) :
    ∃ m : ℚ,
      IsGreatest {r : ℚ | ∃ M : Set E, G.IsMatching M ∧ r = (M.ncard : ℚ)} m ∧
      IsLeast {r : ℚ | ∃ A : Set V, r = G.tutteBergeBound A} m := by
  obtain ⟨H, hH, A, hA⟩ := SS G.toSimple
  obtain ⟨M, hM, hMc⟩ := L2 G H hH
  have heq : H.verts.ncard + oc G.toSimple A = Nat.card V + A.ncard :=
    le_antisymm (SW _ H hH A) hA
  refine ⟨M.ncard, ⟨⟨M, hM, rfl⟩, ?_⟩, ⟨⟨A, ?_⟩, ?_⟩⟩
  · rintro r ⟨M', hM', rfl⟩
    obtain ⟨H', hH', hc⟩ := L1 G M' hM'
    have h1 := SW _ H' hH' A
    have h2 : M'.ncard ≤ M.ncard := by omega
    exact_mod_cast h2
  · unfold Multigraph.tutteBergeBound
    rw [oc_eq]
    have h3 : (2 * M.ncard : ℚ) + (oc G.toSimple A : ℚ) = (Nat.card V : ℚ) + (A.ncard : ℚ) := by
      exact_mod_cast (by omega : 2 * M.ncard + oc G.toSimple A = Nat.card V + A.ncard)
    linarith
  · rintro r ⟨B, rfl⟩
    unfold Multigraph.tutteBergeBound
    rw [oc_eq]
    have h4 := SW _ H hH B
    have h3 : (2 * M.ncard : ℚ) + (oc G.toSimple B : ℚ) ≤ (Nat.card V : ℚ) + (B.ncard : ℚ) := by
      exact_mod_cast (by omega : 2 * M.ncard + oc G.toSimple B ≤ Nat.card V + B.ncard)
    linarith
