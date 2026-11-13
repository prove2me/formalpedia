-- Prove2me | solution 1 for CombOpt.SpanningTree.mst_charVec_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T07:39:29.600664+00:00
-- url     : https://prove2.me/submissions/8e4f6047-4adc-4a5a-bf38-de9f4458fa06

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsMST
import Definitions.Def_CombOpt_SpanningTree_Graph_SpanningTreeLPOptimal

set_option autoImplicit false

namespace CombOpt.SpanningTree.A8AUX

variable {V E : Type*} {G : Graph V E}

@[simp] lemma edges_nil (v : V) : (Graph.Walk.nil (G := G) v).edges = [] := rfl
@[simp] lemma edges_cons {u v w : V} (e : E) (h : G.ends e = s(u, v)) (p : G.Walk v w) :
    (Graph.Walk.cons e h p).edges = e :: p.edges := rfl
@[simp] lemma support_nil (v : V) : (Graph.Walk.nil (G := G) v).support = [v] := rfl
@[simp] lemma support_cons {u v w : V} (e : E) (h : G.ends e = s(u, v)) (p : G.Walk v w) :
    (Graph.Walk.cons e h p).support = u :: p.support := rfl

def wapp : {u v w : V} → G.Walk u v → G.Walk v w → G.Walk u w
  | _, _, _, .nil _, q => q
  | _, _, _, .cons e h p, q => .cons e h (wapp p q)

@[simp] lemma wapp_edges : ∀ {u v w : V} (p : G.Walk u v) (q : G.Walk v w),
    (wapp p q).edges = p.edges ++ q.edges
  | _, _, _, .nil _, q => rfl
  | _, _, _, .cons e h p, q => by simp [wapp, wapp_edges p q]

lemma exists_rev : ∀ {u v : V} (p : G.Walk u v), ∃ q : G.Walk v u, ∀ e, e ∈ q.edges ↔ e ∈ p.edges
  | _, _, .nil _ => ⟨.nil _, by simp⟩
  | _, _, .cons e h p => by
      obtain ⟨q, hq⟩ := exists_rev p
      refine ⟨wapp q (.cons e (h.trans Sym2.eq_swap) (.nil _)), ?_⟩
      intro f
      simp only [wapp_edges, edges_cons, edges_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, hq]
      exact or_comm

def Conn (G : Graph V E) (F : Finset E) (u v : V) : Prop :=
  ∃ p : G.Walk u v, ∀ e ∈ p.edges, e ∈ F

lemma conn_refl (F : Finset E) (u : V) : Conn G F u u := ⟨.nil u, by simp⟩

lemma conn_symm {F : Finset E} {u v : V} (h : Conn G F u v) : Conn G F v u := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := exists_rev p
  exact ⟨q, fun e he => hp e ((hq e).1 he)⟩

lemma conn_trans {F : Finset E} {u v w : V} (h1 : Conn G F u v) (h2 : Conn G F v w) :
    Conn G F u w := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  refine ⟨wapp p q, fun e he => ?_⟩
  rw [wapp_edges, List.mem_append] at he
  exact he.elim (hp e) (hq e)

lemma conn_mono {F F' : Finset E} (hF : F ⊆ F') {u v : V} (h : Conn G F u v) : Conn G F' u v := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun e he => hF (hp e he)⟩

lemma conn_edge {F : Finset E} {e : E} (he : e ∈ F) {u v : V} (h : G.ends e = s(u, v)) :
    Conn G F u v :=
  ⟨.cons e h (.nil v), by simp [he]⟩

lemma conn_of_walk {F F' : Finset E}
    (hF : ∀ e ∈ F, ∀ a b : V, G.ends e = s(a, b) → Conn G F' a b) :
    ∀ {u v : V} (p : G.Walk u v), (∀ e ∈ p.edges, e ∈ F) → Conn G F' u v
  | _, _, .nil _, _ => conn_refl _ _
  | _, _, .cons e h p, hp => conn_trans (hF e (hp e (by simp)) _ _ h)
      (conn_of_walk hF p (fun f hf => hp f (by simp [hf])))

lemma start_mem : ∀ {u v : V} (p : G.Walk u v), u ∈ p.support
  | _, _, .nil _ => by simp
  | _, _, .cons _ _ _ => by simp

lemma ends_mem_support : ∀ {u v : V} (p : G.Walk u v) (e : E), e ∈ p.edges →
    ∀ a ∈ G.ends e, a ∈ p.support
  | _, _, .nil _, e, he, _, _ => by simp at he
  | _, _, .cons f h p, e, he, a, ha => by
      simp only [edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · rw [h, Sym2.mem_iff] at ha
        rcases ha with rfl | rfl
        · simp
        · simp [start_mem p]
      · simp [ends_mem_support p e he a ha]

lemma edges_nodup_of_support_nodup : ∀ {u v : V} (p : G.Walk u v), p.support.Nodup →
    p.edges.Nodup
  | _, _, .nil _, _ => by simp
  | _, _, .cons e h p, hs => by
      rw [support_cons, List.nodup_cons] at hs
      rw [edges_cons, List.nodup_cons]
      refine ⟨fun he => hs.1 ?_, edges_nodup_of_support_nodup p hs.2⟩
      exact ends_mem_support p e he _ (by rw [h]; exact Sym2.mem_mk_left _ _)

lemma exists_suffix : ∀ {u v : V} (p : G.Walk u v) (x : V), x ∈ p.support →
    ∃ q : G.Walk x v, q.support <:+ p.support ∧ q.edges <:+ p.edges
  | _, _, .nil _, x, hx => by
      simp at hx; subst hx; exact ⟨.nil _, List.suffix_refl _, List.suffix_refl _⟩
  | u, _, .cons e h p, x, hx => by
      by_cases hxu : x = u
      · subst hxu; exact ⟨.cons e h p, List.suffix_refl _, List.suffix_refl _⟩
      · have : x ∈ p.support := by simpa [hxu] using hx
        obtain ⟨q, h1, h2⟩ := exists_suffix p x this
        exact ⟨q, h1.trans (List.suffix_cons _ _), h2.trans (List.suffix_cons _ _)⟩

lemma exists_nodup : ∀ {u v : V} (p : G.Walk u v), ∃ q : G.Walk u v, q.support.Nodup ∧
    (∀ e ∈ q.edges, e ∈ p.edges) ∧ q.edges.length ≤ p.edges.length
  | _, _, .nil v => ⟨.nil v, by simp, by simp, le_rfl⟩
  | u, _, .cons e h p => by
      obtain ⟨q, hq1, hq2, hq3⟩ := exists_nodup p
      by_cases hu : u ∈ q.support
      · obtain ⟨r, hr1, hr2⟩ := exists_suffix q u hu
        refine ⟨r, hr1.sublist.nodup hq1, fun f hf => ?_, ?_⟩
        · simp [hq2 f (hr2.subset hf)]
        · have := hr2.sublist.length_le
          simp only [edges_cons, List.length_cons]
          omega
      · refine ⟨.cons e h q, ?_, ?_, ?_⟩
        · simp [hu, hq1]
        · intro f hf
          simp only [edges_cons, List.mem_cons] at hf ⊢
          rcases hf with hf | hf
          · exact Or.inl hf
          · exact Or.inr (hq2 f hf)
        · simp [hq3]

lemma support_eq : ∀ {u v : V} (p : G.Walk u v), ∃ l : List V, p.support = l ++ [v]
  | _, _, .nil v => ⟨[], rfl⟩
  | u, _, .cons e h p => by
      obtain ⟨l, hl⟩ := support_eq p
      exact ⟨u :: l, by simp [hl]⟩

lemma split_at : ∀ {u v : V} (p : G.Walk u v) (e : E), e ∈ p.edges →
    ∃ (x y : V) (p1 : G.Walk u x) (p2 : G.Walk y v), G.ends e = s(x, y) ∧
      p.edges = p1.edges ++ e :: p2.edges
  | _, _, .nil _, e, he => by simp at he
  | _, _, .cons f h p, e, he => by
      by_cases hef : e = f
      · subst hef; exact ⟨_, _, .nil _, p, h, by simp⟩
      · have : e ∈ p.edges := by simpa [hef] using he
        obtain ⟨x, y, p1, p2, hxy, hp⟩ := split_at p e this
        exact ⟨x, y, .cons f h p1, p2, hxy, by simp [hp]⟩

lemma first_exit (P : V → Prop) : ∀ {u v : V} (p : G.Walk u v), P u → ¬ P v →
    ∃ (x y : V) (f : E) (p1 : G.Walk u x) (p2 : G.Walk y v), G.ends f = s(x, y) ∧ P x ∧
      ¬ P y ∧ p.edges = p1.edges ++ f :: p2.edges
  | _, _, .nil _, hu, hv => absurd hu hv
  | _, _, .cons (v := b) f h p, hu, hv => by
      by_cases hb : P b
      · obtain ⟨x, y, g, p1, p2, hg, hx, hy, hp⟩ := first_exit P p hb hv
        exact ⟨x, y, g, .cons f h p1, p2, hg, hx, hy, by simp [hp]⟩
      · exact ⟨_, _, f, .nil _, p, h, hu, hb, by simp⟩

/-- A forest has no edge whose ends are joined in the forest minus that edge. -/
lemma not_conn_erase [DecidableEq E] {F : Finset E} (hF : G.IsForest F) {e : E} (he : e ∈ F) {u v : V}
    (h : G.ends e = s(u, v)) (hc : Conn G (F.erase e) u v) : False := by
  obtain ⟨p, hp⟩ := hc
  obtain ⟨q, hq1, hq2, -⟩ := exists_nodup p
  apply hF
  refine ⟨v, .cons e (h.trans Sym2.eq_swap) q, ⟨?_, ?_, by simp⟩, ?_⟩
  · simp only [edges_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, edges_nodup_of_support_nodup q hq1⟩
    have := hp e (hq2 e hm)
    simp at this
  · obtain ⟨l, hl⟩ := support_eq q
    rw [support_cons, hl, ← List.cons_append, List.dropLast_concat]
    rw [hl] at hq1
    have := List.nodup_append_comm.1 hq1
    simpa using this
  · intro f hf
    simp only [edges_cons, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact he
    · exact Finset.mem_of_mem_erase (hp f (hq2 f hf))

/-- A circuit inside `F` yields an edge of `F` whose ends are joined in `F` minus it. -/
lemma conn_erase_of_circuit [DecidableEq E] {F : Finset E} {w : V} (p : G.Walk w w) (hp : G.IsCircuit p)
    (hF : ∀ e ∈ p.edges, e ∈ F) :
    ∃ e ∈ F, ∃ a b : V, G.ends e = s(a, b) ∧ Conn G (F.erase e) a b := by
  obtain ⟨hnd, -, hlen⟩ := hp
  cases p with
  | nil => simp at hlen
  | cons e h q =>
    refine ⟨e, hF e (by simp), _, _, h, conn_symm ⟨q, fun f hf => ?_⟩⟩
    simp only [edges_cons, List.nodup_cons] at hnd
    rw [Finset.mem_erase]
    exact ⟨fun hfe => hnd.1 (hfe ▸ hf), hF f (by simp [hf])⟩


lemma ends_exists (e : E) : ∃ a b, G.ends e = s(a, b) :=
  Sym2.ind (f := fun z => ∃ a b, z = s(a, b)) (fun a b => ⟨a, b, rfl⟩) (G.ends e)

lemma conn_of_mem_ends {A : Finset E} {e : E} (he : e ∈ A) {a b : V} (ha : a ∈ G.ends e)
    (hb : b ∈ G.ends e) : Conn G A a b := by
  obtain ⟨p, q, hpq⟩ := ends_exists (G := G) e
  have hc := conn_edge he hpq
  rw [hpq, Sym2.mem_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  all_goals first | exact conn_refl _ _ | exact hc | exact conn_symm hc

lemma forest_mono {F F' : Finset E} (h : F ⊆ F') (hF : G.IsForest F') : G.IsForest F :=
  fun ⟨v, p, hp, hpF⟩ => hF ⟨v, p, hp, fun e he => h (hpF e he)⟩

lemma spanning_of {T T' : Finset E} (hT : G.SpanConnected T)
    (h : ∀ e ∈ T, ∀ a b : V, G.ends e = s(a, b) → Conn G T' a b) : G.SpanConnected T' :=
  fun u v => by
    obtain ⟨p, hp⟩ := hT u v
    exact conn_of_walk h p hp

/-! ### L5: a connected vertex set needs `|C| - 1` edges -/

noncomputable def dist (G : Graph V E) (B : Finset E) (r x : V) : ℕ :=
  sInf {n | ∃ p : G.Walk x r, (∀ e ∈ p.edges, e ∈ B) ∧ p.edges.length = n}

lemma dist_spec {B : Finset E} {r x : V} (h : Conn G B x r) :
    ∃ p : G.Walk x r, (∀ e ∈ p.edges, e ∈ B) ∧ p.edges.length = dist G B r x := by
  obtain ⟨p, hp⟩ := h
  exact Nat.sInf_mem (s := {n | ∃ p : G.Walk x r, (∀ e ∈ p.edges, e ∈ B) ∧ p.edges.length = n})
    ⟨_, p, hp, rfl⟩

lemma dist_le {B : Finset E} {r x : V} (p : G.Walk x r) (hp : ∀ e ∈ p.edges, e ∈ B) :
    dist G B r x ≤ p.edges.length := Nat.sInf_le ⟨p, hp, rfl⟩

lemma exists_step {B : Finset E} {r v : V} (h : Conn G B v r) (hv : v ≠ r) :
    ∃ e v', G.ends e = s(v, v') ∧ e ∈ B ∧ dist G B r v' < dist G B r v := by
  obtain ⟨p, hp, hl⟩ := dist_spec h
  cases p with
  | nil => exact absurd rfl hv
  | cons e h q =>
    refine ⟨e, _, h, hp e (by simp), ?_⟩
    have := dist_le q (fun f hf => hp f (by simp [hf]))
    simp only [edges_cons, List.length_cons] at hl
    omega

lemma card_le_conn {B : Finset E} (C : Finset V) [DecidablePred (fun e => ∃ a ∈ G.ends e, a ∈ C)]
    {r : V} (hr : r ∈ C) (hC : ∀ v ∈ C, Conn G B v r) :
    C.card ≤ (B.filter (fun e => ∃ a ∈ G.ends e, a ∈ C)).card + 1 := by
  classical
  have key : (C.erase r).card ≤ (B.filter (fun e => ∃ a ∈ G.ends e, a ∈ C)).card := by
    apply Finset.card_le_card_of_forall_subsingleton
      (fun v e => ∃ v', G.ends e = s(v, v') ∧ e ∈ B ∧ dist G B r v' < dist G B r v)
    · intro v hv
      rw [Finset.mem_erase] at hv
      obtain ⟨e, v', h1, h2, h3⟩ := exists_step (hC v hv.2) hv.1
      refine ⟨e, ?_, v', h1, h2, h3⟩
      rw [Finset.mem_filter]
      exact ⟨h2, v, by rw [h1]; exact Sym2.mem_mk_left _ _, hv.2⟩
    · intro e _ v hv w hw
      obtain ⟨-, v', hv1, -, hv3⟩ := hv
      obtain ⟨-, w', hw1, -, hw3⟩ := hw
      have h := hv1.symm.trans hw1
      rw [Sym2.eq_iff] at h
      rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact h1
      · subst h1 h2
        exfalso
        omega
  have := Finset.card_erase_of_mem hr
  have : 0 < C.card := Finset.card_pos.2 ⟨r, hr⟩
  omega

/-! ### L6: a forest has at most `|S| - 1` edges inside `S` -/

open Classical in
lemma ncomp_le [DecidableEq E] (S : Finset V) :
    ∀ F : Finset E, G.IsForest F → (∀ e ∈ F, ∀ a ∈ G.ends e, a ∈ S) →
      F.card + (S.image (fun v => S.filter (Conn G F v))).card ≤ S.card := by
  intro F
  induction F using Finset.induction_on with
  | empty => intro _ _; simpa using Finset.card_image_le
  | insert e F he ih =>
    intro hF hS
    have ih' := ih (forest_mono (Finset.subset_insert _ _) hF)
      (fun f hf => hS f (Finset.mem_insert_of_mem hf))
    obtain ⟨a, b, hab⟩ := ends_exists (G := G) e
    have haS : a ∈ S :=
      hS e (Finset.mem_insert_self _ _) a (by rw [hab]; exact Sym2.mem_mk_left _ _)
    have hbS : b ∈ S :=
      hS e (Finset.mem_insert_self _ _) b (by rw [hab]; exact Sym2.mem_mk_right _ _)
    have hnc : ¬ Conn G F a b := fun hc =>
      not_conn_erase hF (Finset.mem_insert_self _ _) hab (by rwa [Finset.erase_insert he])
    let ψ : Finset V → Finset V := fun X => S.filter (fun w => ∃ x ∈ X, Conn G (insert e F) x w)
    have hcl : ∀ v ∈ S, ψ (S.filter (Conn G F v)) = S.filter (Conn G (insert e F) v) := by
      intro v hv
      ext w
      simp only [ψ, Finset.mem_filter]
      constructor
      · rintro ⟨hw, x, ⟨-, hx⟩, hxw⟩
        exact ⟨hw, conn_trans (conn_mono (Finset.subset_insert _ _) hx) hxw⟩
      · rintro ⟨hw, h⟩
        exact ⟨hw, v, ⟨hv, conn_refl _ _⟩, h⟩
    have himg : S.image (fun v => S.filter (Conn G (insert e F) v)) =
        (S.image (fun v => S.filter (Conn G F v))).image ψ := by
      rw [Finset.image_image]
      exact Finset.image_congr (fun v hv => (hcl v hv).symm)
    have hlt : ((S.image (fun v => S.filter (Conn G F v))).image ψ).card <
        (S.image (fun v => S.filter (Conn G F v))).card := by
      refine lt_of_le_of_ne Finset.card_image_le (fun heq => ?_)
      rw [Finset.card_image_iff] at heq
      have hab' : Conn G (insert e F) a b := conn_edge (Finset.mem_insert_self _ _) hab
      have h1 : ψ (S.filter (Conn G F a)) = ψ (S.filter (Conn G F b)) := by
        rw [hcl a haS, hcl b hbS]
        ext w
        simp only [Finset.mem_filter]
        exact ⟨fun ⟨hw, h⟩ => ⟨hw, conn_trans (conn_symm hab') h⟩,
          fun ⟨hw, h⟩ => ⟨hw, conn_trans hab' h⟩⟩
      have h2 := heq (Finset.mem_coe.2 (Finset.mem_image_of_mem _ haS))
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hbS)) h1
      have hb : b ∈ S.filter (Conn G F b) := Finset.mem_filter.2 ⟨hbS, conn_refl _ _⟩
      rw [← h2, Finset.mem_filter] at hb
      exact hnc hb.2
    rw [himg, Finset.card_insert_of_notMem he]
    omega

lemma forest_card [Fintype E] [DecidableEq E] {F : Finset E} (hF : G.IsForest F) {S : Finset V}
    (hS : S.Nonempty) : ((G.gamma S).filter (· ∈ F)).card + 1 ≤ S.card := by
  classical
  have h := ncomp_le S ((G.gamma S).filter (· ∈ F))
    (forest_mono (fun e he => (Finset.mem_filter.1 he).2) hF)
    (fun e he => by
      have := (Finset.mem_filter.1 he).1
      simp only [Graph.gamma, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this)
  have : 0 < (S.image (fun v => S.filter (Conn G ((G.gamma S).filter (· ∈ F)) v))).card :=
    (hS.image _).card_pos
  omega

lemma tree_card [Fintype V] [Nonempty V] [Fintype E] [DecidableEq E] {T : Finset E}
    (hT : G.IsSpanningTree T) : T.card + 1 = Fintype.card V := by
  classical
  apply le_antisymm
  · have h := forest_card hT.2 (S := Finset.univ) Finset.univ_nonempty
    have : (G.gamma Finset.univ).filter (· ∈ T) = T := by
      ext e; simp [Graph.gamma]
    rw [this, Finset.card_univ] at h
    exact h
  · have h := card_le_conn (G := G) (B := T) Finset.univ (Finset.mem_univ (Classical.arbitrary V))
      (fun v _ => hT.1 v _)
    rw [Finset.card_univ] at h
    exact h.trans (Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) 1)

/-! ### L7: cycle property of an MST -/

lemma mst_cycle [Fintype V] [Nonempty V] [Fintype E] [DecidableEq E] {c : E → ℝ} {T : Finset E}
    (hT : G.IsMST c T) {e : E} {u v : V} (huv : G.ends e = s(u, v)) :
    Conn G (T.filter (fun f => c f ≤ c e)) u v := by
  classical
  by_contra hne
  have heT : e ∉ T := fun heT => hne (conn_edge (by simp [heT]) huv)
  obtain ⟨p0, hp0⟩ := hT.1.1 u v
  obtain ⟨p, hps, hpe, -⟩ := exists_nodup p0
  have hpT : ∀ f ∈ p.edges, f ∈ T := fun f hf => hp0 f (hpe f hf)
  obtain ⟨x, y, f, p1, p2, hf, hx, hy, hsplit⟩ :=
    first_exit (Conn G (T.filter (fun f => c f ≤ c e)) u) p (conn_refl _ _) hne
  have hfT : f ∈ T := hpT f (by rw [hsplit]; simp)
  have hfA : f ∉ T.filter (fun f => c f ≤ c e) := fun hfA => hy (conn_trans hx (conn_edge hfA hf))
  have hcf : c e < c f := by
    by_contra h
    push Not at h
    exact hfA (Finset.mem_filter.2 ⟨hfT, h⟩)
  have hnd : p.edges.Nodup := edges_nodup_of_support_nodup p hps
  have hfp2 : f ∉ p2.edges := by
    intro h
    rw [hsplit] at hnd
    have := (List.nodup_append.1 hnd).2.1
    exact (List.nodup_cons.1 this).1 h
  have hcard : (insert e (T.erase f)).card = T.card := by
    rw [Finset.card_insert_of_notMem (by simp [heT]), Finset.card_erase_of_mem hfT]
    have : 0 < T.card := Finset.card_pos.2 ⟨f, hfT⟩
    omega
  have hmem : ∀ g ∈ T, g ≠ f → g ∈ insert e (T.erase f) := fun g hg hgf =>
    Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hgf, hg⟩)
  have hAT' : T.filter (fun f => c f ≤ c e) ⊆ insert e (T.erase f) := fun g hg =>
    hmem g (Finset.mem_filter.1 hg).1 (fun h => hfA (h ▸ hg))
  have hxy : Conn G (insert e (T.erase f)) x y := by
    have h1 : Conn G (insert e (T.erase f)) x u := conn_mono hAT' (conn_symm hx)
    have h2 : Conn G (insert e (T.erase f)) u v := conn_edge (Finset.mem_insert_self _ _) huv
    have h3 : Conn G (insert e (T.erase f)) y v := ⟨p2, fun g hg =>
      hmem g (hpT g (by rw [hsplit]; simp [hg])) (fun h => hfp2 (h ▸ hg))⟩
    exact conn_trans h1 (conn_trans h2 (conn_symm h3))
  have hconn : G.SpanConnected (insert e (T.erase f)) := spanning_of hT.1.1 (fun g hg a b hab => by
    by_cases hgf : g = f
    · subst hgf
      rw [hf, Sym2.eq_iff] at hab
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy
      · exact conn_symm hxy
    · exact conn_edge (hmem g hg hgf) hab)
  have hforest : G.IsForest (insert e (T.erase f)) := by
    rintro ⟨w, q, hq, hqT⟩
    obtain ⟨g, hg, a, b, hab, hcab⟩ := conn_erase_of_circuit q hq hqT
    have hconn' : G.SpanConnected ((insert e (T.erase f)).erase g) :=
      spanning_of hconn (fun g' hg' a' b' hab' => by
        by_cases h : g' = g
        · subst h
          rw [hab, Sym2.eq_iff] at hab'
          rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hcab
          · exact conn_symm hcab
        · exact conn_edge (Finset.mem_erase.2 ⟨h, hg'⟩) hab')
    have h1 := card_le_conn (G := G) (B := (insert e (T.erase f)).erase g) Finset.univ
      (Finset.mem_univ (Classical.arbitrary V)) (fun v _ => hconn' v _)
    rw [Finset.card_univ] at h1
    have h2 := h1.trans (Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) 1)
    have h3 := Finset.card_erase_of_mem hg
    have h4 : 0 < (insert e (T.erase f)).card := Finset.card_pos.2 ⟨g, hg⟩
    have h5 := tree_card hT.1
    omega
  have hsum : ∑ g ∈ insert e (T.erase f), c g = ∑ g ∈ T, c g - c f + c e := by
    rw [Finset.sum_insert (by simp [heT]), ← Finset.add_sum_erase T c hfT]
    ring
  have := hT.2 _ ⟨hconn, hforest⟩
  linarith

/-! ### L8: `y(F_t) ≤ |T ∩ F_t|` -/

open Classical in
noncomputable def cls [Fintype V] (G : Graph V E) (A : Finset E) (v : V) : Finset V :=
  Finset.univ.filter (Conn G A v)

lemma mem_cls [Fintype V] {A : Finset E} {v w : V} : w ∈ cls G A v ↔ Conn G A v w := by
  simp [cls]

lemma cls_eq [Fintype V] {A : Finset E} {v w a b : V} (ha : a ∈ cls G A v) (hb : b ∈ cls G A w)
    (hab : Conn G A a b) : cls G A v = cls G A w := by
  rw [mem_cls] at ha hb
  have hvw : Conn G A v w := conn_trans ha (conn_trans hab (conn_symm hb))
  ext x
  rw [mem_cls, mem_cls]
  exact ⟨fun h => conn_trans (conn_symm hvw) h, fun h => conn_trans hvw h⟩

lemma cut_bound [Fintype V] [Nonempty V] [Fintype E] [DecidableEq E] {c : E → ℝ}
    {T : Finset E} (hT : G.IsMST c T) {y : E → ℝ} (hy : G.SpanningTreeLPFeasible y) (t : ℝ) :
    ∑ e ∈ Finset.univ.filter (fun e => c e ≤ t), y e ≤
      (((Finset.univ.filter (fun e => c e ≤ t)).filter (fun e => e ∈ T)).card : ℝ) := by
  classical
  set A := (Finset.univ.filter (fun e => c e ≤ t)).filter (fun e => e ∈ T) with hA
  have hsub : Finset.univ.filter (fun e => c e ≤ t) ⊆
      (Finset.univ.image (cls G A)).biUnion (fun C => G.gamma C) := by
    intro e he
    obtain ⟨u, v, huv⟩ := ends_exists (G := G) e
    have hce : c e ≤ t := (Finset.mem_filter.1 he).2
    have hc : Conn G A u v := conn_mono (fun f hf => by
        obtain ⟨hfT, hfc⟩ := Finset.mem_filter.1 hf
        rw [hA, Finset.mem_filter, Finset.mem_filter]
        exact ⟨⟨Finset.mem_univ _, by linarith⟩, hfT⟩) (mst_cycle hT huv)
    rw [Finset.mem_biUnion]
    refine ⟨cls G A u, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    simp only [Graph.gamma, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a ha
    rw [huv, Sym2.mem_iff] at ha
    rw [mem_cls]
    rcases ha with rfl | rfl
    · exact conn_refl _ _
    · exact hc
  have hdisj : ((Finset.univ.image (cls G A) : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint
      (fun C => G.gamma C) := by
    intro C1 hC1 C2 hC2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨v1, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hC1)
    obtain ⟨v2, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hC2)
    obtain ⟨a, b, hab⟩ := ends_exists (G := G) e
    have ha : a ∈ G.ends e := by rw [hab]; exact Sym2.mem_mk_left _ _
    simp only [Graph.gamma, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hne (cls_eq (h1 a ha) (h2 a ha) (conn_refl _ _))
  have h2 : ∑ e ∈ Finset.univ.filter (fun e => c e ≤ t), y e ≤
      ∑ C ∈ Finset.univ.image (cls G A), ∑ e ∈ G.gamma C, y e := by
    rw [← Finset.sum_biUnion hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hy.2.2 e)
  have h3 : ∑ C ∈ Finset.univ.image (cls G A), ∑ e ∈ G.gamma C, y e ≤
      ∑ C ∈ Finset.univ.image (cls G A), ((C.card : ℝ) - 1) := by
    apply Finset.sum_le_sum
    intro C hC
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hC
    exact hy.1 _ ⟨v, mem_cls.2 (conn_refl _ _)⟩
  have hdisj2 : ((Finset.univ.image (cls G A) : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint
      (fun C => A.filter (fun e => ∃ a ∈ G.ends e, a ∈ C)) := by
    intro C1 hC1 C2 hC2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨v1, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hC1)
    obtain ⟨v2, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hC2)
    obtain ⟨heA, a, ha, haC⟩ := Finset.mem_filter.1 h1
    obtain ⟨-, b, hb, hbC⟩ := Finset.mem_filter.1 h2
    exact hne (cls_eq haC hbC (conn_of_mem_ends heA ha hb))
  have h4 : ∑ C ∈ Finset.univ.image (cls G A), C.card ≤
      A.card + (Finset.univ.image (cls G A)).card := by
    have hle : ∀ C ∈ Finset.univ.image (cls G A),
        C.card ≤ (A.filter (fun e => ∃ a ∈ G.ends e, a ∈ C)).card + 1 := by
      intro C hC
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hC
      exact card_le_conn (cls G A v) (mem_cls.2 (conn_refl _ _))
        (fun w hw => conn_symm (mem_cls.1 hw))
    calc ∑ C ∈ Finset.univ.image (cls G A), C.card
        ≤ ∑ C ∈ Finset.univ.image (cls G A),
            ((A.filter (fun e => ∃ a ∈ G.ends e, a ∈ C)).card + 1) := Finset.sum_le_sum hle
      _ = ((Finset.univ.image (cls G A)).biUnion
            (fun C => A.filter (fun e => ∃ a ∈ G.ends e, a ∈ C))).card +
            (Finset.univ.image (cls G A)).card := by
          rw [Finset.sum_add_distrib, Finset.card_biUnion hdisj2]
          simp
      _ ≤ A.card + (Finset.univ.image (cls G A)).card := by
          gcongr
          exact Finset.biUnion_subset.2 (fun C _ => Finset.filter_subset _ _)
  have h5 : ∑ C ∈ Finset.univ.image (cls G A), ((C.card : ℝ) - 1) ≤ A.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : ((∑ C ∈ Finset.univ.image (cls G A), C.card : ℕ) : ℝ) ≤
        (A.card : ℝ) + (Finset.univ.image (cls G A)).card := by exact_mod_cast h4
    push_cast at this
    linarith
  linarith

/-! ### L9: Abel summation -/

lemma abel_sum {ι : Type*} [Fintype ι] : ∀ (n : ℕ) (c d : ι → ℝ),
    (Finset.univ.image c).card ≤ n → ∑ i, d i = 0 →
    (∀ t, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => c i ≤ t), d i) →
    ∑ i, c i * d i ≤ 0 := by
  intro n
  induction n with
  | zero =>
    intro c d hn _ _
    have h0 : (Finset.univ : Finset ι) = ∅ :=
      Finset.image_eq_empty.1 (Finset.card_eq_zero.1 (Nat.le_zero.1 hn))
    rw [h0, Finset.sum_empty]
  | succ n ih =>
    intro c d hn hd hD
    by_cases hne : (Finset.univ.image c).Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty, Finset.image_eq_empty] at hne
      rw [hne, Finset.sum_empty]
    obtain ⟨M, hMS, hMmax⟩ : ∃ M ∈ Finset.univ.image c, ∀ z ∈ Finset.univ.image c, z ≤ M :=
      ⟨_, Finset.max'_mem _ hne, fun z hz => Finset.le_max' _ z hz⟩
    by_cases h1 : ((Finset.univ.image c).erase M).Nonempty
    swap
    · have hall : ∀ i, c i = M := by
        intro i
        by_contra h
        exact h1 ⟨c i, Finset.mem_erase.2 ⟨h, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩⟩
      simp only [hall, ← Finset.mul_sum, hd, mul_zero, le_refl]
    obtain ⟨M2, hM2S, hM2max⟩ : ∃ M2 ∈ (Finset.univ.image c).erase M,
        ∀ z ∈ (Finset.univ.image c).erase M, z ≤ M2 :=
      ⟨_, Finset.max'_mem _ h1, fun z hz => Finset.le_max' _ z hz⟩
    have hM2M : M2 < M :=
      lt_of_le_of_ne (hMmax M2 (Finset.mem_of_mem_erase hM2S)) (Finset.ne_of_mem_erase hM2S)
    have hval : ∀ i, c i ≤ M2 ∨ c i = M := by
      intro i
      by_cases h : c i = M
      · exact Or.inr h
      · exact Or.inl (hM2max _ (Finset.mem_erase.2 ⟨h, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩))
    have himg : Finset.univ.image (fun i => min (c i) M2) ⊆ (Finset.univ.image c).erase M := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
      rcases hval i with h | h
      · rw [min_eq_left h]
        exact Finset.mem_erase.2 ⟨by linarith, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
      · rw [h, min_eq_right hM2M.le]
        exact hM2S
    have hcard : (Finset.univ.image (fun i => min (c i) M2)).card ≤ n := by
      have := Finset.card_le_card himg
      have h2 := Finset.card_erase_of_mem hMS
      omega
    have hD' : ∀ t, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => min (c i) M2 ≤ t), d i := by
      intro t
      by_cases ht : M2 ≤ t
      · have : Finset.univ.filter (fun i => min (c i) M2 ≤ t) = Finset.univ :=
          Finset.filter_true_of_mem (fun i _ => (min_le_right _ _).trans ht)
        rw [this, hd]
      · push Not at ht
        have : Finset.univ.filter (fun i => min (c i) M2 ≤ t) =
            Finset.univ.filter (fun i => c i ≤ t) := by
          apply Finset.filter_congr
          intro i _
          constructor
          · intro h
            rcases le_total (c i) M2 with h' | h'
            · rwa [min_eq_left h'] at h
            · rw [min_eq_right h'] at h
              linarith
          · intro h
            exact (min_le_left _ _).trans h
        rw [this]
        exact hD t
    have hih := ih (fun i => min (c i) M2) d hcard hd hD'
    have hsplit : ∑ i, c i * d i = ∑ i, min (c i) M2 * d i +
        (M - M2) * ∑ i ∈ Finset.univ.filter (fun i => ¬ c i ≤ M2), d i := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rcases hval i with h | h
      · rw [if_neg (not_not.2 h), min_eq_left h]
        ring
      · have h' : ¬ c i ≤ M2 := by rw [h]; linarith
        rw [if_pos h', h, min_eq_right hM2M.le]
        ring
    have hneg : ∑ i ∈ Finset.univ.filter (fun i => ¬ c i ≤ M2), d i ≤ 0 := by
      have := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => c i ≤ M2) d
      have := hD M2
      linarith
    have h3 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hM2M.le) hneg
    linarith

end CombOpt.SpanningTree.A8AUX

open CombOpt.SpanningTree in
theorem solution {V E : Type*} [Fintype V] [Nonempty V] [Fintype E] [DecidableEq E]
    (G : CombOpt.SpanningTree.Graph V E) (c : E → ℝ) (T : Finset E) (hT : G.IsMST c T) :
    G.SpanningTreeLPOptimal c (fun e => if e ∈ T then 1 else 0) := by
  have hcard := A8AUX.tree_card hT.1
  have feas : G.SpanningTreeLPFeasible (fun e => if e ∈ T then 1 else 0) := by
    refine ⟨fun S hS => ?_, ?_, fun e => by dsimp only; split_ifs <;> norm_num⟩
    · rw [Finset.sum_boole]
      have := A8AUX.forest_card hT.1.2 hS
      have h' : (((G.gamma S).filter (· ∈ T)).card : ℝ) + 1 ≤ S.card := by exact_mod_cast this
      linarith
    · rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
      have h' : (T.card : ℝ) + 1 = Fintype.card V := by exact_mod_cast hcard
      linarith
  refine ⟨feas, fun y hy => ?_⟩
  have hD : ∀ t, 0 ≤ ∑ e ∈ Finset.univ.filter (fun e => c e ≤ t),
      ((if e ∈ T then (1 : ℝ) else 0) - y e) := by
    intro t
    rw [Finset.sum_sub_distrib, Finset.sum_boole]
    have := A8AUX.cut_bound hT hy t
    linarith
  have hsum : ∑ e, ((if e ∈ T then (1 : ℝ) else 0) - y e) = 0 := by
    rw [Finset.sum_sub_distrib, feas.2.1, hy.2.1]
    ring
  have h1 := A8AUX.abel_sum _ c _ le_rfl hsum hD
  have h2 : ∑ e, c e * ((if e ∈ T then (1 : ℝ) else 0) - y e) =
      ∑ e, c e * (if e ∈ T then 1 else 0) - ∑ e, c e * y e := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  linarith
