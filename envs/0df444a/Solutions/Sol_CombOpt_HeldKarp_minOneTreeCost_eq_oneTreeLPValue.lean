-- Prove2me | solution 1 for CombOpt.HeldKarp.minOneTreeCost_eq_oneTreeLPValue
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:14:07.849885+00:00
-- url     : https://prove2.me/submissions/f076b537-b247-4125-a63a-7efa2c3e4e66

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_minOneTreeCost
import Definitions.Def_CombOpt_HeldKarp_Graph_oneTreeLPValue
import Theorems.Thm_CombOpt_HeldKarp_forest_polytope

/-! e7dcbdc1 working draft: reduction glue for (7.7).
Children (still hypotheses here): C1 = 1-tree incidence vectors are 1-tree-LP feasible;
C2a = spanning tree LP lower bound on G minus v1 (Edmonds). The v1 part (two cheapest edges)
and the cost split are proved below. -/

set_option autoImplicit false

namespace CombOpt.HeldKarp.E7

open CombOpt.HeldKarp Finset

section Aux
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
lemma ncomp_le [DecidableEq V] [DecidableEq E] (S : Finset V) :
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

lemma forest_card [Fintype E] [DecidableEq V] [DecidableEq E] {F : Finset E} (hF : G.IsForest F) {S : Finset V}
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
end Aux

lemma mem_gamma_iff {V E : Type*} [Fintype E] (G : Graph V E) (S : Finset V) (e : E) :
    e ∈ G.gamma S ↔ ∀ a ∈ G.ends e, a ∈ S := by
  classical
  simp [Graph.gamma]

lemma mem_cut_single_iff {V E : Type*} [Fintype E] (G : Graph V E) (v₁ : V) (e : E) :
    e ∈ G.cut {v₁} ↔ (v₁ ∈ G.ends e ∧ ∃ b ∈ G.ends e, b ≠ v₁) := by
  classical
  simp [Graph.cut]

/-- With no loop at `v₁`, the edges split into `γ(V \ {v₁})` and `δ(v₁)`. -/
lemma sum_split {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Graph V E) (v₁ : V) (hv₁ : ∀ e : E, G.ends e ≠ s(v₁, v₁)) (g : E → ℝ) :
    ∑ e, g e = ∑ e ∈ G.gamma (univ.erase v₁), g e + ∑ e ∈ G.cut {v₁}, g e := by
  have hdisj : Disjoint (G.gamma (univ.erase v₁)) (G.cut {v₁}) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    have := (mem_gamma_iff G _ e).1 h1 v₁ ((mem_cut_single_iff G v₁ e).1 h2).1
    simp at this
  have hcov : G.gamma (univ.erase v₁) ∪ G.cut {v₁} = univ := by
    ext e
    simp only [Finset.mem_union, mem_gamma_iff, mem_cut_single_iff, Finset.mem_univ, iff_true,
      Finset.mem_erase, ne_eq, and_true]
    have h := hv₁ e
    revert h
    generalize G.ends e = z
    induction z using Sym2.ind with
    | _ a b =>
      intro h
      simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left]
      by_cases ha : a = v₁ <;> by_cases hb : b = v₁
      · subst ha; subst hb; exact absurd rfl h
      · subst ha; right; exact ⟨Or.inl rfl, Or.inr hb⟩
      · subst hb; right; exact ⟨Or.inr rfl, Or.inl ha⟩
      · left; exact ⟨ha, hb⟩
  rw [← Finset.sum_union hdisj, hcov]

/-- The `v₁` part of (7.7): `0 ≤ x ≤ 1` on `C` with `x(C) = 2` costs at least the two
cheapest edges of `C`. -/
lemma two_cheapest {E : Type*} [DecidableEq E] (C : Finset E) (c x : E → ℝ)
    (hx : ∀ e ∈ C, 0 ≤ x e ∧ x e ≤ 1) (hs : ∑ e ∈ C, x e = 2) :
    ∃ e f, e ≠ f ∧ e ∈ C ∧ f ∈ C ∧ c e + c f ≤ ∑ g ∈ C, c g * x g := by
  have hC : C.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hs
  obtain ⟨e, he, hemin⟩ := C.exists_min_image c hC
  have h2 : ∑ g ∈ C, x g = x e + ∑ g ∈ C.erase e, x g := (Finset.add_sum_erase C _ he).symm
  have hC' : (C.erase e).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at h2
    linarith [(hx e he).2]
  obtain ⟨f, hf, hfmin⟩ := (C.erase e).exists_min_image c hC'
  refine ⟨e, f, (Finset.ne_of_mem_erase hf).symm, he, Finset.mem_of_mem_erase hf, ?_⟩
  have h1 : ∑ g ∈ C, c g * x g = c e * x e + ∑ g ∈ C.erase e, c g * x g :=
    (Finset.add_sum_erase C _ he).symm
  have h3 : ∑ g ∈ C.erase e, c f * x g ≤ ∑ g ∈ C.erase e, c g * x g :=
    Finset.sum_le_sum (fun g hg =>
      mul_le_mul_of_nonneg_right (hfmin g hg) (hx g (Finset.mem_of_mem_erase hg)).1)
  rw [← Finset.mul_sum] at h3
  have hef : c e ≤ c f := hemin f (Finset.mem_of_mem_erase hf)
  have hxe := hx e he
  have h4 : ∑ g ∈ C.erase e, x g = 2 - x e := by linarith
  rw [h4] at h3
  nlinarith [mul_nonneg (sub_nonneg.2 hef) (sub_nonneg.2 hxe.2)]

/-- LP value ≤ minimum 1-tree cost, given child C1. -/
theorem lp_le_min {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Graph V E) (v₁ : V) (c : E → ℝ)
    (h1 : ∀ J, G.IsOneTree v₁ J → G.OneTreeLPFeasible v₁ (fun e => if e ∈ J then 1 else 0)) :
    G.oneTreeLPValue c v₁ ≤ G.minOneTreeCost c v₁ := by
  unfold Graph.oneTreeLPValue Graph.minOneTreeCost
  refine le_iInf₂ (fun J hJ => ?_)
  refine (iInf₂_le (fun e => if e ∈ J then (1 : ℝ) else 0) (h1 J hJ)).trans (le_of_eq ?_)
  have hs : ∑ e, c e * (if e ∈ J then (1 : ℝ) else 0) = ∑ e ∈ J, c e := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hs]

/-- Minimum 1-tree cost ≤ LP value, given child C2a (spanning tree LP bound on `G \ v₁`). -/
theorem min_le_lp {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Graph V E) (v₁ : V) (hv₁ : ∀ e : E, G.ends e ≠ s(v₁, v₁)) (c : E → ℝ)
    (h2 : ∀ x : E → ℝ,
      (∀ S : Finset V, S.Nonempty → v₁ ∉ S → ∑ e ∈ G.gamma S, x e ≤ (S.card : ℝ) - 1) →
      (∑ e ∈ G.gamma (univ.erase v₁), x e = (Fintype.card V : ℝ) - 2) →
      (∀ e, 0 ≤ x e) →
      ∃ T, G.IsSpanningTreeDelete v₁ T ∧
        ∑ e ∈ T, c e ≤ ∑ e ∈ G.gamma (univ.erase v₁), c e * x e) :
    G.minOneTreeCost c v₁ ≤ G.oneTreeLPValue c v₁ := by
  unfold Graph.oneTreeLPValue Graph.minOneTreeCost
  refine le_iInf₂ (fun x hx => ?_)
  obtain ⟨h74, h75, h76, hcut⟩ := hx
  obtain ⟨T, hT, hTc⟩ := h2 x h74 h75 (fun e => (h76 e).1)
  obtain ⟨e, f, hef, he, hf, hcost⟩ := two_cheapest (G.cut {v₁}) c x (fun e _ => h76 e) hcut
  have heT : e ∉ T := fun h => hT.1 e h ((mem_cut_single_iff G v₁ e).1 he).1
  have hfT : f ∉ T := fun h => hT.1 f h ((mem_cut_single_iff G v₁ f).1 hf).1
  refine (iInf₂_le (insert e (insert f T)) ⟨e, f, T, hef, he, hf, hT, rfl⟩).trans ?_
  have hsum : ∑ g ∈ insert e (insert f T), c g = c e + c f + ∑ g ∈ T, c g := by
    rw [Finset.sum_insert (by simp [hef, heT]), Finset.sum_insert hfT]
    ring
  apply EReal.coe_le_coe_iff.mpr
  rw [hsum, sum_split G v₁ hv₁ (fun e => c e * x e)]
  linarith

/-- The parent (7.7) from children C1 and C2a. -/
theorem parent_of_children {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : Graph V E) (v₁ : V) (hv₁ : ∀ e : E, G.ends e ≠ s(v₁, v₁))
    (c : E → ℝ)
    (h1 : ∀ J, G.IsOneTree v₁ J → G.OneTreeLPFeasible v₁ (fun e => if e ∈ J then 1 else 0))
    (h2 : ∀ x : E → ℝ,
      (∀ S : Finset V, S.Nonempty → v₁ ∉ S → ∑ e ∈ G.gamma S, x e ≤ (S.card : ℝ) - 1) →
      (∑ e ∈ G.gamma (univ.erase v₁), x e = (Fintype.card V : ℝ) - 2) →
      (∀ e, 0 ≤ x e) →
      ∃ T, G.IsSpanningTreeDelete v₁ T ∧
        ∑ e ∈ T, c e ≤ ∑ e ∈ G.gamma (univ.erase v₁), c e * x e) :
    G.minOneTreeCost c v₁ = G.oneTreeLPValue c v₁ :=
  le_antisymm (min_le_lp G v₁ hv₁ c h2) (lp_le_min G v₁ c h1)

lemma ends_nonempty {V E : Type*} (G : Graph V E) (e : E) : ∃ a, a ∈ G.ends e := by
  induction G.ends e using Sym2.ind with
  | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩

/-- C2a from the (Proved, c776d601) forest polytope theorem `hfp` and the connectivity fact `hK2`. -/
theorem c2a_of_forest_polytope {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : Graph V E) (v₁ : V) (c : E → ℝ)
    (hfp : convexHull ℝ {x : E → ℝ | ∃ F : Finset E, G.IsForest F ∧ x = fun e => if e ∈ F then 1 else 0} =
      {x : E → ℝ | (∀ T : Finset V, T.Nonempty → ∑ e ∈ G.gamma T, x e ≤ (T.card : ℝ) - 1) ∧
        ∀ e : E, 0 ≤ x e})
    (hK2 : ∀ F : Finset E, G.IsForest F → F ⊆ G.gamma (univ.erase v₁) →
      F.card + 2 = Fintype.card V →
      ∀ u w : V, u ≠ v₁ → w ≠ v₁ → ∃ p : G.Walk u w, ∀ e ∈ p.edges, e ∈ F) :
    ∀ x : E → ℝ,
      (∀ S : Finset V, S.Nonempty → v₁ ∉ S → ∑ e ∈ G.gamma S, x e ≤ (S.card : ℝ) - 1) →
      (∑ e ∈ G.gamma (univ.erase v₁), x e = (Fintype.card V : ℝ) - 2) →
      (∀ e, 0 ≤ x e) →
      ∃ T, G.IsSpanningTreeDelete v₁ T ∧
        ∑ e ∈ T, c e ≤ ∑ e ∈ G.gamma (univ.erase v₁), c e * x e := by
  intro x h74 h75 hx0
  set Γ := G.gamma (univ.erase v₁) with hΓ
  have hcardV' : (univ.erase v₁).card + 1 = Fintype.card V := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v₁⟩
    omega
  have hgamma_empty : G.gamma (∅ : Finset V) = ∅ := by
    ext e
    simp only [mem_gamma_iff, Finset.notMem_empty, iff_false, not_forall]
    obtain ⟨a, ha⟩ := ends_nonempty G e
    exact ⟨a, ha, id⟩
  -- V' is nonempty
  have hV'ne : (univ.erase v₁).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.card_empty] at hcardV'
    rw [hΓ, h, hgamma_empty, Finset.sum_empty] at h75
    have : (Fintype.card V : ℝ) = 1 := by exact_mod_cast hcardV'.symm
    linarith
  -- x' := x restricted to Γ lies in the forest polytope
  set x' : E → ℝ := fun e => if e ∈ Γ then x e else 0 with hx'
  have hx'mem : x' ∈ convexHull ℝ {x : E → ℝ | ∃ F : Finset E, G.IsForest F ∧
      x = fun e => if e ∈ F then 1 else 0} := by
    rw [hfp]
    refine ⟨fun T hT => ?_, fun e => by simp only [hx']; split_ifs <;> simp [hx0]⟩
    have hsplit : ∑ e ∈ G.gamma T, x' e = ∑ e ∈ G.gamma (T.erase v₁), x e := by
      simp only [hx']
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext e
      simp only [Finset.mem_filter, hΓ, mem_gamma_iff, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro ⟨h1, h2⟩ a ha; exact ⟨h2 a ha, h1 a ha⟩
      · intro h; exact ⟨fun a ha => (h a ha).2, fun a ha => (h a ha).1⟩
    rw [hsplit]
    by_cases hne : (T.erase v₁).Nonempty
    · have h1 := h74 _ hne (Finset.notMem_erase v₁ T)
      have h2 : ((T.erase v₁).card : ℝ) ≤ T.card := by
        exact_mod_cast Finset.card_le_card (Finset.erase_subset v₁ T)
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, hgamma_empty, Finset.sum_empty]
      have : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
      linarith
  -- the weighted linear functional
  set M : ℝ := 1 + ∑ e ∈ Γ, |c e| * (1 + x e) with hM
  set φ : (E → ℝ) → ℝ := fun y => ∑ e ∈ Γ, (c e - M) * y e with hφ
  have hconc : ConcaveOn ℝ Set.univ φ := by
    refine ⟨convex_univ, fun y _ z _ a b _ _ _ => le_of_eq ?_⟩
    simp only [hφ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  obtain ⟨y, ⟨F, hF, rfl⟩, hy⟩ :=
    hconc.exists_le_of_mem_convexHull (Set.subset_univ _) hx'mem
  set F' := Γ.filter (· ∈ F) with hF'
  have hφF : φ (fun e => if e ∈ F then 1 else 0) = ∑ e ∈ F', c e - M * F'.card := by
    simp only [hφ, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hφx : φ x' = ∑ e ∈ Γ, c e * x e - M * ((Fintype.card V : ℝ) - 2) := by
    rw [← h75]
    simp only [hφ, hx']
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun e he => by rw [if_pos he]; ring)
  rw [hφF, hφx] at hy
  -- |F'| ≤ |V| - 2 from the forest polytope at V'
  have hF'le : F'.card + 2 ≤ Fintype.card V := by
    have hmem : (fun e => if e ∈ F then (1 : ℝ) else 0) ∈ convexHull ℝ {x : E → ℝ |
        ∃ F : Finset E, G.IsForest F ∧ x = fun e => if e ∈ F then 1 else 0} :=
      subset_convexHull ℝ _ ⟨F, hF, rfl⟩
    rw [hfp] at hmem
    have h := hmem.1 _ hV'ne
    rw [Finset.sum_boole] at h
    have h' : ((F'.card : ℕ) : ℝ) + 1 ≤ ((univ.erase v₁).card : ℝ) := by
      have : (Γ.filter (· ∈ F)).card = F'.card := rfl
      simp only [hΓ] at h this ⊢
      rw [← this]; linarith
    have : F'.card + 1 ≤ (univ.erase v₁).card := by exact_mod_cast h'
    omega
  -- bounds for the penalty argument
  have hcF : -(∑ e ∈ Γ, |c e|) ≤ ∑ e ∈ F', c e := by
    have h1 : ∑ e ∈ F', -|c e| ≤ ∑ e ∈ F', c e :=
      Finset.sum_le_sum (fun e _ => neg_abs_le (c e))
    have h2 : ∑ e ∈ F', |c e| ≤ ∑ e ∈ Γ, |c e| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun e _ _ => abs_nonneg (c e))
    rw [Finset.sum_neg_distrib] at h1
    linarith
  have hA : ∑ e ∈ Γ, |c e| + ∑ e ∈ Γ, c e * x e ≤ ∑ e ∈ Γ, |c e| * (1 + x e) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e _ => by
      have := mul_le_mul_of_nonneg_right (le_abs_self (c e)) (hx0 e)
      nlinarith)
  have hMpos : 0 ≤ M := by
    have : 0 ≤ ∑ e ∈ Γ, |c e| * (1 + x e) :=
      Finset.sum_nonneg (fun e _ => mul_nonneg (abs_nonneg _) (by linarith [hx0 e]))
    linarith
  have hk : F'.card + 2 = Fintype.card V := by
    by_contra hne
    have h3 : F'.card + 3 ≤ Fintype.card V := by omega
    have h3' : (F'.card : ℝ) ≤ (Fintype.card V : ℝ) - 3 := by
      have : ((F'.card + 3 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h3
      push_cast at this; linarith
    have := mul_le_mul_of_nonneg_left h3' hMpos
    nlinarith
  have hk' : (F'.card : ℝ) = (Fintype.card V : ℝ) - 2 := by
    have : ((F'.card + 2 : ℕ) : ℝ) = (Fintype.card V : ℝ) := by exact_mod_cast hk
    push_cast at this; linarith
  refine ⟨F', ⟨fun e he => ?_, hK2 F' ?_ (Finset.filter_subset _ _) hk, ?_⟩, ?_⟩
  · have := (mem_gamma_iff G _ e).1 (Finset.mem_filter.1 he).1
    intro hv
    simpa using this v₁ hv
  · rintro ⟨v, p, hp, hpF⟩
    exact hF ⟨v, p, hp, fun e he => (Finset.mem_filter.1 (hpF e he)).2⟩
  · rintro ⟨v, p, hp, hpF⟩
    exact hF ⟨v, p, hp, fun e he => (Finset.mem_filter.1 (hpF e he)).2⟩
  · rw [hk'] at hy
    linarith

section Final

variable {V E : Type*}

/-- K2: a forest inside `γ(V \ v₁)` with `|V| - 2` edges connects `V \ v₁`. -/
theorem k2 [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : Graph V E) (v₁ : V) :
    ∀ F : Finset E, G.IsForest F → F ⊆ G.gamma (univ.erase v₁) →
      F.card + 2 = Fintype.card V →
      ∀ u w : V, u ≠ v₁ → w ≠ v₁ → ∃ p : G.Walk u w, ∀ e ∈ p.edges, e ∈ F := by
  classical
  intro F hF hFs hcard u w hu hw
  have h := ncomp_le (G := G) (univ.erase v₁) F hF
    (fun e he a ha => (mem_gamma_iff G _ e).1 (hFs he) a ha)
  have hV' : (univ.erase v₁).card + 1 = Fintype.card V := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v₁⟩
    omega
  have key : ∀ I : Finset (Finset V), F.card + I.card ≤ (univ.erase v₁).card → I.card ≤ 1 :=
    fun I hI => by omega
  have hle := key _ h
  have huS : u ∈ univ.erase v₁ := Finset.mem_erase.2 ⟨hu, Finset.mem_univ _⟩
  have hwS : w ∈ univ.erase v₁ := Finset.mem_erase.2 ⟨hw, Finset.mem_univ _⟩
  have heq := Finset.card_le_one.1 hle _ (Finset.mem_image_of_mem _ huS) _
    (Finset.mem_image_of_mem _ hwS)
  have hw' : w ∈ (univ.erase v₁).filter (Conn G F w) := Finset.mem_filter.2 ⟨hwS, conn_refl _ _⟩
  rw [← heq, Finset.mem_filter] at hw'
  exact hw'.2

/-- K1: a set connecting `V \ v₁` has at least `|V \ v₁| - 1` edges. -/
theorem k1 [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : Graph V E) (v₁ : V)
    (T : Finset E) (hT : ∀ u w : V, u ≠ v₁ → w ≠ v₁ → ∃ p : G.Walk u w, ∀ e ∈ p.edges, e ∈ T)
    (hne : (univ.erase v₁).Nonempty) : (univ.erase v₁).card ≤ T.card + 1 := by
  classical
  obtain ⟨r, hr⟩ := hne
  have hr' : r ≠ v₁ := (Finset.mem_erase.1 hr).1
  have h := card_le_conn (G := G) (B := T) (univ.erase v₁) hr
    (fun v hv => hT v r (Finset.mem_erase.1 hv).1 hr')
  exact h.trans (Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) 1)

/-- C1: the incidence vector of a 1-tree is feasible for (7.7). -/
theorem c1 [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : Graph V E) (v₁ : V) :
    ∀ J, G.IsOneTree v₁ J → G.OneTreeLPFeasible v₁ (fun e => if e ∈ J then 1 else 0) := by
  rintro J ⟨e, f, T, hef, he, hf, hT, rfl⟩
  have hev : v₁ ∈ G.ends e := ((mem_cut_single_iff G v₁ e).1 he).1
  have hfv : v₁ ∈ G.ends f := ((mem_cut_single_iff G v₁ f).1 hf).1
  have hsum : ∀ A : Finset E, ∑ g ∈ A, (if g ∈ insert e (insert f T) then (1 : ℝ) else 0)
      = ((A.filter (· ∈ insert e (insert f T))).card : ℝ) := by
    intro A; rw [Finset.sum_boole]
  have hgS : ∀ S : Finset V, v₁ ∉ S →
      (G.gamma S).filter (· ∈ insert e (insert f T)) = (G.gamma S).filter (· ∈ T) := by
    intro S hS
    ext g
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hg, h | h | h⟩
      · exact absurd ((mem_gamma_iff G S g).1 hg v₁ (by rw [h]; exact hev)) hS
      · exact absurd ((mem_gamma_iff G S g).1 hg v₁ (by rw [h]; exact hfv)) hS
      · exact ⟨hg, h⟩
    · rintro ⟨hg, h⟩; exact ⟨hg, Or.inr (Or.inr h)⟩
  have hTΓ : (G.gamma (univ.erase v₁)).filter (· ∈ T) = T := by
    ext g
    simp only [Finset.mem_filter, mem_gamma_iff, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · exact fun h => h.2
    · intro hg
      refine ⟨fun a ha hav => hT.1 g hg ?_, hg⟩
      rw [← hav]; exact ha
  have hne : (univ.erase v₁).Nonempty := by
    obtain ⟨b, -, hb⟩ := ((mem_cut_single_iff G v₁ e).1 he).2
    exact ⟨b, Finset.mem_erase.2 ⟨hb, Finset.mem_univ _⟩⟩
  have hV' : (univ.erase v₁).card + 1 = Fintype.card V := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v₁⟩
    omega
  have hcut : (G.cut {v₁}).filter (· ∈ insert e (insert f T)) = {e, f} := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hg, h | h | h⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd ((mem_cut_single_iff G v₁ g).1 hg).1 (hT.1 g h)
    · rintro (h | h)
      · exact ⟨h ▸ he, Or.inl h⟩
      · exact ⟨h ▸ hf, Or.inr (Or.inl h)⟩
  refine ⟨fun S hS hv => ?_, ?_, fun g => by dsimp only; split_ifs <;> norm_num, ?_⟩
  · rw [hsum, hgS S hv]
    have h1 := forest_card hT.2.2 hS
    have h2 : (((G.gamma S).filter (· ∈ T)).card : ℝ) + 1 ≤ S.card := by exact_mod_cast h1
    linarith
  · rw [hsum, hgS _ (Finset.notMem_erase v₁ univ), hTΓ]
    have h1 := forest_card hT.2.2 hne
    rw [hTΓ] at h1
    have h2 := k1 G v₁ T hT.2.1 hne
    have h3 : T.card + 2 = Fintype.card V := by omega
    have h4 : ((T.card + 2 : ℕ) : ℝ) = Fintype.card V := by exact_mod_cast h3
    push_cast at h4; linarith
  · rw [hsum, hcut, Finset.card_pair hef]; norm_num

/-- The parent (7.7) from the forest polytope theorem (child c776d601) for `G`. -/
theorem main [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : Graph V E) (v₁ : V)
    (hv₁ : ∀ e : E, G.ends e ≠ s(v₁, v₁)) (c : E → ℝ)
    (hfp : convexHull ℝ {x : E → ℝ | ∃ F : Finset E, G.IsForest F ∧ x = fun e => if e ∈ F then 1 else 0} =
      {x : E → ℝ | (∀ T : Finset V, T.Nonempty → ∑ e ∈ G.gamma T, x e ≤ (T.card : ℝ) - 1) ∧
        ∀ e : E, 0 ≤ x e}) :
    G.minOneTreeCost c v₁ = G.oneTreeLPValue c v₁ :=
  parent_of_children G v₁ hv₁ c (c1 G v₁) (c2a_of_forest_polytope G v₁ c hfp (k2 G v₁))

end Final
end CombOpt.HeldKarp.E7

open CombOpt.HeldKarp in
theorem solution {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : CombOpt.HeldKarp.Graph V E) (v₁ : V) (hv₁ : ∀ e : E, G.ends e ≠ s(v₁, v₁))
    (c : E → ℝ) :
    G.minOneTreeCost c v₁ = G.oneTreeLPValue c v₁ := by
  exact CombOpt.HeldKarp.E7.main G v₁ hv₁ c (CombOpt.HeldKarp.forest_polytope G)
