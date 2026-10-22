-- Prove2me | solution 1 for FlowsNetworks.Graphs.unicursal_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:41:44.562362+00:00
-- url     : https://prove2.me/submissions/8884fd3f-f148-4009-8d7c-a395710fa715

import Mathlib
import Definitions.Def_FlowsNetworks_Graphs_MixedGraph

section g71u
set_option linter.unusedSectionVars false
variable {N : Type} [DecidableEq N]

def g71u_Tr : N → List (N × N) → N → Prop
  | u, [], w => u = w
  | u, e :: P, w => e.1 = u ∧ g71u_Tr e.2 P w

theorem g71u_tr_append (P Q : List (N × N)) : ∀ (u w : N),
    g71u_Tr u (P ++ Q) w ↔ ∃ m, g71u_Tr u P m ∧ g71u_Tr m Q w := by
  induction P with
  | nil => intro u w; simp [g71u_Tr]
  | cons e P ih =>
    intro u w
    simp only [List.cons_append, g71u_Tr, ih]
    constructor
    · rintro ⟨h1, m, h2, h3⟩; exact ⟨m, ⟨h1, h2⟩, h3⟩
    · rintro ⟨m, ⟨h1, h2⟩, h3⟩; exact ⟨h1, m, h2, h3⟩

def g71u_cin (z : N) (P : List (N × N)) : ℕ := (P.filter (fun e => e.2 = z)).length
def g71u_cout (z : N) (P : List (N × N)) : ℕ := (P.filter (fun e => e.1 = z)).length

theorem g71u_tr_count (P : List (N × N)) : ∀ (u w : N), g71u_Tr u P w → ∀ z,
    (g71u_cin z P : ℤ) - g71u_cout z P = (if z = w then 1 else 0) - (if z = u then 1 else 0) := by
  induction P with
  | nil => intro u w h z; simp [g71u_Tr] at h; subst h; simp [g71u_cin, g71u_cout]
  | cons e P ih =>
    intro u w h z
    obtain ⟨h1, h2⟩ := h
    have hih := ih _ _ h2 z
    have hi : (g71u_cin z (e :: P) : ℤ) = g71u_cin z P + (if e.2 = z then 1 else 0) := by
      unfold g71u_cin; rw [List.filter_cons]; split_ifs <;> simp_all
    have ho : (g71u_cout z (e :: P) : ℤ) = g71u_cout z P + (if e.1 = z then 1 else 0) := by
      unfold g71u_cout; rw [List.filter_cons]; split_ifs <;> simp_all
    rw [hi, ho]
    subst h1
    simp only [@eq_comm _ e.2 z, @eq_comm _ e.1 z] at hih ⊢
    split_ifs at hih ⊢ <;> omega

def g71u_Bal (F : Finset (N × N)) : Prop :=
  ∀ z, (F.filter (fun e => e.1 = z)).card = (F.filter (fun e => e.2 = z)).card

theorem g71u_len_le (F : Finset (N × N)) (P : List (N × N)) (hP : P.Nodup) (hPF : ∀ e ∈ P, e ∈ F)
    (p : N × N → Prop) [DecidablePred p] :
    (P.filter p).length ≤ (F.filter p).card := by
  rw [← List.toFinset_card_of_nodup (hP.filter _)]
  apply Finset.card_le_card
  intro e he
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at he
  simp only [Finset.mem_filter]
  exact ⟨hPF e he.1, he.2⟩

theorem g71u_unused (F : Finset (N × N)) (P : List (N × N)) (hP : P.Nodup) (w : N)
    (hlt : g71u_cout w P < (F.filter (fun e => e.1 = w)).card) :
    ∃ e ∈ F, e.1 = w ∧ e ∉ P := by
  by_contra hc
  push Not at hc
  have : (F.filter (fun e => e.1 = w)) ⊆ (P.filter (fun e => e.1 = w)).toFinset := by
    intro e he
    rw [Finset.mem_filter] at he
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨hc e he.1 he.2, he.2⟩
  have h2 := Finset.card_le_card this
  have h3 := List.toFinset_card_le (P.filter (fun e => e.1 = w))
  unfold g71u_cout at hlt
  omega

theorem g71u_closed_walk (F : Finset (N × N)) (hF : g71u_Bal F) (u c : N) (huc : (u, c) ∈ F) :
    ∃ W : List (N × N), W ≠ [] ∧ g71u_Tr u W u ∧ W.Nodup ∧ ∀ e ∈ W, e ∈ F := by
  have key : ∀ n, ∀ (P : List (N × N)) (w : N), F.card - P.length = n → P ≠ [] →
      g71u_Tr u P w → P.Nodup → (∀ e ∈ P, e ∈ F) →
      ∃ W : List (N × N), W ≠ [] ∧ g71u_Tr u W u ∧ W.Nodup ∧ ∀ e ∈ W, e ∈ F := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro P w hn hne htr hnd hsub
    by_cases hw : w = u
    · subst hw; exact ⟨P, hne, htr, hnd, hsub⟩
    · have hc := g71u_tr_count P u w htr w
      rw [if_pos rfl, if_neg hw] at hc
      have hin := g71u_len_le F P hnd hsub (fun e => e.2 = w)
      have hbal := hF w
      have hlt : g71u_cout w P < (F.filter (fun e => e.1 = w)).card := by
        unfold g71u_cin at hc; omega
      obtain ⟨e, heF, he1, heP⟩ := g71u_unused F P hnd w hlt
      have htr' : g71u_Tr u (P ++ [e]) e.2 :=
        (g71u_tr_append P [e] u e.2).2 ⟨w, htr, he1, rfl⟩
      have hnd' : (P ++ [e]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton e, ?_⟩
        intro a ha b hb; simp at hb; subst hb; intro h; subst h; exact heP ha
      have hsub' : ∀ x ∈ P ++ [e], x ∈ F := by
        intro x hx; rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hsub x hx
        · simp at hx; subst hx; exact heF
      have hlen : (P ++ [e]).length ≤ F.card := by
        have := g71u_len_le F (P ++ [e]) hnd' hsub' (fun _ => True)
        simpa using this
      exact ih (F.card - (P ++ [e]).length) (by simp at hlen ⊢; omega) (P ++ [e]) e.2 rfl
        (by simp) htr' hnd' hsub'
  exact key _ [(u, c)] c rfl (by simp) ⟨rfl, rfl⟩ (List.nodup_singleton _)
    (by intro e he; simp at he; subst he; exact huc)

theorem g71u_cross (R : N → N → Prop) (S : Finset N) {x y : N} (h : Relation.ReflTransGen R x y)
    (hx : x ∈ S) (hy : y ∉ S) : ∃ a b, R a b ∧ a ∈ S ∧ b ∉ S := by
  induction h with
  | refl => exact absurd hx hy
  | @tail b c _ hbc ih =>
    by_cases hb : b ∈ S
    · exact ⟨b, c, hbc, hb, hy⟩
    · exact ih hb

theorem g71u_split_card (F : Finset (N × N)) (T : List (N × N)) (hnd : T.Nodup)
    (hsub : ∀ e ∈ T, e ∈ F) (p : N × N → Prop) [DecidablePred p] :
    (F.filter p).card = (T.filter p).length + ((F.filter (fun e => e ∉ T)).filter p).card := by
  rw [← Finset.card_filter_add_card_filter_not (s := F.filter p) (fun e => e ∈ T)]
  congr 1
  · rw [← List.toFinset_card_of_nodup (hnd.filter _)]
    congr 1
    ext e
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨hsub e h1, h2⟩, h1⟩
  · congr 1
    ext e
    simp only [Finset.mem_filter]
    tauto

theorem g71u_bal_rest (F : Finset (N × N)) (hF : g71u_Bal F) (T : List (N × N)) (s : N)
    (hT : g71u_Tr s T s) (hnd : T.Nodup) (hsub : ∀ e ∈ T, e ∈ F) :
    g71u_Bal (F.filter (fun e => e ∉ T)) := by
  intro z
  have h1 := g71u_split_card F T hnd hsub (fun e => e.1 = z)
  have h2 := g71u_split_card F T hnd hsub (fun e => e.2 = z)
  have h3 := g71u_tr_count T s s hT z
  have h4 := hF z
  unfold g71u_cin g71u_cout at h3
  split_ifs at h3 <;> omega

theorem g71u_split_at (T : List (N × N)) (s w : N) (hT : g71u_Tr s T w) (u : N)
    (hu : u ∈ (T.map Prod.fst).toFinset ∪ (T.map Prod.snd).toFinset) :
    ∃ A B, T = A ++ B ∧ g71u_Tr s A u ∧ g71u_Tr u B w := by
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_map] at hu
  rcases hu with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · obtain ⟨A, B, rfl⟩ := List.append_of_mem he
    obtain ⟨m, h1, h2⟩ := (g71u_tr_append A (e :: B) s w).1 hT
    have hm : e.1 = m := h2.1
    refine ⟨A, e :: B, rfl, hm ▸ h1, ?_⟩
    exact ⟨rfl, h2.2⟩
  · obtain ⟨A, B, rfl⟩ := List.append_of_mem he
    have hT' : g71u_Tr s ((A ++ [e]) ++ B) w := by simpa using hT
    obtain ⟨m, h1, h2⟩ := (g71u_tr_append (A ++ [e]) B s w).1 hT'
    obtain ⟨k, h3, h4⟩ := (g71u_tr_append A [e] s m).1 h1
    have hm : e.2 = m := h4.2
    refine ⟨A ++ [e], B, by simp, hm ▸ h1, hm ▸ h2⟩

theorem g71u_extend (F : Finset (N × N)) (hF : g71u_Bal F)
    (hconn : ∀ x y : N, Relation.ReflTransGen (fun a b => (a, b) ∈ F ∨ (b, a) ∈ F) x y)
    (T : List (N × N)) (s : N) (hT : g71u_Tr s T s) (hnd : T.Nodup) (hsub : ∀ e ∈ T, e ∈ F)
    (hlt : T.length < F.card) :
    ∃ (T' : List (N × N)) (s' : N), g71u_Tr s' T' s' ∧ T'.Nodup ∧ (∀ e ∈ T', e ∈ F) ∧
      T.length < T'.length := by
  set R := F.filter (fun e => e ∉ T) with hR
  have hRF : ∀ e ∈ R, e ∈ F := fun e he => (Finset.mem_filter.1 he).1
  have hRT : ∀ e ∈ R, e ∉ T := fun e he => (Finset.mem_filter.1 he).2
  have hRb : g71u_Bal R := g71u_bal_rest F hF T s hT hnd hsub
  have hRne : R.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := g71u_split_card F T hnd hsub (fun _ => True)
    rw [show (F.filter fun e => e ∉ T) = R from rfl, h] at this
    simp at this; omega
  rcases (em (T = [])) with hT0 | hT0
  · obtain ⟨r, hr⟩ := hRne
    obtain ⟨W, hWne, hW, hWnd, hWR⟩ := g71u_closed_walk R hRb r.1 r.2 (by simpa using hr)
    refine ⟨W, r.1, hW, hWnd, fun e he => hRF e (hWR e he), ?_⟩
    subst hT0; simp only [List.length_nil]
    exact List.length_pos_iff.2 hWne
  set V : Finset N := (T.map Prod.fst).toFinset ∪ (T.map Prod.snd).toFinset with hV
  have hVmem : ∀ e ∈ T, e.1 ∈ V ∧ e.2 ∈ V := by
    intro e he
    simp only [hV, Finset.mem_union, List.mem_toFinset, List.mem_map]
    exact ⟨Or.inl ⟨e, he, rfl⟩, Or.inr ⟨e, he, rfl⟩⟩
  have hsV : s ∈ V := by
    obtain ⟨e, T1, rfl⟩ := List.exists_cons_of_ne_nil hT0
    have : e.1 = s := hT.1
    rw [← this]; exact (hVmem e (List.mem_cons_self)).1
  have hr : ∃ r ∈ R, r.1 ∈ V ∨ r.2 ∈ V := by
    by_contra hc
    push Not at hc
    obtain ⟨r0, hr0⟩ := hRne
    obtain ⟨a, b, hab, ha, hb⟩ := g71u_cross _ V (hconn s r0.1) hsV (hc r0 hr0).1
    rcases hab with h | h
    · by_cases hT' : (a, b) ∈ T
      · exact hb (hVmem _ hT').2
      · exact (hc (a, b) (Finset.mem_filter.2 ⟨h, hT'⟩)).1 ha
    · by_cases hT' : (b, a) ∈ T
      · exact hb (hVmem _ hT').1
      · exact (hc (b, a) (Finset.mem_filter.2 ⟨h, hT'⟩)).2 ha
  obtain ⟨r, hrR, hrV⟩ := hr
  have hu : ∃ u ∈ V, ∃ c, (u, c) ∈ R := by
    rcases hrV with h | h
    · exact ⟨r.1, h, r.2, by simpa using hrR⟩
    · have hpos : 0 < (R.filter (fun e => e.2 = r.2)).card :=
        Finset.card_pos.2 ⟨r, Finset.mem_filter.2 ⟨hrR, rfl⟩⟩
      rw [← hRb r.2] at hpos
      obtain ⟨e, he⟩ := Finset.card_pos.1 hpos
      rw [Finset.mem_filter] at he
      refine ⟨r.2, h, e.2, ?_⟩
      rw [← he.2]; simpa using he.1
  obtain ⟨u, huV, c, huc⟩ := hu
  obtain ⟨A, B, hAB, hA, hB⟩ := g71u_split_at T s s hT u huV
  obtain ⟨W, hWne, hW, hWnd, hWR⟩ := g71u_closed_walk R hRb u c huc
  have hBA : g71u_Tr u (B ++ A) u := (g71u_tr_append B A u u).2 ⟨s, hB, hA⟩
  have hmem : ∀ x, x ∈ B ++ A ↔ x ∈ T := by
    intro x; rw [hAB]; simp only [List.mem_append]; tauto
  refine ⟨W ++ (B ++ A), u, (g71u_tr_append W (B ++ A) u u).2 ⟨u, hW, hBA⟩, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hWnd, ?_, ?_⟩
    · rw [hAB] at hnd; exact (List.perm_append_comm.nodup_iff).1 hnd
    · intro a ha b hb hab
      subst hab
      exact hRT a (hWR a ha) ((hmem a).1 hb)
  · intro e he
    rw [List.mem_append] at he
    rcases he with he | he
    · exact hRF e (hWR e he)
    · exact hsub e ((hmem e).1 he)
  · have : T.length = (B ++ A).length := by rw [hAB]; simp [Nat.add_comm]
    rw [List.length_append, ← this]
    have := List.length_pos_iff.2 hWne
    omega

theorem g71u_euler (F : Finset (N × N)) (hF : g71u_Bal F)
    (hconn : ∀ x y : N, Relation.ReflTransGen (fun a b => (a, b) ∈ F ∨ (b, a) ∈ F) x y)
    (s₀ : N) :
    ∃ (T : List (N × N)) (s : N), g71u_Tr s T s ∧ T.Nodup ∧ (∀ e ∈ T, e ∈ F) ∧
      T.length = F.card := by
  have key : ∀ k, ∃ (T : List (N × N)) (s : N), g71u_Tr s T s ∧ T.Nodup ∧
      (∀ e ∈ T, e ∈ F) ∧ min k F.card ≤ T.length := by
    intro k
    induction k with
    | zero => exact ⟨[], s₀, rfl, List.nodup_nil, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨T, s, hT, hnd, hsub, hk⟩ := ih
      have hle : T.length ≤ F.card := by
        have := g71u_len_le F T hnd hsub (fun _ => True)
        simpa using this
      by_cases hlt : T.length < F.card
      · obtain ⟨T', s', hT', hnd', hsub', hlt'⟩ := g71u_extend F hF hconn T s hT hnd hsub hlt
        exact ⟨T', s', hT', hnd', hsub', by omega⟩
      · exact ⟨T, s, hT, hnd, hsub, by omega⟩
  obtain ⟨T, s, hT, hnd, hsub, hk⟩ := key F.card
  have hle : T.length ≤ F.card := by
    have := g71u_len_le F T hnd hsub (fun _ => True)
    simpa using this
  exact ⟨T, s, hT, hnd, hsub, by simp at hk; omega⟩

end g71u
open FlowsNetworks.Graphs FlowsNetworks.Graphs.MixedGraph

section g71uS
set_option linter.unusedSectionVars false
variable {N : Type} [Fintype N] [DecidableEq N]

theorem g71u_tr_get (T : List (N × N)) : ∀ (s w : N), g71u_Tr s T w → ∀ (i : ℕ) (h : i < T.length),
    T[i] = ((s :: T.map Prod.snd)[i]'(by simp; omega), (s :: T.map Prod.snd)[i + 1]'(by simp; omega)) := by
  induction T with
  | nil => intro s w _ i h; simp at h
  | cons e T ih =>
    intro s w htr i h
    obtain ⟨h1, h2⟩ := htr
    cases i with
    | zero => simp [← h1]
    | succ i =>
      have := ih e.2 w h2 i (by simp at h; omega)
      simpa using this

theorem g71u_tr_last (T : List (N × N)) : ∀ (s w : N), g71u_Tr s T w →
    (s :: T.map Prod.snd)[T.length]'(by simp) = w := by
  induction T with
  | nil => intro s w h; simpa [g71u_Tr] using h
  | cons e T ih =>
    intro s w htr
    have := ih e.2 w htr.2
    simpa using this

end g71uS

open FlowsNetworks.Graphs FlowsNetworks.Graphs.MixedGraph

section g71uM
set_option linter.unusedSectionVars false
variable {N : Type} [Fintype N] [DecidableEq N]

theorem g71u_route_arc (G : MixedGraph N) {m : ℕ} {x : Fin (m + 1) → N} {a : Fin m → MixedArc N}
    (hr : G.IsClosedRoute m x a) (i : Fin m) : G.IsArc (a i) := by
  rcases hr.2 i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> exact h2

theorem g71u_route_ne (G : MixedGraph N) {m : ℕ} {x : Fin (m + 1) → N} {a : Fin m → MixedArc N}
    (hr : G.IsClosedRoute m x a) (i : Fin m) : x i.castSucc ≠ x i.succ := by
  rcases hr.2 i with ⟨_, h2⟩ | ⟨_, h2⟩
  · exact G.dir_loopless _ h2
  · have := G.undir_loopless _ h2; simpa using this

theorem g71u_cntD (G : MixedGraph N) {m : ℕ} {x : Fin (m + 1) → N} {a : Fin m → MixedArc N}
    (hr : G.IsClosedRoute m x a) (hinj : Function.Injective a) (hcov : ∀ e, G.IsArc e → ∃ i, a i = e)
    (P : N × N → Prop) [DecidablePred P] :
    (G.dirArcs.filter P).card = (Finset.univ.filter
      (fun i => Sum.elim (fun p => decide (P p)) (fun _ => false) (a i) = true)).card := by
  refine Finset.card_bij (fun p hp => Classical.choose (hcov (Sum.inl p) (Finset.mem_filter.1 hp).1))
    ?_ ?_ ?_
  · intro p hp
    have := Classical.choose_spec (hcov (Sum.inl p) (Finset.mem_filter.1 hp).1)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [this]; simpa using (Finset.mem_filter.1 hp).2
  · intro p hp q hq h
    have h1 := Classical.choose_spec (hcov (Sum.inl p) (Finset.mem_filter.1 hp).1)
    have h2 := Classical.choose_spec (hcov (Sum.inl q) (Finset.mem_filter.1 hq).1)
    rw [h] at h1; rw [h1] at h2; exact Sum.inl_injective h2
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have harc := g71u_route_arc G hr i
    rcases hai : a i with p | e
    · rw [hai] at hi harc
      have hpd : p ∈ G.dirArcs := harc
      have hP : P p := by simpa using hi
      refine ⟨p, Finset.mem_filter.2 ⟨hpd, hP⟩, ?_⟩
      have h1 := Classical.choose_spec (hcov (Sum.inl p) hpd)
      exact hinj (h1.trans hai.symm)
    · rw [hai] at hi; simp at hi

theorem g71u_cntU (G : MixedGraph N) {m : ℕ} {x : Fin (m + 1) → N} {a : Fin m → MixedArc N}
    (hr : G.IsClosedRoute m x a) (hinj : Function.Injective a) (hcov : ∀ e, G.IsArc e → ∃ i, a i = e)
    (P : Sym2 N → Prop) [DecidablePred P] :
    (G.undirArcs.filter P).card = (Finset.univ.filter
      (fun i => Sum.elim (fun _ => false) (fun e => decide (P e)) (a i) = true)).card := by
  refine Finset.card_bij (fun p hp => Classical.choose (hcov (Sum.inr p) (Finset.mem_filter.1 hp).1))
    ?_ ?_ ?_
  · intro p hp
    have := Classical.choose_spec (hcov (Sum.inr p) (Finset.mem_filter.1 hp).1)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [this]; simpa using (Finset.mem_filter.1 hp).2
  · intro p hp q hq h
    have h1 := Classical.choose_spec (hcov (Sum.inr p) (Finset.mem_filter.1 hp).1)
    have h2 := Classical.choose_spec (hcov (Sum.inr q) (Finset.mem_filter.1 hq).1)
    rw [h] at h1; rw [h1] at h2; exact Sum.inr_injective h2
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have harc := g71u_route_arc G hr i
    rcases hai : a i with p | e
    · rw [hai] at hi; simp at hi
    · rw [hai] at hi harc
      have hpd : e ∈ G.undirArcs := harc
      have hP : P e := by simpa using hi
      refine ⟨e, Finset.mem_filter.2 ⟨hpd, hP⟩, ?_⟩
      have h1 := Classical.choose_spec (hcov (Sum.inr e) hpd)
      exact hinj (h1.trans hai.symm)

theorem g71u_card_sum {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ((s.filter p).card : ℤ) = ∑ i ∈ s, if p i then (1 : ℤ) else 0 := by
  rw [Finset.card_filter]; push_cast; rfl

theorem g71u_shift {m : ℕ} (x : Fin (m + 1) → N) (hx : x 0 = x (Fin.last m)) (f : N → ℤ) :
    ∑ i : Fin m, f (x i.castSucc) = ∑ i : Fin m, f (x i.succ) := by
  have h1 := Fin.sum_univ_castSucc (fun j => f (x j))
  have h2 := Fin.sum_univ_succ (fun j => f (x j))
  rw [hx] at h2
  linarith

theorem g71u_cross_iff (X : Finset N) (c d : N) :
    (∃ x ∈ X, ∃ y ∈ Xᶜ, s(c, d) = s(x, y)) ↔ (c ∈ X ∧ d ∉ X) ∨ (d ∈ X ∧ c ∉ X) := by
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    rw [Finset.mem_compl] at hy
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨c, h1, d, Finset.mem_compl.2 h2, rfl⟩
    · exact ⟨d, h1, c, Finset.mem_compl.2 h2, Sym2.eq_swap⟩

theorem g71u_adj_symm (G : MixedGraph N) {x y : N} (h : G.Adj x y) : G.Adj y x := by
  unfold MixedGraph.Adj at *
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (by rwa [Sym2.eq_swap]))

theorem g71u_rtg_symm (G : MixedGraph N) {x y : N} (h : Relation.ReflTransGen G.Adj x y) :
    Relation.ReflTransGen G.Adj y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (g71u_adj_symm G hab) ih

theorem g71u_nec (G : MixedGraph N) (h : G.Unicursal) :
    G.Connected ∧ (∀ v : N, Even (G.degree v)) ∧
        ∀ X : Finset N, (G.dirOut X : ℤ) - (G.dirIn X : ℤ) ≤ (G.undirJoining X : ℤ) := by
  obtain ⟨m, x, a, hr, hinj, hcov, hvis⟩ := h
  refine ⟨⟨⟨x 0⟩, ?_⟩, ?_, ?_⟩
  · have reach : ∀ j : Fin (m + 1), Relation.ReflTransGen G.Adj (x 0) (x j) := by
      intro j
      induction j using Fin.induction with
      | zero => exact Relation.ReflTransGen.refl
      | succ i ih =>
        refine ih.tail ?_
        rcases hr.2 i with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inl h2
        · exact Or.inr (Or.inr h2)
    intro u v
    obtain ⟨i, rfl⟩ := hvis u
    obtain ⟨j, rfl⟩ := hvis v
    exact (g71u_rtg_symm G (reach i)).trans (reach j)
  · intro v
    have hD := g71u_cntD G hr hinj hcov (fun p => p.1 = v ∨ p.2 = v)
    have hU := g71u_cntU G hr hinj hcov (fun e => v ∈ e)
    have hz : (G.degree v : ℤ) = 2 * ∑ i : Fin m, (if x i.castSucc = v then (1 : ℤ) else 0) := by
      unfold MixedGraph.degree
      push_cast
      rw [hD, hU, g71u_card_sum, g71u_card_sum, ← Finset.sum_add_distrib]
      have hpt : ∀ i : Fin m,
          ((if Sum.elim (fun p => decide (p.1 = v ∨ p.2 = v)) (fun _ => false) (a i) = true
              then (1 : ℤ) else 0) +
            (if Sum.elim (fun _ => false) (fun e => decide (v ∈ e)) (a i) = true then 1 else 0)) =
          (if x i.castSucc = v then 1 else 0) + (if x i.succ = v then 1 else 0) := by
        intro i
        have hne := g71u_route_ne G hr i
        rcases hr.2 i with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;>
          by_cases h3 : x i.castSucc = v <;> by_cases h4 : x i.succ = v <;>
          simp [h3, h4, @eq_comm _ v] <;> (try subst h3) <;> (try subst h4) <;> simp_all
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib,
        ← g71u_shift x hr.1 (fun w => if w = v then (1 : ℤ) else 0)]
      ring
    have : Even (G.degree v : ℤ) := ⟨_, by rw [hz]; ring⟩
    exact (Int.even_coe_nat _).1 this
  · intro X
    have hO := g71u_cntD G hr hinj hcov (fun p => p.1 ∈ X ∧ p.2 ∉ X)
    have hI := g71u_cntD G hr hinj hcov (fun p => p.1 ∉ X ∧ p.2 ∈ X)
    have hU := g71u_cntU G hr hinj hcov (fun e => ∃ x ∈ X, ∃ y ∈ Xᶜ, e = s(x, y))
    unfold MixedGraph.dirOut MixedGraph.dirIn MixedGraph.undirJoining
    rw [hO, hI, hU, g71u_card_sum, g71u_card_sum, g71u_card_sum]
    have hpt : ∀ i : Fin m,
        (if Sum.elim (fun p => decide (p.1 ∈ X ∧ p.2 ∉ X)) (fun _ => false) (a i) = true
            then (1 : ℤ) else 0) -
          (if Sum.elim (fun p => decide (p.1 ∉ X ∧ p.2 ∈ X)) (fun _ => false) (a i) = true
            then 1 else 0) -
          (if Sum.elim (fun _ => false) (fun e => decide (∃ x ∈ X, ∃ y ∈ Xᶜ, e = s(x, y))) (a i)
            = true then 1 else 0) ≤
        (if x i.castSucc ∈ X then 1 else 0) - (if x i.succ ∈ X then 1 else 0) := by
      intro i
      rcases hr.2 i with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
      · by_cases h3 : x i.castSucc ∈ X <;> by_cases h4 : x i.succ ∈ X <;> simp [h3, h4]
      · have hc := g71u_cross_iff X (x i.castSucc) (x i.succ)
        simp only [Sum.elim_inr, Sum.elim_inl, decide_eq_true_eq, hc]
        by_cases h3 : x i.castSucc ∈ X <;> by_cases h4 : x i.succ ∈ X <;> simp [h3, h4]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
    simp only [Finset.sum_sub_distrib] at hsum
    rw [g71u_shift x hr.1 (fun w => if w ∈ X then (1 : ℤ) else 0)] at hsum
    linarith

end g71uM

section g72u
set_option linter.unusedSectionVars false
variable {N : Type} [Fintype N] [DecidableEq N]

def g72u_net (F : Finset (N × N)) (z : N) : ℤ :=
  ((F.filter (fun p => p.1 = z)).card : ℤ) - (F.filter (fun p => p.2 = z)).card

def g72u_Valid (G : MixedGraph N) (O : Finset (N × N)) : Prop :=
  (∀ p ∈ O, s(p.1, p.2) ∈ G.undirArcs) ∧ (∀ e ∈ G.undirArcs, ∃ p ∈ O, s(p.1, p.2) = e) ∧
    (∀ p ∈ O, (p.2, p.1) ∉ O)

def g72u_b (G : MixedGraph N) (O : Finset (N × N)) (z : N) : ℤ :=
  g72u_net G.dirArcs z + g72u_net O z

def g72u_Phi (G : MixedGraph N) (O : Finset (N × N)) : ℤ := ∑ z, |g72u_b G O z|

theorem g72u_inj (G : MixedGraph N) (O : Finset (N × N)) (hO : g72u_Valid G O) {p q : N × N}
    (hp : p ∈ O) (hq : q ∈ O) (h : s(p.1, p.2) = s(q.1, q.2)) : p = q := by
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · exfalso; apply hO.2.2 q hq
    have : (q.2, q.1) = p := Prod.ext h1.symm h2.symm
    rw [this]; exact hp

theorem g72u_cardU (G : MixedGraph N) (O : Finset (N × N)) (hO : g72u_Valid G O)
    (P : Sym2 N → Prop) [DecidablePred P] (Q : N × N → Prop) [DecidablePred Q]
    (hQ : ∀ p, Q p ↔ P s(p.1, p.2)) :
    (O.filter Q).card = (G.undirArcs.filter P).card := by
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hO.1 p hp.1, (hQ p).1 hp.2⟩
  · intro p hp q hq h
    exact g72u_inj G O hO (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hq).1 h
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨p, hp, rfl⟩ := hO.2.1 e he.1
    exact ⟨p, Finset.mem_filter.2 ⟨hp, (hQ p).2 he.2⟩, rfl⟩

theorem g72u_orcard (F : Finset (N × N)) (hF : ∀ p ∈ F, p.1 ≠ p.2) (z : N) :
    (F.filter (fun p => p.1 = z ∨ p.2 = z)).card =
      (F.filter (fun p => p.1 = z)).card + (F.filter (fun p => p.2 = z)).card := by
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro p hp h1 h2
  exact hF p hp (h1.trans h2.symm)

theorem g72u_even (G : MixedGraph N) (O : Finset (N × N)) (hO : g72u_Valid G O)
    (hev : ∀ v, Even (G.degree v)) (z : N) : Even (g72u_b G O z) := by
  have hOl : ∀ p ∈ O, p.1 ≠ p.2 := by
    intro p hp h
    have := G.undir_loopless _ (hO.1 p hp)
    rw [Sym2.mk_isDiag_iff] at this; exact this h
  have h1 := g72u_orcard G.dirArcs G.dir_loopless z
  have h2 := g72u_orcard O hOl z
  have h3 := g72u_cardU G O hO (fun e => z ∈ e) (fun p => p.1 = z ∨ p.2 = z)
    (by intro p; rw [Sym2.mem_iff]; tauto)
  obtain ⟨k, hk⟩ := hev z
  unfold MixedGraph.degree at hk
  unfold g72u_b g72u_net
  refine ⟨(k : ℤ) - (G.dirArcs.filter (fun p => p.2 = z)).card -
    (O.filter (fun p => p.2 = z)).card, ?_⟩
  omega

theorem g72u_fib (F : Finset (N × N)) (X : Finset N) (f : N × N → N) :
    ∑ z ∈ X, (((F.filter (fun p => f p = z)).card : ℤ)) =
      ((F.filter (fun p => f p ∈ X)).card : ℤ) := by
  simp only [g71u_card_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_ite_eq]

theorem g72u_sum_net (F : Finset (N × N)) (X : Finset N) :
    ∑ z ∈ X, g72u_net F z = ((F.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X)).card : ℤ) -
      (F.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)).card := by
  have e1 := g72u_fib F X Prod.fst
  have e2 := g72u_fib F X Prod.snd
  unfold g72u_net
  rw [Finset.sum_sub_distrib, e1, e2]
  simp only [g71u_card_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h1 : p.1 ∈ X <;> by_cases h2 : p.2 ∈ X <;> simp [h1, h2]

theorem g72u_join (G : MixedGraph N) (O : Finset (N × N)) (hO : g72u_Valid G O) (X : Finset N) :
    (G.undirJoining X : ℤ) = (O.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X)).card +
      (O.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)).card := by
  have h := g72u_cardU G O hO (fun e => ∃ x ∈ X, ∃ y ∈ Xᶜ, e = s(x, y))
    (fun p => (p.1 ∈ X ∧ p.2 ∉ X) ∨ (p.1 ∉ X ∧ p.2 ∈ X))
    (by intro p; rw [g71u_cross_iff]; tauto)
  unfold MixedGraph.undirJoining
  rw [← h, Finset.filter_or, Finset.card_union_of_disjoint]
  · push_cast; ring
  · rw [Finset.disjoint_filter]; intro p _ h1 h2; exact h1.2 h2.2

theorem g72u_walk (O : Finset (N × N)) {s v : N}
    (h : Relation.ReflTransGen (fun a b => (a, b) ∈ O) s v) :
    ∃ P : List (N × N), g71u_Tr s P v ∧ ∀ e ∈ P, e ∈ O := by
  induction h with
  | refl => exact ⟨[], rfl, by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨P, hP, hPO⟩ := ih
    refine ⟨P ++ [(b, c)], (g71u_tr_append P [(b, c)] s c).2 ⟨b, hP, rfl, rfl⟩, ?_⟩
    intro e he
    rw [List.mem_append] at he
    rcases he with he | he
    · exact hPO e he
    · simp at he; subst he; exact hbc

theorem g72u_trail (P : List (N × N)) : ∀ s v : N, g71u_Tr s P v →
    ∃ P' : List (N × N), g71u_Tr s P' v ∧ P'.Nodup ∧ ∀ e ∈ P', e ∈ P := by
  induction P with
  | nil => intro s v h; exact ⟨[], h, List.nodup_nil, by simp⟩
  | cons e P ih =>
    intro s v h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨Q, hQ, hQnd, hQP⟩ := ih e.2 v h2
    by_cases he : e ∈ Q
    · obtain ⟨A, B, rfl⟩ := List.append_of_mem he
      obtain ⟨m, _, hm⟩ := (g71u_tr_append A (e :: B) e.2 v).1 hQ
      refine ⟨e :: B, ⟨h1, hm.2⟩, ?_, ?_⟩
      · exact (List.nodup_append.1 hQnd).2.1
      · intro x hx
        exact List.mem_cons_of_mem _ (hQP x (List.mem_append_right _ hx))
    · refine ⟨e :: Q, ⟨h1, hQ⟩, List.nodup_cons.2 ⟨he, hQnd⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hQP x hx)

theorem g72u_swapcard (P : List (N × N)) (hnd : P.Nodup) (q : N × N → Prop) [DecidablePred q] :
    ((P.map Prod.swap).toFinset.filter q).card = (P.filter (fun e => q (e.2, e.1))).length := by
  have : ((P.map Prod.swap).toFinset.filter q) =
      ((P.filter (fun e => q (e.2, e.1))).map Prod.swap).toFinset := by
    ext x
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_map, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hq⟩; exact ⟨a, ⟨ha, hq⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hq⟩, rfl⟩; exact ⟨⟨a, ha, rfl⟩, hq⟩
  rw [this, List.toFinset_card_of_nodup ((hnd.filter _).map Prod.swap_injective), List.length_map]

theorem g72u_improve (G : MixedGraph N) (hev : ∀ v, Even (G.degree v))
    (hcut : ∀ X : Finset N, (G.dirOut X : ℤ) - (G.dirIn X : ℤ) ≤ (G.undirJoining X : ℤ))
    (O : Finset (N × N)) (hO : g72u_Valid G O) (s : N) (hs : 0 < g72u_b G O s) :
    ∃ O', g72u_Valid G O' ∧ g72u_Phi G O' < g72u_Phi G O := by
  classical
  have hv : ∃ v, Relation.ReflTransGen (fun a b => (a, b) ∈ O) s v ∧ g72u_b G O v < 0 := by
    by_contra hno
    push Not at hno
    set X := Finset.univ.filter (fun z => Relation.ReflTransGen (fun a b => (a, b) ∈ O) s z)
      with hX
    have hmem : ∀ z, z ∈ X ↔ Relation.ReflTransGen (fun a b => (a, b) ∈ O) s z := by
      intro z; simp [hX]
    have hsX : s ∈ X := (hmem s).2 Relation.ReflTransGen.refl
    have hout0 : (O.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro p hp ⟨h1, h2⟩
      exact h2 ((hmem _).2 (((hmem _).1 h1).tail hp))
    have hsum : ∑ z ∈ X, g72u_b G O z = ((G.dirOut X : ℤ) - G.dirIn X) +
        (((O.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X)).card : ℤ) -
          (O.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)).card) := by
      unfold g72u_b
      rw [Finset.sum_add_distrib, g72u_sum_net, g72u_sum_net]
      rfl
    have hj := g72u_join G O hO X
    have hc := hcut X
    have hpos : g72u_b G O s ≤ ∑ z ∈ X, g72u_b G O z :=
      Finset.single_le_sum (fun z hz => hno z ((hmem z).1 hz)) hsX
    rw [hout0] at hsum hj
    push_cast at hsum hj
    linarith
  obtain ⟨v, hsv, hv⟩ := hv
  obtain ⟨P0, hP0, hP0O⟩ := g72u_walk O hsv
  obtain ⟨P, hP, hPnd, hPP0⟩ := g72u_trail P0 s v hP0
  have hPO : ∀ e ∈ P, e ∈ O := fun e he => hP0O e (hPP0 e he)
  have hsv' : s ≠ v := by rintro rfl; linarith
  set O' := O.filter (fun p => p ∉ P) ∪ (P.map Prod.swap).toFinset with hO'
  have hmemO' : ∀ p, p ∈ O' ↔ (p ∈ O ∧ p ∉ P) ∨ (p.2, p.1) ∈ P := by
    intro p
    rw [hO', Finset.mem_union, Finset.mem_filter, List.mem_toFinset, List.mem_map]
    constructor
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ha
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨(p.2, p.1), h, rfl⟩
  have hval : g72u_Valid G O' := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      rcases (hmemO' p).1 hp with h | h
      · exact hO.1 p h.1
      · have := hO.1 _ (hPO _ h)
        rw [Sym2.eq_swap]; exact this
    · intro e he
      obtain ⟨p, hp, rfl⟩ := hO.2.1 e he
      by_cases hpP : p ∈ P
      · refine ⟨(p.2, p.1), (hmemO' _).2 (Or.inr hpP), ?_⟩
        exact Sym2.eq_swap
      · exact ⟨p, (hmemO' p).2 (Or.inl ⟨hp, hpP⟩), rfl⟩
    · intro p hp hp'
      rcases (hmemO' p).1 hp with h | h <;> rcases (hmemO' _).1 hp' with h' | h'
      · exact hO.2.2 p h.1 h'.1
      · exact h.2 h'
      · exact h'.2 h
      · exact hO.2.2 _ (hPO _ h) (hPO _ h')
  have hnet : ∀ z, g72u_net O' z =
      g72u_net O z + 2 * ((g71u_cin z P : ℤ) - g71u_cout z P) := by
    intro z
    have hdisj : Disjoint (O.filter (fun p => p ∉ P)) (P.map Prod.swap).toFinset := by
      rw [Finset.disjoint_left]
      intro q hq hq'
      rw [Finset.mem_filter] at hq
      rw [List.mem_toFinset, List.mem_map] at hq'
      obtain ⟨a, ha, rfl⟩ := hq'
      exact hO.2.2 a (hPO a ha) hq.1
    have c1 : ∀ (r : N × N → Prop) [DecidablePred r], (O'.filter r).card =
        ((O.filter (fun p => p ∉ P)).filter r).card + ((P.map Prod.swap).toFinset.filter r).card := by
      intro r _
      rw [hO', Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
    have s1 := g71u_split_card O P hPnd hPO (fun e => e.1 = z)
    have s2 := g71u_split_card O P hPnd hPO (fun e => e.2 = z)
    have w1 := g72u_swapcard P hPnd (fun e => e.1 = z)
    have w2 := g72u_swapcard P hPnd (fun e => e.2 = z)
    unfold g72u_net g71u_cin g71u_cout
    rw [c1, c1]
    dsimp only at w1 w2
    omega
  have hb' : ∀ z, g72u_b G O' z =
      g72u_b G O z + 2 * ((if z = v then 1 else 0) - (if z = s then 1 else 0)) := by
    intro z; unfold g72u_b; rw [hnet, g71u_tr_count P s v hP z]; ring
  have hs2 : 2 ≤ g72u_b G O s := by
    obtain ⟨k, hk⟩ := g72u_even G O hO hev s; omega
  have hv2 : g72u_b G O v ≤ -2 := by
    obtain ⟨k, hk⟩ := g72u_even G O hO hev v; omega
  refine ⟨O', hval, ?_⟩
  unfold g72u_Phi
  apply Finset.sum_lt_sum
  · intro z _
    rw [hb' z]
    by_cases h1 : z = v
    · subst h1
      rw [if_pos rfl, if_neg (Ne.symm hsv'), abs_of_nonpos (by linarith),
        abs_of_neg (by linarith)]
      linarith
    · by_cases h2 : z = s
      · subst h2
        rw [if_neg h1, if_pos rfl, abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
        linarith
      · rw [if_neg h1, if_neg h2]; simp
  · refine ⟨s, Finset.mem_univ _, ?_⟩
    rw [hb' s, if_neg hsv', if_pos rfl, abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
    linarith

theorem g72u_exists (G : MixedGraph N) (hev : ∀ v, Even (G.degree v))
    (hcut : ∀ X : Finset N, (G.dirOut X : ℤ) - (G.dirIn X : ℤ) ≤ (G.undirJoining X : ℤ)) :
    ∃ O, g72u_Valid G O ∧ ∀ z, g72u_b G O z = 0 := by
  have hq : ∀ e : Sym2 N, s((Quot.out e).1, (Quot.out e).2) = e := fun e => Quot.out_eq e
  have h0 : g72u_Valid G (G.undirArcs.image (fun e => Quot.out e)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hp
      rw [hq]; exact he
    · intro e he
      exact ⟨Quot.out e, Finset.mem_image_of_mem _ he, hq e⟩
    · intro p hp hp'
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨e', he', h'⟩ := Finset.mem_image.1 hp'
      have hee : e' = e := by
        rw [← hq e', ← hq e, h']; exact Sym2.eq_swap
      subst hee
      have hloop := G.undir_loopless _ he'
      rw [← hq e', Sym2.mk_isDiag_iff] at hloop
      apply hloop
      have := congrArg Prod.fst h'
      simpa using this
  have hstep : ∀ O, g72u_Valid G O → (¬ ∀ z, g72u_b G O z = 0) →
      ∃ O', g72u_Valid G O' ∧ g72u_Phi G O' < g72u_Phi G O := by
    intro O hO hno
    have htot : ∑ z, g72u_b G O z = 0 := by
      unfold g72u_b; rw [Finset.sum_add_distrib, g72u_sum_net, g72u_sum_net]; simp
    have : ∃ s, 0 < g72u_b G O s := by
      by_contra hn
      push Not at hn
      push Not at hno
      obtain ⟨z, hz⟩ := hno
      have : ∑ z, g72u_b G O z < ∑ z : N, (0 : ℤ) :=
        Finset.sum_lt_sum (fun z _ => hn z) ⟨z, Finset.mem_univ _, lt_of_le_of_ne (hn z) hz⟩
      rw [Finset.sum_const_zero] at this; linarith
    obtain ⟨s, hs⟩ := this
    exact g72u_improve G hev hcut O hO s hs
  have hnn : ∀ O, 0 ≤ g72u_Phi G O := fun O => Finset.sum_nonneg (fun z _ => abs_nonneg _)
  have key : ∀ n : ℕ, ∀ O, g72u_Valid G O → (g72u_Phi G O).toNat ≤ n →
      ∃ O, g72u_Valid G O ∧ ∀ z, g72u_b G O z = 0 := by
    intro n
    induction n with
    | zero =>
      intro O hO hn
      by_contra hno'
      obtain ⟨O', _, hlt⟩ := hstep O hO (fun h => hno' ⟨O, hO, h⟩)
      have := hnn O'; have := hnn O
      omega
    | succ n ih =>
      intro O hO hn
      by_cases hb : ∀ z, g72u_b G O z = 0
      · exact ⟨O, hO, hb⟩
      obtain ⟨O', hO', hlt⟩ := hstep O hO hb
      exact ih O' hO' (by have := hnn O'; omega)
  exact key _ _ h0 le_rfl

end g72u

section g72uF
set_option linter.unusedSectionVars false
variable {N : Type} [Fintype N] [DecidableEq N]

def g72u_phi (G : MixedGraph N) (p : N × N) : MixedArc N :=
  if p ∈ G.dirArcs then Sum.inl p else Sum.inr s(p.1, p.2)

theorem g72u_phi_inj (G : MixedGraph N) (O : Finset (N × N)) (hO : g72u_Valid G O) {p q : N × N}
    (hp : p ∈ G.dirArcs ∪ O) (hq : q ∈ G.dirArcs ∪ O) (h : g72u_phi G p = g72u_phi G q) :
    p = q := by
  have hp' : p ∉ G.dirArcs → p ∈ O := by
    intro h1
    rcases Finset.mem_union.1 hp with h' | h'
    · exact absurd h' h1
    · exact h'
  have hq' : q ∉ G.dirArcs → q ∈ O := by
    intro h1
    rcases Finset.mem_union.1 hq with h' | h'
    · exact absurd h' h1
    · exact h'
  unfold g72u_phi at h
  by_cases h1 : p ∈ G.dirArcs <;> by_cases h2 : q ∈ G.dirArcs
  · rw [if_pos h1, if_pos h2] at h; exact Sum.inl_injective h
  · rw [if_pos h1, if_neg h2] at h; exact absurd h Sum.inl_ne_inr
  · rw [if_neg h1, if_pos h2] at h; exact absurd h Sum.inr_ne_inl
  · rw [if_neg h1, if_neg h2] at h
    exact g72u_inj G O hO (hp' h1) (hq' h2) (Sum.inr_injective h)

theorem g72u_final (G : MixedGraph N) (hc : G.Connected) (O : Finset (N × N))
    (hO : g72u_Valid G O) (hbal : ∀ z, g72u_b G O z = 0) : G.Unicursal := by
  have hOD : ∀ p ∈ O, p ∉ G.dirArcs := fun p hp => G.undir_not_dir p.1 p.2 (hO.1 p hp)
  set F := G.dirArcs ∪ O with hF
  have hdisj : Disjoint G.dirArcs O := Finset.disjoint_right.2 hOD
  have hFb : g71u_Bal F := by
    intro z
    have := hbal z
    unfold g72u_b g72u_net at this
    rw [hF, Finset.filter_union, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
    omega
  have hadj : ∀ u v, G.Adj u v → (u, v) ∈ F ∨ (v, u) ∈ F := by
    intro u v h
    rcases h with h | h | h
    · exact Or.inl (Finset.mem_union_left _ h)
    · exact Or.inr (Finset.mem_union_left _ h)
    · obtain ⟨p, hp, hpe⟩ := hO.2.1 _ h
      rcases Sym2.eq_iff.1 hpe with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; apply Finset.mem_union_right; rw [← h1, ← h2]; exact hp
      · right; apply Finset.mem_union_right; rw [← h1, ← h2]; exact hp
  have hconn : ∀ x y : N, Relation.ReflTransGen (fun a b => (a, b) ∈ F ∨ (b, a) ∈ F) x y :=
    fun x y => Relation.ReflTransGen.mono (fun u v h => hadj u v h) _ _ (hc.2 x y)
  obtain ⟨s₀⟩ := hc.1
  obtain ⟨T, s, hT, hnd, hsub, hlen⟩ := g71u_euler F hFb hconn s₀
  have hTF : T.toFinset = F := by
    apply Finset.eq_of_subset_of_card_le
    · intro e he; exact hsub e (List.mem_toFinset.1 he)
    · rw [List.toFinset_card_of_nodup hnd, hlen]
  have hinT : ∀ p ∈ F, ∃ i : Fin T.length, T[i.val] = p := by
    intro p hp
    have hp' : p ∈ T := by rw [← List.mem_toFinset, hTF]; exact hp
    obtain ⟨i, hi, hTi⟩ := List.mem_iff_getElem.1 hp'
    exact ⟨⟨i, hi⟩, hTi⟩
  have hLlen : (s :: T.map Prod.snd).length = T.length + 1 := by simp
  obtain ⟨x, hx⟩ : ∃ x : Fin (T.length + 1) → N,
      ∀ i, x i = (s :: T.map Prod.snd)[i.val]'(by rw [hLlen]; exact i.isLt) := ⟨_, fun _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Fin T.length → MixedArc N,
      ∀ i, a i = g72u_phi G (T[i.val]'i.isLt) := ⟨_, fun _ => rfl⟩
  have hTi : ∀ i : Fin T.length, T[i.val]'i.isLt = (x i.castSucc, x i.succ) := by
    intro i
    rw [hx, hx]
    exact g71u_tr_get T s s hT i.val i.isLt
  refine ⟨T.length, x, a, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hx, hx]
    simp only [Fin.val_zero, Fin.val_last]
    rw [g71u_tr_last T s s hT]; simp
  · intro i
    have h := hTi i
    have hmF := hsub _ (List.getElem_mem i.isLt)
    unfold MixedGraph.Traverses
    by_cases hd : T[i.val]'i.isLt ∈ G.dirArcs
    · left
      refine ⟨?_, ?_⟩
      · rw [ha, g72u_phi, if_pos hd, h]
      · rw [← h]; exact hd
    · right
      have hO' : T[i.val]'i.isLt ∈ O := by
        rcases Finset.mem_union.1 hmF with h' | h'
        · exact absurd h' hd
        · exact h'
      refine ⟨?_, ?_⟩
      · rw [ha, g72u_phi, if_neg hd, h]
      · have := hO.1 _ hO'; rw [h] at this; exact this
  · intro i j hij
    rw [ha, ha] at hij
    have := g72u_phi_inj G O hO (hsub _ (List.getElem_mem i.isLt))
      (hsub _ (List.getElem_mem j.isLt)) hij
    exact Fin.ext ((hnd.getElem_inj_iff).1 this)
  · intro e he
    rcases e with p | e
    · have hp : p ∈ G.dirArcs := he
      obtain ⟨i, hi⟩ := hinT p (Finset.mem_union_left _ hp)
      refine ⟨i, ?_⟩
      rw [ha, hi, g72u_phi, if_pos hp]
    · have he' : e ∈ G.undirArcs := he
      obtain ⟨p, hp, rfl⟩ := hO.2.1 e he'
      obtain ⟨i, hi⟩ := hinT p (Finset.mem_union_right _ hp)
      refine ⟨i, ?_⟩
      rw [ha, hi, g72u_phi, if_neg (hOD p hp)]
  · intro v
    by_cases hvs : v = s
    · refine ⟨0, ?_⟩; rw [hx]; simp [hvs]
    · rcases Relation.ReflTransGen.cases_head (hc.2 v s) with h | ⟨c, hvc, _⟩
      · exact absurd h hvs
      · rcases hadj v c hvc with h | h
        · obtain ⟨i, hi⟩ := hinT _ h
          have := hTi i
          rw [hi] at this
          exact ⟨i.castSucc, (congrArg Prod.fst this).symm⟩
        · obtain ⟨i, hi⟩ := hinT _ h
          have := hTi i
          rw [hi] at this
          exact ⟨i.succ, (congrArg Prod.snd this).symm⟩

theorem g72u_main (G : MixedGraph N) :
    G.Unicursal ↔
      G.Connected ∧ (∀ v : N, Even (G.degree v)) ∧
        ∀ X : Finset N, (G.dirOut X : ℤ) - (G.dirIn X : ℤ) ≤ (G.undirJoining X : ℤ) := by
  constructor
  · exact g71u_nec G
  · rintro ⟨hc, hev, hcut⟩
    obtain ⟨O, hO, hb⟩ := g72u_exists G hev hcut
    exact g72u_final G hc O hO hb

end g72uF

open FlowsNetworks.Graphs

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Theorem 7.1 (pp. 42–43). The mixed graph
`G = [N; 𝒜]` is unicursal if and only if (a) `G` is connected; (b) every node of `G` is incident
with an even number of arcs; (c) for every `X ⊆ N`, the number of directed arcs from `X` to `X̄`
minus the number of directed arcs from `X̄` to `X` is at most the number of undirected arcs
joining `X` and `X̄`. -/
theorem solution {N : Type} [Fintype N] [DecidableEq N] (G : MixedGraph N) :
    G.Unicursal ↔
      G.Connected ∧ (∀ v : N, Even (G.degree v)) ∧
        ∀ X : Finset N, (G.dirOut X : ℤ) - (G.dirIn X : ℤ) ≤ (G.undirJoining X : ℤ) := g72u_main G
