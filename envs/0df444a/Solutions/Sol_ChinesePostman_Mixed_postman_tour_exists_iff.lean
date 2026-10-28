-- Prove2me | solution 1 for ChinesePostman.Mixed.postman_tour_exists_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:15:21.795579+00:00
-- url     : https://prove2.me/submissions/58835346-06e2-4f62-b03c-5f4628a4a6ec

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Definitions.Def_ChinesePostman_Mixed_Setting

open ChinesePostman.Mixed

namespace ChinesePostman.Mixed.PostmanTourExistsIff

variable {V E : Type}

/-- Valid step of a mixed walk from `u` to `v` along edge `e`. -/
def ValidStep (G : MixedGraph V E) (e : E) (u v : V) : Prop :=
  (G.tail e = u ∧ G.head e = v) ∨ (G.directed e = false ∧ G.tail e = v ∧ G.head e = u)

/-- Valid step of an undirected walk from `u` to `v` along edge `e`. -/
def UndirStep (G : MixedGraph V E) (e : E) (u v : V) : Prop :=
  (G.tail e = u ∧ G.head e = v) ∨ (G.tail e = v ∧ G.head e = u)

lemma isMixedWalk_nil (G : MixedGraph V E) (u : V) : G.IsMixedWalk [u] [] :=
  ⟨rfl, fun _ h => by simp at h⟩

lemma isMixedWalk_cons {G : MixedGraph V E} {u v : V} {ns : List V} {e : E} {es : List E}
    (hstep : ValidStep G e u v) (hw : G.IsMixedWalk (v :: ns) es) :
    G.IsMixedWalk (u :: v :: ns) (e :: es) := by
  rcases hw with ⟨hlen, hwalk⟩
  refine ⟨by simp [hlen], fun i hi => ?_⟩
  rcases i with _ | i
  · exact hstep
  · exact hwalk i (Nat.lt_of_succ_lt_succ hi)

lemma isMixedWalk_uncons {G : MixedGraph V E} {u v : V} {ns : List V} {e : E} {es : List E}
    (hw : G.IsMixedWalk (u :: v :: ns) (e :: es)) :
    ValidStep G e u v ∧ G.IsMixedWalk (v :: ns) es := by
  rcases hw with ⟨hlen, hwalk⟩
  refine ⟨hwalk 0 (by simp), ⟨Nat.succ.inj hlen, fun i hi => ?_⟩⟩
  exact hwalk (i + 1) (Nat.succ_lt_succ hi)

lemma isMixedWalk_single {G : MixedGraph V E} {e : E} {u v : V} (hstep : ValidStep G e u v) :
    G.IsMixedWalk [u, v] [e] :=
  isMixedWalk_cons hstep (isMixedWalk_nil G v)

lemma isUndirWalkIn_uncons {G : MixedGraph V E} {P : E → Prop} {u v : V} {ns : List V}
    {e : E} {es : List E} (hw : G.IsUndirWalkIn P (u :: v :: ns) (e :: es)) :
    UndirStep G e u v ∧ G.IsUndirWalkIn P (v :: ns) es := by
  rcases hw with ⟨hlen, hwalk⟩
  refine ⟨(hwalk 0 (by simp)).2, ⟨Nat.succ.inj hlen, fun i hi => ?_⟩⟩
  exact hwalk (i + 1) (Nat.succ_lt_succ hi)

lemma isMixedWalk_append {G : MixedGraph V E} :
    ∀ {es₁ : List E} {ns₁ ns₂ : List V} {es₂ : List E} {u v w : V},
      G.IsMixedWalk ns₁ es₁ → ns₁.head? = some u → ns₁.getLast? = some v →
      G.IsMixedWalk ns₂ es₂ → ns₂.head? = some v → ns₂.getLast? = some w →
      ∃ ns, G.IsMixedWalk ns (es₁ ++ es₂) ∧ ns.head? = some u ∧ ns.getLast? = some w
  | [], ns₁, ns₂, es₂, u, v, w, hw₁, hh₁, hl₁, hw₂, hh₂, hl₂ => by
    rcases hw₁ with ⟨hlen, _⟩
    rcases ns₁ with _ | ⟨a, _ | _⟩ <;> simp at hlen
    simp only [List.head?_cons, Option.some.injEq] at hh₁
    simp only [List.getLast?_singleton, Option.some.injEq] at hl₁
    subst hh₁; subst hl₁
    exact ⟨ns₂, hw₂, hh₂, hl₂⟩
  | e :: es₁, ns₁, ns₂, es₂, u, v, w, hw₁, hh₁, hl₁, hw₂, hh₂, hl₂ => by
    rcases hw₁ with ⟨hlen, hwalk⟩
    rcases ns₁ with _ | ⟨a, _ | ⟨b, ns₁'⟩⟩ <;> simp at hlen
    have ⟨hstep, hw₁'⟩ := isMixedWalk_uncons ⟨by simp [hlen], hwalk⟩
    simp only [List.head?_cons, Option.some.injEq] at hh₁
    subst hh₁
    have hl₁' : (b :: ns₁').getLast? = some v := by simpa using hl₁
    rcases isMixedWalk_append hw₁' rfl hl₁' hw₂ hh₂ hl₂ with ⟨ns₃, hw₃, hh₃, hl₃⟩
    rcases ns₃ with _ | ⟨b', ns₃'⟩
    · simp at hh₃
    · simp only [List.head?_cons, Option.some.injEq] at hh₃
      subst b'
      refine ⟨a :: b :: ns₃', isMixedWalk_cons hstep hw₃, rfl, ?_⟩
      simpa using hl₃

lemma validStep_not_mem [DecidableEq V] {G : MixedGraph V E} {S : Finset V}
    (hcut : ∀ e, (G.tail e ∈ S ↔ G.head e ∉ S) → (G.directed e = true ∧ G.tail e ∈ S))
    {e : E} {u v : V} (hstep : ValidStep G e u v) (hu : u ∉ S) : v ∉ S := by
  intro hv
  rcases hstep with ⟨rfl, rfl⟩ | ⟨hdir, rfl, rfl⟩
  · exact hu (hcut e (by tauto)).2
  · have := (hcut e (by tauto)).1
    simp [hdir] at this

lemma isMixedWalk_forall_not_mem_of_head [DecidableEq V] {G : MixedGraph V E} {S : Finset V}
    (hcut : ∀ e, (G.tail e ∈ S ↔ G.head e ∉ S) → (G.directed e = true ∧ G.tail e ∈ S)) :
    ∀ {es : List E} {ns : List V} {u : V},
      G.IsMixedWalk ns es → ns.head? = some u → u ∉ S → ∀ x ∈ ns, x ∉ S
  | [], ns, u, ⟨hlen, _⟩, hh, hu, x, hx => by
    rcases ns with _ | ⟨a, _ | _⟩ <;> simp at hlen
    simp only [List.head?_cons, Option.some.injEq] at hh
    simp only [List.mem_singleton] at hx
    rwa [hx, hh]
  | e :: es, ns, u, ⟨hlen, hwalk⟩, hh, hu, x, hx => by
    rcases ns with _ | ⟨a, _ | ⟨b, ns'⟩⟩ <;> simp at hlen
    have ⟨hstep, hw'⟩ := isMixedWalk_uncons ⟨by simp [hlen], hwalk⟩
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst a
    have hb : b ∉ S := validStep_not_mem hcut hstep hu
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hu
    · exact isMixedWalk_forall_not_mem_of_head hcut hw' rfl hb x hx'

lemma isMixedWalk_getLast_not_mem_of_exists [DecidableEq V] {G : MixedGraph V E} {S : Finset V}
    (hcut : ∀ e, (G.tail e ∈ S ↔ G.head e ∉ S) → (G.directed e = true ∧ G.tail e ∈ S)) :
    ∀ {es : List E} {ns : List V} {w x : V},
      G.IsMixedWalk ns es → ns.getLast? = some w → x ∈ ns → x ∉ S → w ∉ S
  | [], ns, w, x, ⟨hlen, _⟩, hl, hx, hnx => by
    rcases ns with _ | ⟨a, _ | _⟩ <;> simp at hlen
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    simp only [List.mem_singleton] at hx
    rwa [← hl, ← hx]
  | e :: es, ns, w, x, ⟨hlen, hwalk⟩, hl, hx, hnx => by
    rcases ns with _ | ⟨a, _ | ⟨b, ns'⟩⟩ <;> simp at hlen
    have ⟨hstep, hw'⟩ := isMixedWalk_uncons ⟨by simp [hlen], hwalk⟩
    have hl' : (b :: ns').getLast? = some w := by simpa using hl
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact isMixedWalk_forall_not_mem_of_head hcut hw' rfl (validStep_not_mem hcut hstep hnx)
        w (List.mem_of_getLast? hl')
    · exact isMixedWalk_getLast_not_mem_of_exists hcut hw' hl' hx' hnx

lemma isMixedWalk_endpoints_mem {G : MixedGraph V E} :
    ∀ {es : List E} {ns : List V} {e : E},
      G.IsMixedWalk ns es → e ∈ es → G.tail e ∈ ns ∧ G.head e ∈ ns
  | [], _, _, _, he => by simp at he
  | e₀ :: es, ns, e, ⟨hlen, hwalk⟩, he => by
    rcases ns with _ | ⟨a, _ | ⟨b, ns'⟩⟩ <;> simp at hlen
    have ⟨hstep, hw'⟩ := isMixedWalk_uncons ⟨by simp [hlen], hwalk⟩
    rcases List.mem_cons.mp he with rfl | he'
    · rcases hstep with ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> simp
    · obtain ⟨ht, hh⟩ := isMixedWalk_endpoints_mem hw' he'
      exact ⟨List.mem_cons_of_mem a ht, List.mem_cons_of_mem a hh⟩

lemma isUndirWalkIn_exists_cut_edge [DecidableEq V] {G : MixedGraph V E} {P : E → Prop}
    {S : Finset V} :
    ∀ {es : List E} {ns : List V} {u v : V},
      G.IsUndirWalkIn P ns es → ns.head? = some u → ns.getLast? = some v →
      u ∈ S → v ∉ S → ∃ e : E, G.tail e ∈ S ↔ G.head e ∉ S
  | [], ns, u, v, ⟨hlen, _⟩, hh, hl, hu, hv => by
    rcases ns with _ | ⟨a, _ | _⟩ <;> simp at hlen
    simp only [List.head?_cons, Option.some.injEq] at hh
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst u; subst v
    exact (hv hu).elim
  | e :: es, ns, u, v, ⟨hlen, hwalk⟩, hh, hl, hu, hv => by
    rcases ns with _ | ⟨a, _ | ⟨b, ns'⟩⟩ <;> simp at hlen
    have ⟨hstep, hw'⟩ := isUndirWalkIn_uncons ⟨by simp [hlen], hwalk⟩
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst a
    by_cases hb : b ∈ S
    · exact isUndirWalkIn_exists_cut_edge hw' rfl (by simpa using hl) hb hv
    · refine ⟨e, ?_⟩
      rcases hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto

/-- Reachability by a mixed walk. -/
def Reach (G : MixedGraph V E) (u v : V) : Prop :=
  ∃ ns es, G.IsMixedWalk ns es ∧ ns.head? = some u ∧ ns.getLast? = some v

lemma reach_refl (G : MixedGraph V E) (u : V) : Reach G u u :=
  ⟨[u], [], isMixedWalk_nil G u, rfl, rfl⟩

lemma reach_trans {G : MixedGraph V E} {u v w : V} (h₁ : Reach G u v) (h₂ : Reach G v w) :
    Reach G u w := by
  rcases h₁ with ⟨ns₁, es₁, hw₁, hh₁, hl₁⟩
  rcases h₂ with ⟨ns₂, es₂, hw₂, hh₂, hl₂⟩
  rcases isMixedWalk_append hw₁ hh₁ hl₁ hw₂ hh₂ hl₂ with ⟨ns, hw, hh, hl⟩
  exact ⟨ns, es₁ ++ es₂, hw, hh, hl⟩

lemma reach_step {G : MixedGraph V E} {e : E} {u v : V} (hstep : ValidStep G e u v) :
    Reach G u v :=
  ⟨[u, v], [e], isMixedWalk_single hstep, rfl, rfl⟩

lemma reach_all [Fintype V] [DecidableEq V] {G : MixedGraph V E}
    (hno_cut : ¬ ∃ S : Finset V, S.Nonempty ∧ S ≠ Finset.univ ∧
      ∀ e, (G.tail e ∈ S ↔ G.head e ∉ S) → (G.directed e = true ∧ G.tail e ∈ S))
    (u v : V) : Reach G u v := by
   classical
  by_contra hnr
  apply hno_cut
  let S : Finset V := Finset.univ.filter (fun x => ¬ Reach G u x)
  have mem_S : ∀ x, x ∈ S ↔ ¬ Reach G u x := by simp [S]
  refine ⟨S, ⟨v, (mem_S v).mpr hnr⟩, ?_, ?_⟩
  · intro hSu
    have : u ∈ S := hSu ▸ Finset.mem_univ u
    exact (mem_S u).mp this (reach_refl G u)
  · intro e he
    have ht : G.tail e ∈ S := by
      by_contra hnt
      have hu_tail : Reach G u (G.tail e) := not_not.mp ((mem_S (G.tail e)).not.mp hnt)
      have hhead_S : G.head e ∈ S := not_not.mp (he.not.mp hnt)
      exact (mem_S (G.head e)).mp hhead_S
        (reach_trans hu_tail (reach_step (Or.inl ⟨rfl, rfl⟩)))
    have hnh : G.head e ∉ S := he.mp ht
    have hu_head : Reach G u (G.head e) := not_not.mp ((mem_S (G.head e)).not.mp hnh)
    have hdir : G.directed e = true := by
      cases h : G.directed e
      · exfalso
        exact (mem_S (G.tail e)).mp ht
          (reach_trans hu_head (reach_step (Or.inr ⟨h, rfl, rfl⟩)))
      · rfl
    exact ⟨hdir, ht⟩

lemma closed_walk_covering_list {G : MixedGraph V E} (r : V) (hreach : ∀ u v : V, Reach G u v) :
    ∀ L : List E, ∃ ns es, G.IsMixedWalk ns es ∧
      ns.head? = some r ∧ ns.getLast? = some r ∧ ∀ e ∈ L, e ∈ es
  | [] => ⟨[r], [], isMixedWalk_nil G r, rfl, rfl, by simp⟩
  | e :: L => by
    rcases closed_walk_covering_list r hreach L with ⟨ns₀, es₀, hw₀, hh₀, hl₀, hcov₀⟩
    rcases hreach r (G.tail e) with ⟨ns₁, es₁, hw₁, hh₁, hl₁⟩
    rcases hreach (G.head e) r with ⟨ns₂, es₂, hw₂, hh₂, hl₂⟩
    have hw_e : G.IsMixedWalk [G.tail e, G.head e] [e] :=
      isMixedWalk_single (Or.inl ⟨rfl, rfl⟩)
    rcases isMixedWalk_append hw₁ hh₁ hl₁ hw_e rfl rfl with ⟨ns₃, hw₃, hh₃, hl₃⟩
    rcases isMixedWalk_append hw₃ hh₃ hl₃ hw₂ hh₂ hl₂ with ⟨ns₄, hw₄, hh₄, hl₄⟩
    rcases isMixedWalk_append hw₀ hh₀ hl₀ hw₄ hh₄ hl₄ with ⟨ns, hw, hh, hl⟩
    refine ⟨ns, es₀ ++ (es₁ ++ [e] ++ es₂), hw, hh, hl, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp
    · simp [hcov₀ x hx']

end ChinesePostman.Mixed.PostmanTourExistsIff

open ChinesePostman.Mixed.PostmanTourExistsIff

/-- §7, p. 120: a connected mixed graph has a postman tour if and only if there is no proper
(nonempty) subset `S` of nodes such that every edge meeting one node in `S` and one node not in
`S` is directed away from the node in `S`. -/
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] [Nonempty V] (G : MixedGraph V E) (hconn : G.Connected) :
    (∃ ns es, G.IsMixedPostmanTour ns es) ↔
      ¬ ∃ S : Finset V, S.Nonempty ∧ S ≠ Finset.univ ∧
        ∀ e, (G.tail e ∈ S ↔ G.head e ∉ S) → (G.directed e = true ∧ G.tail e ∈ S) := by
  constructor
  · rintro ⟨ns, es, ⟨hw, htour⟩, hall⟩ ⟨S, ⟨u, hu⟩, hSu, hcut⟩
    have ⟨v, hv⟩ : ∃ v : V, v ∉ S := by
      by_contra! hall_S
      exact hSu (Finset.eq_univ_iff_forall.mpr hall_S)
    rcases hconn u v with ⟨ns', es', hw', hh', hl'⟩
    rcases isUndirWalkIn_exists_cut_edge hw' hh' hl' hu hv with ⟨e, he⟩
    obtain ⟨ht_mem, hh_mem⟩ := isMixedWalk_endpoints_mem hw (hall e)
    have ⟨x, hx_ns, hx_S, y, hy_ns, hy_nS⟩ :
        ∃ x ∈ ns, x ∈ S ∧ ∃ y ∈ ns, y ∉ S := by
      by_cases ht : G.tail e ∈ S
      · exact ⟨G.tail e, ht_mem, ht, G.head e, hh_mem, he.mp ht⟩
      · exact ⟨G.head e, hh_mem, not_not.mp (he.not.mp ht), G.tail e, ht_mem, ht⟩
    rcases hw with ⟨hlen, hwalk⟩
    rcases ns with _ | ⟨r, ns_tl⟩
    · simp at hlen
    have hh : (r :: ns_tl).head? = some r := rfl
    have hl : (r :: ns_tl).getLast? = some r := htour.symm.trans hh
    have hr_nS : r ∉ S :=
      isMixedWalk_getLast_not_mem_of_exists hcut ⟨hlen, hwalk⟩ hl hy_ns hy_nS
    exact isMixedWalk_forall_not_mem_of_head hcut ⟨hlen, hwalk⟩ hh hr_nS x hx_ns hx_S
  · intro hno_cut
    obtain ⟨r⟩ := ‹Nonempty V›
    rcases closed_walk_covering_list r (reach_all hno_cut) Finset.univ.toList with
      ⟨ns, es, hw, hh, hl, hcov⟩
    exact ⟨ns, es, ⟨hw, hh.trans hl.symm⟩, fun e => hcov e (Finset.mem_toList.mpr (Finset.mem_univ e))⟩
