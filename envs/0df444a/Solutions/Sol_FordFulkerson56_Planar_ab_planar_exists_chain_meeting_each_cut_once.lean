-- Prove2me | solution 1 for FordFulkerson56.Planar.ab_planar_exists_chain_meeting_each_cut_once
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T05:39:33.037362+00:00
-- url     : https://prove2.me/submissions/5ddfcfbb-9655-4aae-9993-280de7705a8c

import Mathlib.Data.Finset.Card
import Mathlib.Data.List.TakeDrop
import Mathlib.Logic.Relation
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting
import Definitions.Def_FordFulkerson56_Planar_ABPlaneDrawing
import Theorems.Thm_FordFulkerson56_Planar_exists_chain_meeting_cut_only_at
import Theorems.Thm_FordFulkerson56_Planar_ab_planar_exists_topmost_chain_walk

open FordFulkerson56.MinCut
open FordFulkerson56.Planar

namespace SolFordFulkerson56Planar

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

private def Step (N : Network V E) (e : E) (u v : V) : Prop :=
  (u = N.tail e ∧ v = N.head e) ∨ (u = N.head e ∧ v = N.tail e)

private theorem step_symm {N : Network V E} {e : E} {u v : V} (h : Step N e u v) :
    Step N e v u := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

private theorem step_endpoints_cases {N : Network V E} {e : E} {x₁ y₁ x₂ y₂ : V}
    (h1 : Step N e x₁ y₁) (h2 : Step N e x₂ y₂) :
    (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = y₂ ∧ y₁ = x₂) := by
  rcases h1 with ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩ <;> rcases h2 with ⟨hx2, hy2⟩ | ⟨hx2, hy2⟩
  · exact Or.inl ⟨hx1.trans hx2.symm, hy1.trans hy2.symm⟩
  · exact Or.inr ⟨hx1.trans hy2.symm, hy1.trans hx2.symm⟩
  · exact Or.inr ⟨hx1.trans hy2.symm, hy1.trans hx2.symm⟩
  · exact Or.inl ⟨hx1.trans hx2.symm, hy1.trans hy2.symm⟩

private def AdjAvoiding (N : Network V E) (D : Finset E) (u v : V) : Prop :=
  ∃ e : E, e ∉ D ∧ Step N e u v

private theorem adjAvoiding_symm {N : Network V E} {D : Finset E} {u v : V}
    (h : AdjAvoiding N D u v) : AdjAvoiding N D v u := by
  rcases h with ⟨e, he, hstep⟩
  exact ⟨e, he, step_symm hstep⟩

private theorem reaches_symm {N : Network V E} {D : Finset E} {u v : V}
    (h : Relation.ReflTransGen (AdjAvoiding N D) u v) :
    Relation.ReflTransGen (AdjAvoiding N D) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hadj ih => exact Relation.ReflTransGen.head (adjAvoiding_symm hadj) ih

private theorem chainWalk_head_eq {N : Network V E} {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) :
    ∃ (h0 : 0 < vs.length), vs[0]'h0 = u := by
  have h0 : 0 < vs.length := by have := hw.1; omega
  refine ⟨h0, ?_⟩
  have hhead := hw.2.1
  rw [List.head?_eq_getElem?] at hhead
  rw [List.getElem?_eq_getElem h0] at hhead
  exact Option.some.inj hhead

private theorem chainWalk_last_eq {N : Network V E} {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) :
    ∃ (hl : p.length < vs.length), vs[p.length]'hl = w := by
  have hl : p.length < vs.length := by have := hw.1; omega
  refine ⟨hl, ?_⟩
  have hlast := hw.2.2.1
  rw [List.getLast?_eq_getElem?] at hlast
  have hidx : vs.length - 1 = p.length := by have := hw.1; omega
  rw [hidx, List.getElem?_eq_getElem hl] at hlast
  exact Option.some.inj hlast

private theorem chainWalk_step_at {N : Network V E} {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) (i : ℕ) (hi : i < p.length) :
    Step N (p[i]'hi) (vs[i]'(by have := hw.1; omega)) (vs[i + 1]'(by have := hw.1; omega)) := by
  have hi_vs : i < vs.length := by have := hw.1; omega
  have hi1_vs : i + 1 < vs.length := by have := hw.1; omega
  have hstep := hw.2.2.2.2.2 i hi
  rw [List.getElem?_eq_getElem hi_vs, List.getElem?_eq_getElem hi1_vs] at hstep
  rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨Option.some.inj h1, Option.some.inj h2⟩
  · exact Or.inr ⟨Option.some.inj h1, Option.some.inj h2⟩

private theorem isChainWalk_drop {N : Network V E} {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) (k : ℕ) (hk : k < vs.length) :
    IsChainWalk N (vs[k]'hk) w (p.drop k) (vs.drop k) := by
  have hlen : (vs.drop k).length = (p.drop k).length + 1 := by
    simp only [List.length_drop]
    have := hw.1
    omega
  refine ⟨hlen, ?_, ?_, hw.2.2.2.1.sublist (List.drop_sublist _ _),
    hw.2.2.2.2.1.sublist (List.drop_sublist _ _), ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hk]
  · obtain ⟨hl, hlast_eq⟩ := chainWalk_last_eq hw
    rw [List.getLast?_eq_getElem?]
    have hidx : (vs.drop k).length - 1 = p.length - k := by
      simp only [List.length_drop]
      have := hw.1
      omega
    have hk_p : k + (p.length - k) = p.length := by have := hw.1; omega
    rw [hidx, List.getElem?_drop, hk_p, List.getElem?_eq_getElem hl, hlast_eq]
  · intro i hi
    simp only [List.length_drop] at hi
    have hki : k + i < p.length := by omega
    have hki_vs : k + i < vs.length := by have := hw.1; omega
    have hki1_vs : k + (i + 1) < vs.length := by have := hw.1; omega
    have hstep := hw.2.2.2.2.2 (k + i) hki
    rw [List.getElem?_drop, List.getElem?_drop]
    simpa [Nat.add_assoc, List.getElem_drop] using hstep

private theorem isChainWalk_cons {N : Network V E} {u v w : V} {e₀ : E} {p : List E} {vs : List V}
    (hw : IsChainWalk N v w p vs) (he₀ : Step N e₀ u v) (hu : u ∉ vs) :
    IsChainWalk N u w (e₀ :: p) (u :: vs) := by
  have hlen : (u :: vs).length = (e₀ :: p).length + 1 := by
    simp [hw.1]
  have he₀_not_mem : e₀ ∉ p := by
    intro hmem
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
    have hstep_i := chainWalk_step_at hw i hi
    have hcases := step_endpoints_cases he₀ hstep_i
    rcases hcases with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hu (List.getElem_mem _)
    · exact hu (List.getElem_mem _)
  refine ⟨hlen, rfl, ?_, List.nodup_cons.mpr ⟨hu, hw.2.2.2.1⟩,
    List.nodup_cons.mpr ⟨he₀_not_mem, hw.2.2.2.2.1⟩, ?_⟩
  · cases vs with
    | nil =>
      have := hw.1
      simp at this
    | cons x xs =>
      simpa using hw.2.2.1
  · intro i hi
    cases i with
    | zero =>
      obtain ⟨h0, hv0⟩ := chainWalk_head_eq hw
      have h1 : (u :: vs)[1]? = some v := by
        simp [List.getElem?_eq_getElem h0, hv0]
      rcases he₀ with ⟨hu_eq, hv_eq⟩ | ⟨hu_eq, hv_eq⟩
      · left
        exact ⟨by simp [hu_eq], by simpa [hv_eq] using h1⟩
      · right
        exact ⟨by simp [hu_eq], by simpa [hv_eq] using h1⟩
    | succ j =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      simpa using hw.2.2.2.2.2 j hi

private theorem exists_chainWalk_avoiding_of_reaches {N : Network V E} {D : Finset E} {u w : V}
    (h : Relation.ReflTransGen (AdjAvoiding N D) u w) :
    ∃ (q : List E) (ws : List V),
      IsChainWalk N u w q ws ∧ ∀ e ∈ q, e ∉ D := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨[], [w], ?_, by simp⟩
    refine ⟨rfl, rfl, rfl, List.nodup_singleton w, List.nodup_nil, ?_⟩
    intro i hi
    simp at hi
  | @head x y hadj _ ih =>
    rcases hadj with ⟨e₀, he₀_not_D, hstep₀⟩
    rcases ih with ⟨q, ws, hw, hq_avoid⟩
    by_cases hx : x ∈ ws
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      refine ⟨q.drop k, ws.drop k, isChainWalk_drop hw k hk, ?_⟩
      intro e he
      exact hq_avoid e (List.mem_of_mem_drop he)
    · refine ⟨e₀ :: q, x :: ws, isChainWalk_cons hw hstep₀ hx, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · exact he₀_not_D
      · exact hq_avoid e he'

private theorem reaches_of_subwalk_avoiding_aux {N : Network V E} {D : Finset E}
    {u w : V} {q : List E} {ws : List V} (hw : IsChainWalk N u w q ws) :
    ∀ (d a : ℕ) (hab : a + d < ws.length),
      (∀ (k : ℕ) (hk : k < q.length), a ≤ k → k < a + d → q[k]'hk ∉ D) →
      Relation.ReflTransGen (AdjAvoiding N D) (ws[a]'(by omega)) (ws[a + d]'hab)
  | 0, a, hab, _ => by
    simp only [Nat.add_zero]
    exact Relation.ReflTransGen.refl
  | d + 1, a, hab, havoid => by
    have had : a + d < ws.length := by omega
    have had_q : a + d < q.length := by have := hw.1; omega
    have hprev := reaches_of_subwalk_avoiding_aux hw d a had (fun k hk h1 h2 =>
      havoid k hk h1 (by omega))
    have hstep : AdjAvoiding N D (ws[a + d]'had) (ws[a + d + 1]'hab) := by
      refine ⟨q[a + d]'had_q, havoid (a + d) had_q (by omega) (by omega), ?_⟩
      exact chainWalk_step_at hw (a + d) had_q
    exact Relation.ReflTransGen.tail hprev hstep

private theorem reaches_of_subwalk_avoiding {N : Network V E} {D : Finset E}
    {u w : V} {q : List E} {ws : List V} (hw : IsChainWalk N u w q ws)
    (a b : ℕ) (hab : a ≤ b) (hb : b < ws.length)
    (havoid : ∀ (k : ℕ) (hk : k < q.length), a ≤ k → k < b → q[k]'hk ∉ D) :
    Relation.ReflTransGen (AdjAvoiding N D) (ws[a]'(by omega)) (ws[b]'hb) := by
  have hbd : a + (b - a) = b := Nat.add_sub_of_le hab
  have hb' : a + (b - a) < ws.length := hbd.symm ▸ hb
  have h := reaches_of_subwalk_avoiding_aux hw (b - a) a hb' (by
    intro k hk h1 h2
    exact havoid k hk h1 (by omega))
  simpa [hbd] using h

private theorem reaches_of_mem_chainWalk_avoiding {N : Network V E} {D : Finset E}
    {u w : V} {q : List E} {ws : List V} (hw : IsChainWalk N u w q ws)
    (havoid : ∀ e ∈ q, e ∉ D) {x : V} (hx : x ∈ ws) :
    Relation.ReflTransGen (AdjAvoiding N D) u x ∧
    Relation.ReflTransGen (AdjAvoiding N D) x w := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨h0, hu0⟩ := chainWalk_head_eq hw
  obtain ⟨hl, hwl⟩ := chainWalk_last_eq hw
  have hk_le_l : k ≤ q.length := by have := hw.1; omega
  have h1 := reaches_of_subwalk_avoiding hw 0 k (Nat.zero_le k) hk
    (fun m hm _ _ => havoid (q[m]'hm) (List.getElem_mem _))
  have h2 := reaches_of_subwalk_avoiding hw k q.length hk_le_l hl
    (fun m hm _ _ => havoid (q[m]'hm) (List.getElem_mem _))
  rw [hu0] at h1
  rw [hwl] at h2
  exact ⟨h1, h2⟩

private theorem not_reaches_source_sink {N : Network V E} {D : Finset E}
    (hD : IsDisconnecting N D) :
    ¬ Relation.ReflTransGen (AdjAvoiding N D) N.source N.sink := by
  intro hreach
  obtain ⟨q, ws, hw, havoid⟩ := exists_chainWalk_avoiding_of_reaches hreach
  have hchain : IsChain N N.source N.sink q.toFinset := ⟨q, ws, hw, rfl⟩
  obtain ⟨e, he⟩ := hD q.toFinset hchain
  rw [Finset.mem_inter, List.mem_toFinset] at he
  exact havoid e he.1 he.2

private theorem cut_arc_split_reaches {N : Network V E} {D : Finset E}
    (hD : IsCut N D) {α : E} (hα : α ∈ D) :
    ∃ x y : V, Step N α x y ∧
      Relation.ReflTransGen (AdjAvoiding N D) N.source x ∧
      Relation.ReflTransGen (AdjAvoiding N D) y N.sink := by
  obtain ⟨C, ⟨q, ws, hw, rfl⟩, hCD⟩ := exists_chain_meeting_cut_only_at N D hD α hα
  have hα_in_CD : α ∈ q.toFinset ∩ D := by rw [hCD]; exact Finset.mem_singleton_self α
  have hα_in_q : α ∈ q := List.mem_toFinset.mp (Finset.mem_of_mem_inter_left hα_in_CD)
  obtain ⟨k, hk, hk_eq⟩ := List.getElem_of_mem hα_in_q
  have havoid_ne : ∀ (m : ℕ) (hm : m < q.length), m ≠ k → q[m]'hm ∉ D := by
    intro m hm hne hmemD
    have hmem_inter : q[m]'hm ∈ q.toFinset ∩ D :=
      Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem _), hmemD⟩
    rw [hCD, Finset.mem_singleton] at hmem_inter
    have heq : q[m]'hm = q[k]'hk := hmem_inter.trans hk_eq.symm
    exact hne ((List.Nodup.getElem_inj_iff hw.2.2.2.2.1).mp heq)
  obtain ⟨h0, hu0⟩ := chainWalk_head_eq hw
  obtain ⟨hl, hwl⟩ := chainWalk_last_eq hw
  have hk_ws : k < ws.length := by have := hw.1; omega
  have hk1_ws : k + 1 < ws.length := by have := hw.1; omega
  have hreach1 := reaches_of_subwalk_avoiding hw 0 k (Nat.zero_le k) hk_ws
    (fun m hm _ hlt => havoid_ne m hm (by omega))
  have hreach2 := reaches_of_subwalk_avoiding hw (k + 1) q.length (by omega) hl
    (fun m hm hge _ => havoid_ne m hm (by omega))
  rw [hu0] at hreach1
  rw [hwl] at hreach2
  have hstep : Step N α (ws[k]'hk_ws) (ws[k + 1]'hk1_ws) := by
    rw [← hk_eq]
    exact chainWalk_step_at hw k hk
  exact ⟨ws[k]'hk_ws, ws[k + 1]'hk1_ws, hstep, hreach1, hreach2⟩

private theorem exists_first_two_cut_indices {p : List E} {D : Finset E}
    (hcard : 1 < (p.toFinset ∩ D).card) :
    ∃ (i₁ i₂ : ℕ) (hi₁ : i₁ < p.length) (hi₂ : i₂ < p.length),
      i₁ < i₂ ∧ p[i₁]'hi₁ ∈ D ∧ p[i₂]'hi₂ ∈ D ∧
      (∀ (k : ℕ) (hk : k < p.length), k < i₁ → p[k]'hk ∉ D) ∧
      (∀ (k : ℕ) (hk : k < p.length), i₁ < k → k < i₂ → p[k]'hk ∉ D) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  have ha_mem : a ∈ p := List.mem_toFinset.mp (Finset.mem_of_mem_inter_left ha)
  have ha_D : a ∈ D := Finset.mem_of_mem_inter_right ha
  have hb_mem : b ∈ p := List.mem_toFinset.mp (Finset.mem_of_mem_inter_left hb)
  have hb_D : b ∈ D := Finset.mem_of_mem_inter_right hb
  obtain ⟨ia, hia, rfl⟩ := List.getElem_of_mem ha_mem
  obtain ⟨ib, hib, rfl⟩ := List.getElem_of_mem hb_mem
  have hne_idx : ia ≠ ib := by
    intro heq
    apply hab
    congr 1
  have hex1 : ∃ i : ℕ, ∃ hi : i < p.length, p[i]'hi ∈ D := ⟨ia, hia, ha_D⟩
  let i₁ := Nat.find hex1
  have hi₁_spec : ∃ hi : i₁ < p.length, p[i₁]'hi ∈ D := Nat.find_spec hex1
  rcases hi₁_spec with ⟨hi₁, hi₁_D⟩
  have hi₁_min : ∀ (k : ℕ) (hk : k < p.length), k < i₁ → p[k]'hk ∉ D := by
    intro k hk hlt hD
    exact Nat.find_min hex1 hlt ⟨hk, hD⟩
  have hex2 : ∃ i : ℕ, i₁ < i ∧ ∃ hi : i < p.length, p[i]'hi ∈ D := by
    have hia_ge : i₁ ≤ ia := Nat.find_min' hex1 ⟨hia, ha_D⟩
    have hib_ge : i₁ ≤ ib := Nat.find_min' hex1 ⟨hib, hb_D⟩
    rcases Nat.eq_or_lt_of_le hia_ge with rfl | hlt_a
    · exact ⟨ib, Nat.lt_of_le_of_ne hib_ge hne_idx, hib, hb_D⟩
    · exact ⟨ia, hlt_a, hia, ha_D⟩
  let i₂ := Nat.find hex2
  have hi₂_spec : i₁ < i₂ ∧ ∃ hi : i₂ < p.length, p[i₂]'hi ∈ D := Nat.find_spec hex2
  rcases hi₂_spec with ⟨hi₁₂, hi₂, hi₂_D⟩
  have hi₂_min : ∀ (k : ℕ) (hk : k < p.length), i₁ < k → k < i₂ → p[k]'hk ∉ D := by
    intro k hk hgt hlt hD
    exact Nat.find_min hex2 hlt ⟨hgt, hk, hD⟩
  exact ⟨i₁, i₂, hi₁, hi₂, hi₁₂, hi₁_D, hi₂_D, hi₁_min, hi₂_min⟩

end SolFordFulkerson56Planar

open SolFordFulkerson56Planar

theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : FordFulkerson56.MinCut.Network V E)
    (hno_ab : ∀ e : E, ¬ ((N.tail e = N.source ∧ N.head e = N.sink) ∨
      (N.tail e = N.sink ∧ N.head e = N.source)))
    (hconn : ∃ C : Finset E, FordFulkerson56.MinCut.IsChain N N.source N.sink C)
    (hplanar : Nonempty (ABPlaneDrawing N)) :
    ∃ T : Finset E, FordFulkerson56.MinCut.IsChain N N.source N.sink T ∧
      ∀ D : Finset E, FordFulkerson56.MinCut.IsCut N D → (T ∩ D).card = 1 := by
  obtain ⟨p, vs, hT_walk, hcross⟩ :=
    ab_planar_exists_topmost_chain_walk N hno_ab hconn hplanar
  refine ⟨p.toFinset, ⟨p, vs, hT_walk, rfl⟩, ?_⟩
  intro D hD
  have hnonempty : (p.toFinset ∩ D).Nonempty := hD.1 p.toFinset ⟨p, vs, hT_walk, rfl⟩
  have hge1 : 1 ≤ (p.toFinset ∩ D).card := Finset.card_pos.mpr hnonempty
  by_contra hne1
  have hgt1 : 1 < (p.toFinset ∩ D).card := Nat.lt_of_le_of_ne hge1 (Ne.symm hne1)
  have hno_reach : ¬ Relation.ReflTransGen (AdjAvoiding N D) N.source N.sink :=
    not_reaches_source_sink hD.1
  obtain ⟨i₁, i₂, hi₁, hi₂, hi₁₂, hα₁, hα₂, hmin₁, hmin₂⟩ :=
    exists_first_two_cut_indices hgt1
  obtain ⟨h0, hu0⟩ := chainWalk_head_eq hT_walk
  obtain ⟨hl, hwl⟩ := chainWalk_last_eq hT_walk
  have hi₁_vs : i₁ < vs.length := by have := hT_walk.1; omega
  have hi₁1_vs : i₁ + 1 < vs.length := by have := hT_walk.1; omega
  have hi₂_vs : i₂ < vs.length := by have := hT_walk.1; omega
  have hi₂1_vs : i₂ + 1 < vs.length := by have := hT_walk.1; omega
  -- Prefix 0 .. i₁ avoids D
  have hreach_src_u1 : Relation.ReflTransGen (AdjAvoiding N D) N.source (vs[i₁]'hi₁_vs) := by
    have h := reaches_of_subwalk_avoiding hT_walk 0 i₁ (Nat.zero_le i₁) hi₁_vs
      (fun k hk _ hlt => hmin₁ k hk hlt)
    simpa [hu0] using h
  -- Segment i₁ + 1 .. i₂ avoids D
  have hreach_v1_u2 : Relation.ReflTransGen (AdjAvoiding N D) (vs[i₁ + 1]'hi₁1_vs) (vs[i₂]'hi₂_vs) :=
    reaches_of_subwalk_avoiding hT_walk (i₁ + 1) i₂ (by omega) hi₂_vs
      (fun k hk hge hlt => hmin₂ k hk (by omega) hlt)
  -- Cut arc α₁ = p[i₁] gives chain C₁ meeting D only at α₁
  obtain ⟨x₁, y₁, hstep₁, hsrc_x₁, hy₁_snk⟩ := cut_arc_split_reaches hD hα₁
  have hT_step₁ : Step N (p[i₁]'hi₁) (vs[i₁]'hi₁_vs) (vs[i₁ + 1]'hi₁1_vs) :=
    chainWalk_step_at hT_walk i₁ hi₁
  have hreach_v1_snk : Relation.ReflTransGen (AdjAvoiding N D) (vs[i₁ + 1]'hi₁1_vs) N.sink := by
    rcases step_endpoints_cases hT_step₁ hstep₁ with ⟨_, rfl⟩ | ⟨h_u1_y1, _⟩
    · exact hy₁_snk
    · exfalso
      rw [← h_u1_y1] at hy₁_snk
      exact hno_reach (Relation.ReflTransGen.trans hreach_src_u1 hy₁_snk)
  have hreach_u2_snk : Relation.ReflTransGen (AdjAvoiding N D) (vs[i₂]'hi₂_vs) N.sink :=
    Relation.ReflTransGen.trans (reaches_symm hreach_v1_u2) hreach_v1_snk
  -- Cut arc α₂ = p[i₂] gives chain C₂ meeting D only at α₂
  obtain ⟨x₂, y₂, hstep₂, hsrc_x₂, hy₂_snk⟩ := cut_arc_split_reaches hD hα₂
  have hT_step₂ : Step N (p[i₂]'hi₂) (vs[i₂]'hi₂_vs) (vs[i₂ + 1]'hi₂1_vs) :=
    chainWalk_step_at hT_walk i₂ hi₂
  have hreach_src_v2 : Relation.ReflTransGen (AdjAvoiding N D) N.source (vs[i₂ + 1]'hi₂1_vs) := by
    rcases step_endpoints_cases hT_step₂ hstep₂ with ⟨h_u2_x2, _⟩ | ⟨_, h_v2_x2⟩
    · exfalso
      rw [← h_u2_x2] at hsrc_x₂
      exact hno_reach (Relation.ReflTransGen.trans hsrc_x₂ hreach_u2_snk)
    · simpa [h_v2_x2] using hsrc_x₂
  -- Now j₁ = i₁ + 1 and j₂ = i₂ + 1
  by_cases hj₂_last : i₂ + 1 = p.length
  · have hv2_eq_snk : vs[i₂ + 1]'hi₂1_vs = N.sink := by
      simpa [hj₂_last] using hwl
    rw [hv2_eq_snk] at hreach_src_v2
    exact hno_reach hreach_src_v2
  · have hj₂_lt : (i₂ + 1) + 1 < vs.length := by
      have := hT_walk.1
      omega
    obtain ⟨p₁, vs₁, hw₁, havoid₁⟩ := exists_chainWalk_avoiding_of_reaches hreach_v1_snk
    obtain ⟨p₂, vs₂, hw₂, havoid₂⟩ := exists_chainWalk_avoiding_of_reaches hreach_src_v2
    obtain ⟨w, hw_mem₁, hw_mem₂⟩ :=
      hcross (i₁ + 1) (i₂ + 1) (by omega) (by omega) hj₂_lt p₁ p₂ vs₁ vs₂ hw₁ hw₂
    have hsrc_w := (reaches_of_mem_chainWalk_avoiding hw₂ havoid₂ hw_mem₂).1
    have hw_snk := (reaches_of_mem_chainWalk_avoiding hw₁ havoid₁ hw_mem₁).2
    exact hno_reach (Relation.ReflTransGen.trans hsrc_w hw_snk)
