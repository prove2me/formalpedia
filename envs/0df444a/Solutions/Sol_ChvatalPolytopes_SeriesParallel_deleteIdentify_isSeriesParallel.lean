-- Prove2me | solution 1 for ChvatalPolytopes.SeriesParallel.deleteIdentify_isSeriesParallel
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:47:01.881997+00:00
-- url     : https://prove2.me/submissions/cde4be65-84c3-418d-b2ba-e40051abc57a

import Mathlib
import Definitions.Def_ChvatalPolytopes_SeriesParallel_IsSeriesParallel
import Definitions.Def_ChvatalPolytopes_SeriesParallel_deleteIdentify



namespace ChvatalPolytopes.SeriesParallel

namespace DIAux

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (u v w : V)

def RS (z : V) : Prop := z = u ∨ z = v ∨ z = w

lemma val_RS {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) (x : {x : V // x ≠ u ∧ x ≠ w}) :
    RS u v w x.1 ↔ x = v' := by
  constructor
  · rintro (h | h | h)
    · exact absurd h x.2.1
    · exact Subtype.ext (h.trans hv'.symm)
    · exact absurd h x.2.2
  · rintro rfl; exact Or.inr (Or.inl hv')

lemma E1 {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) {a b : {x : V // x ≠ u ∧ x ≠ w}}
    (ha : a ≠ v') (hb : b ≠ v') (h : (deleteIdentify G u v w).Adj a b) : G.Adj a.1 b.1 := by
  simp only [deleteIdentify, SimpleGraph.fromRel_adj] at h
  obtain ⟨_, (h | h) | (h | h)⟩ := h
  · exact h
  · exact absurd (Subtype.ext (h.1.trans hv'.symm)) ha
  · exact h.symm
  · exact absurd (Subtype.ext (h.1.trans hv'.symm)) hb

lemma E2 {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) {c : {x : V // x ≠ u ∧ x ≠ w}}
    (h : (deleteIdentify G u v w).Adj v' c) : G.Adj v c.1 ∨ G.Adj w c.1 := by
  simp only [deleteIdentify, SimpleGraph.fromRel_adj] at h
  obtain ⟨hne, (h | h) | (h | h)⟩ := h
  · exact Or.inl (hv' ▸ h)
  · exact Or.inr h.2
  · exact Or.inl (hv' ▸ h.symm)
  · exact absurd (Subtype.ext (h.1.trans hv'.symm)) hne.symm

lemma L1 {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) :
    ∀ {a b : {x : V // x ≠ u ∧ x ≠ w}} (p : (deleteIdentify G u v w).Walk a b),
      v' ∉ p.support → ∃ Q : G.Walk a.1 b.1, Q.support = p.support.map Subtype.val
  | _, _, .nil, _ => ⟨Walk.nil, by simp⟩
  | a, _, .cons (v := c) h p, hp => by
    simp only [Walk.support_cons, List.mem_cons, not_or] at hp
    obtain ⟨Q, hQ⟩ := L1 hv' p hp.2
    have hc : c ≠ v' := by
      rintro rfl; exact hp.2 (Walk.start_mem_support _)
    exact ⟨Walk.cons (E1 G u v w hv' (Ne.symm hp.1) hc h) Q, by simp [hQ]⟩

lemma map_notRS {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) (l : List {x : V // x ≠ u ∧ x ≠ w})
    (hl : v' ∉ l) (z : V) (hz : z ∈ l.map Subtype.val) : ¬ RS u v w z := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
  rw [val_RS u v w hv']; rintro rfl; exact hl hx

lemma L2 (hvw : v ≠ w) (huv : G.Adj u v) (huw : G.Adj u w)
    {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) {c b : {x : V // x ≠ u ∧ x ≠ w}}
    (h : (deleteIdentify G u v w).Adj v' c) (p : (deleteIdentify G u v w).Walk c b)
    (hp : p.IsPath) (hvp : v' ∉ p.support) (r : V) (hr : r = v ∨ r = w) :
    ∃ Q : G.Walk r b.1, Q.IsPath ∧ (∀ z ∈ Q.support, ¬ RS u v w z → z ∈ p.support.map Subtype.val) ∧
      (G.Adj r c.1 → ∀ z ∈ Q.support, RS u v w z → z = r) := by
  obtain ⟨Q', hQ'⟩ := L1 G u v w hv' p hvp
  have hnd : (p.support.map Subtype.val).Nodup :=
    hp.support_nodup.map Subtype.val_injective
  have hnot := map_notRS u v w hv' _ hvp
  have hrR : RS u v w r := by rcases hr with rfl | rfl <;> simp [RS]
  have huR : RS u v w u := Or.inl rfl
  have hvR : RS u v w v := Or.inr (Or.inl rfl)
  have hwR : RS u v w w := Or.inr (Or.inr rfl)
  have huv' := huv.ne
  have huw' := huw.ne
  by_cases hc : G.Adj r c.1
  · refine ⟨Walk.cons hc Q', ?_, ?_, ?_⟩
    · rw [Walk.isPath_def, Walk.support_cons, hQ', List.nodup_cons]
      exact ⟨fun hm => hnot _ hm hrR, hnd⟩
    · intro z hz hzR
      rw [Walk.support_cons, hQ', List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact absurd hrR hzR
      · exact hz
    · intro _ z hz hzR
      rw [Walk.support_cons, hQ', List.mem_cons] at hz
      rcases hz with rfl | hz
      · rfl
      · exact absurd hzR (hnot _ hz)
  · rcases hr with hr | hr <;> subst r
    · have hwc : G.Adj w c.1 := (E2 G u v w hv' h).resolve_left hc
      refine ⟨Walk.cons huv.symm (Walk.cons huw (Walk.cons hwc Q')), ?_, ?_, ?_⟩
      · rw [Walk.isPath_def]
        simp only [Walk.support_cons, hQ', List.nodup_cons, List.mem_cons, not_or]
        refine ⟨⟨huv'.symm, hvw, fun hm => hnot _ hm hvR⟩, ⟨huw', fun hm => hnot _ hm huR⟩,
          fun hm => hnot _ hm hwR, hnd⟩
      · intro z hz hzR
        simp only [Walk.support_cons, hQ', List.mem_cons] at hz
        rcases hz with rfl | rfl | rfl | hz
        · exact absurd hvR hzR
        · exact absurd huR hzR
        · exact absurd hwR hzR
        · exact hz
      · intro h'; exact absurd h' hc
    · have hvc : G.Adj v c.1 := (E2 G u v w hv' h).resolve_right hc
      refine ⟨Walk.cons huw.symm (Walk.cons huv (Walk.cons hvc Q')), ?_, ?_, ?_⟩
      · rw [Walk.isPath_def]
        simp only [Walk.support_cons, hQ', List.nodup_cons, List.mem_cons, not_or]
        refine ⟨⟨huw'.symm, hvw.symm, fun hm => hnot _ hm hwR⟩, ⟨huv', fun hm => hnot _ hm huR⟩,
          fun hm => hnot _ hm hvR, hnd⟩
      · intro z hz hzR
        simp only [Walk.support_cons, hQ', List.mem_cons] at hz
        rcases hz with rfl | rfl | rfl | hz
        · exact absurd hwR hzR
        · exact absurd huR hzR
        · exact absurd hvR hzR
        · exact hz
      · intro h'; exact absurd h' hc


lemma LPstart (hvw : v ≠ w) (huv : G.Adj u v) (huw : G.Adj u w)
    {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) {a b : {x : V // x ≠ u ∧ x ≠ w}}
    (p : (deleteIdentify G u v w).Walk a b) (ha : a = v')
    (hp : p.IsPath) (hb : b ≠ v') (r : V) (hr : r = v ∨ r = w) :
    ∃ Q : G.Walk r b.1, Q.IsPath ∧ (∀ z ∈ Q.support, ¬ RS u v w z → ∃ x ∈ p.support, z = x.1) ∧
      (G.Adj r (p.getVert 1).1 → ∀ z ∈ Q.support, RS u v w z → z = r) := by
  cases p with
  | nil => exact absurd ha hb
  | cons h p' =>
    subst ha
    rw [Walk.cons_isPath_iff] at hp
    obtain ⟨Q, hQ1, hQ2, hQ3⟩ := L2 G u v w hvw huv huw hv' h p' hp.1 hp.2 r hr
    refine ⟨Q, hQ1, fun z hz hzR => ?_, fun hadj => hQ3 (by simpa using hadj)⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hQ2 z hz hzR)
    exact ⟨x, by simp [hx], rfl⟩

variable [DecidableEq V]

def sig (v' : {x : V // x ≠ u ∧ x ≠ w}) (r : V) (x : {x : V // x ≠ u ∧ x ≠ w}) : V :=
  if x = v' then r else x.1

lemma LP (hvw : v ≠ w) (huv : G.Adj u v) (huw : G.Adj u w)
    {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) (r : V) (hr : r = v ∨ r = w)
    {a b : {x : V // x ≠ u ∧ x ≠ w}}
    (p : (deleteIdentify G u v w).Walk a b) (hp : p.IsPath) (hab : a ≠ b) :
    ∃ Q : G.Walk (sig u w v' r a) (sig u w v' r b), Q.IsPath ∧
      (∀ z ∈ Q.support, ¬ RS u v w z → ∃ x ∈ p.support, z = x.1) ∧
      (∀ z ∈ Q.support, RS u v w z → v' ∈ p.support) ∧
      (a = v' → G.Adj r (p.getVert 1).1 → ∀ z ∈ Q.support, RS u v w z → z = r) ∧
      (b = v' → G.Adj r (p.reverse.getVert 1).1 → ∀ z ∈ Q.support, RS u v w z → z = r) := by
  by_cases ha : a = v'
  · have hb : b ≠ v' := fun hb => hab (ha.trans hb.symm)
    obtain ⟨Q, hQ1, hQ2, hQ3⟩ := LPstart G u v w hvw huv huw hv' p ha hp hb r hr
    have e1 : r = sig u w v' r a := by simp [sig, ha]
    have e2 : b.1 = sig u w v' r b := by simp [sig, hb]
    refine ⟨Q.copy e1 e2, by simpa using hQ1, by simpa using hQ2, ?_, fun _ => by simpa using hQ3,
      fun hb' => absurd hb' hb⟩
    intro z _ _
    rw [← ha]; exact Walk.start_mem_support _
  by_cases hb : b = v'
  · obtain ⟨Q, hQ1, hQ2, hQ3⟩ := LPstart G u v w hvw huv huw hv' p.reverse hb hp.reverse ha r hr
    have e1 : a.1 = sig u w v' r a := by simp [sig, ha]
    have e2 : r = sig u w v' r b := by simp [sig, hb]
    refine ⟨Q.reverse.copy e1 e2, by simpa using hQ1.reverse, ?_, ?_, fun ha' => absurd ha' ha, ?_⟩
    · intro z hz hzR
      simp only [Walk.support_copy, Walk.support_reverse, List.mem_reverse] at hz
      obtain ⟨x, hx, rfl⟩ := hQ2 z hz hzR
      exact ⟨x, by simpa using hx, rfl⟩
    · intro z _ _
      rw [← hb]; exact Walk.end_mem_support _
    · intro _ hadj z hz hzR
      simp only [Walk.support_copy, Walk.support_reverse, List.mem_reverse] at hz
      exact hQ3 hadj z hz hzR
  have e1 : a.1 = sig u w v' r a := by simp [sig, ha]
  have e2 : b.1 = sig u w v' r b := by simp [sig, hb]
  by_cases hv : v' ∈ p.support
  · -- interior
    set p1 := p.takeUntil v' hv
    set p2 := p.dropUntil v' hv
    have hsp : p.support = p1.support ++ p2.support.tail := by
      rw [← Walk.support_append]; simp [p1, p2, Walk.take_spec]
    have hp1 : p1.IsPath := hp.takeUntil hv
    have hp2 : p2.IsPath := hp.dropUntil hv
    have hadjN : (deleteIdentify G u v w).Adj v' (p1.reverse.getVert 1) := by
      have hl : 0 < p1.reverse.length := by
        rcases Nat.eq_zero_or_pos p1.reverse.length with h0 | h0
        · exact absurd (Walk.eq_of_length_eq_zero h0).symm ha
        · exact h0
      simpa using p1.reverse.adj_getVert_succ hl
    obtain ⟨r0, hr0, hadj0⟩ : ∃ r0, (r0 = v ∨ r0 = w) ∧ G.Adj r0 (p1.reverse.getVert 1).1 := by
      rcases E2 G u v w hv' hadjN with h | h
      · exact ⟨v, Or.inl rfl, h⟩
      · exact ⟨w, Or.inr rfl, h⟩
    obtain ⟨Q1, hQ11, hQ12, hQ13⟩ :=
      LPstart G u v w hvw huv huw hv' p1.reverse rfl hp1.reverse ha r0 hr0
    obtain ⟨Q2, hQ21, hQ22, -⟩ := LPstart G u v w hvw huv huw hv' p2 rfl hp2 hb r0 hr0
    have hQ13' := hQ13 hadj0
    have hpnd : (p1.support ++ p2.support.tail).Nodup := hsp ▸ hp.support_nodup
    refine ⟨(Q1.reverse.append Q2).copy e1 e2, ?_, ?_, fun _ _ _ => hv, fun h => absurd h ha,
      fun h => absurd h hb⟩
    · rw [Walk.isPath_def, Walk.support_copy, Walk.support_append, List.nodup_append]
      refine ⟨by simpa using hQ11.support_nodup, hQ21.support_nodup.sublist (List.tail_sublist _),
        ?_⟩
      intro z hz1 z' hz2 hzz
      subst hzz
      simp only [Walk.support_reverse, List.mem_reverse] at hz1
      have hQ2nd := hQ21.support_nodup
      rw [Walk.support_eq_cons Q2, List.nodup_cons] at hQ2nd
      by_cases hzR : RS u v w z
      · have := hQ13' z hz1 hzR
        subst this
        exact hQ2nd.1 hz2
      · obtain ⟨x, hx, rfl⟩ := hQ12 _ hz1 hzR
        obtain ⟨y, hy, hxy⟩ := hQ22 _ (List.mem_of_mem_tail hz2) hzR
        have hxy' : x = y := Subtype.ext hxy
        subst hxy'
        have hxv : x ≠ v' := fun h => hzR ((val_RS u v w hv' x).2 h)
        rw [Walk.support_eq_cons p2, List.mem_cons] at hy
        rcases hy with h | h
        · exact hxv h
        · simp only [Walk.support_reverse, List.mem_reverse] at hx
          exact List.disjoint_of_nodup_append hpnd hx h
    · intro z hz hzR
      rw [Walk.support_copy, Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · simp only [Walk.support_reverse, List.mem_reverse] at hz
        obtain ⟨x, hx, rfl⟩ := hQ12 z hz hzR
        simp only [Walk.support_reverse, List.mem_reverse] at hx
        exact ⟨x, p.support_takeUntil_subset_support hv hx, rfl⟩
      · obtain ⟨x, hx, rfl⟩ := hQ22 z hz hzR
        exact ⟨x, p.support_dropUntil_subset_support hv hx, rfl⟩
  · obtain ⟨Q, hQ⟩ := L1 G u v w hv' p hv
    have hnot := map_notRS u v w hv' _ hv
    refine ⟨Q.copy e1 e2, ?_, ?_, fun z hz hzR => ?_, fun h => absurd h ha, fun h => absurd h hb⟩
    · rw [Walk.isPath_def, Walk.support_copy, hQ]
      exact hp.support_nodup.map Subtype.val_injective
    · intro z hz _
      rw [Walk.support_copy, hQ] at hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
      exact ⟨x, hx, rfl⟩
    · rw [Walk.support_copy, hQ] at hz
      exact absurd hzR (hnot z hz)

lemma sig_RS {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) (r : V) (hr : r = v ∨ r = w)
    (x : {x : V // x ≠ u ∧ x ≠ w}) : RS u v w (sig u w v' r x) ↔ x = v' := by
  unfold sig
  split_ifs with h
  · simp only [h, iff_true]; rcases hr with rfl | rfl <;> simp [RS]
  · rw [val_RS u v w hv']

lemma sig_ne {v' : {x : V // x ≠ u ∧ x ≠ w}} (r : V) {x : {x : V // x ≠ u ∧ x ≠ w}} (h : x ≠ v') :
    sig u w v' r x = x.1 := by simp [sig, h]

lemma sig_v' (v' : {x : V // x ≠ u ∧ x ≠ w}) (r : V) : sig u w v' r v' = r := by simp [sig]

lemma adj_first {W : Type*} {H : SimpleGraph W} {x y : W} (q : H.Walk x y) (h : x ≠ y) :
    H.Adj x (q.getVert 1) := by
  have hl : 0 < q.length := by
    rcases Nat.eq_zero_or_pos q.length with h0 | h0
    · exact absurd (Walk.eq_of_length_eq_zero h0) h
    · exact h0
  simpa using q.adj_getVert_succ hl

lemma comb : ∀ k m1 m2 m m' : Fin 4, m1 ≠ k → m2 ≠ k → m1 ≠ m2 → m ≠ k → m' ≠ k → m ≠ m' →
    m = m1 ∨ m = m2 ∨ m' = m1 ∨ m' = m2 := by decide

end DIAux

open SimpleGraph DIAux in
theorem deleteIdentify_isSeriesParallel_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsSeriesParallel G)
    (u v w : V) (hvw : v ≠ w) (huv : G.Adj u v) (huw : G.Adj u w)
    (_hdeg : G.degree u = 2) (_hnadj : ¬ G.Adj v w) :
    IsSeriesParallel (deleteIdentify G u v w) := by
  rintro ⟨b', p', hinj, hpath, hbr, hdisj⟩
  apply hG
  set v' : {x : V // x ≠ u ∧ x ≠ w} := ⟨v, huv.ne.symm, hvw⟩ with hv'def
  have hv' : v'.1 = v := rfl
  clear_value v'
  let Nb : Fin 4 → Fin 4 → {x : V // x ≠ u ∧ x ≠ w} := fun k m =>
    if k < m then (p' k m).getVert 1 else (p' m k).reverse.getVert 1
  have hNadj : ∀ k m, b' k = v' → m ≠ k → G.Adj v (Nb k m).1 ∨ G.Adj w (Nb k m).1 := by
    intro k m hk hm
    apply E2 G u v w hv'
    rw [← hk]
    have hne : b' k ≠ b' m := fun h => hm (hinj h).symm
    by_cases h : k < m
    · simp only [Nb, if_pos h]; exact adj_first _ hne
    · simp only [Nb, if_neg h]; exact adj_first _ hne
  obtain ⟨r, hr, hgood⟩ : ∃ r, (r = v ∨ r = w) ∧ ∀ k, b' k = v' → ∀ m m', m ≠ k → m' ≠ k →
      m ≠ m' → G.Adj r (Nb k m).1 ∨ G.Adj r (Nb k m').1 := by
    by_cases hex : ∃ k0, b' k0 = v'
    · obtain ⟨k0, hk0⟩ := hex
      have key : ∀ k, b' k = v' → k = k0 := fun k hk => hinj (hk.trans hk0.symm)
      by_cases hall : ∀ m m', m ≠ k0 → m' ≠ k0 → m ≠ m' →
          G.Adj v (Nb k0 m).1 ∨ G.Adj v (Nb k0 m').1
      · refine ⟨v, Or.inl rfl, fun k hk => ?_⟩
        obtain rfl := key k hk
        exact hall
      · push_neg at hall
        obtain ⟨m1, m2, h1, h2, h12, hn1, hn2⟩ := hall
        refine ⟨w, Or.inr rfl, fun k hk m m' hm hm' hmm' => ?_⟩
        obtain rfl := key k hk
        rcases comb k m1 m2 m m' h1 h2 h12 hm hm' hmm' with rfl | rfl | rfl | rfl
        · exact Or.inl ((hNadj _ _ hk h1).resolve_left hn1)
        · exact Or.inl ((hNadj _ _ hk h2).resolve_left hn2)
        · exact Or.inr ((hNadj _ _ hk h1).resolve_left hn1)
        · exact Or.inr ((hNadj _ _ hk h2).resolve_left hn2)
    · exact ⟨v, Or.inl rfl, fun k hk => absurd ⟨k, hk⟩ hex⟩
  let b : Fin 4 → V := fun k => sig u w v' r (b' k)
  have hsR := sig_RS u v w hv' r hr
  have hQ : ∀ i j, ∃ Q : G.Walk (b i) (b j), i < j →
      (Q.IsPath ∧
      (∀ z ∈ Q.support, ¬ RS u v w z → ∃ x ∈ (p' i j).support, z = x.1) ∧
      (∀ z ∈ Q.support, RS u v w z → v' ∈ (p' i j).support) ∧
      (b' i = v' → G.Adj r ((p' i j).getVert 1).1 → ∀ z ∈ Q.support, RS u v w z → z = r) ∧
      (b' j = v' → G.Adj r ((p' i j).reverse.getVert 1).1 →
        ∀ z ∈ Q.support, RS u v w z → z = r)) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · obtain ⟨Q, hQ⟩ := LP G u v w hvw huv huw hv' r hr (p' i j) (hpath i j h)
        (fun e => h.ne (hinj e))
      exact ⟨Q, fun _ => hQ⟩
    · subst h; exact ⟨Walk.nil, fun h => absurd h (lt_irrefl _)⟩
    · obtain ⟨Q, -⟩ := LP G u v w hvw huv huw hv' r hr (p' j i) (hpath j i h)
        (fun e => h.ne (hinj e))
      exact ⟨Q.reverse, fun h' => absurd h' (lt_asymm h)⟩
  choose Q hQ using hQ
  refine ⟨b, Q, ?_, fun i j h => (hQ i j h).1, ?_, ?_⟩
  · intro k l hkl
    apply hinj
    simp only [b] at hkl
    by_cases hk : b' k = v'
    · have : RS u v w (sig u w v' r (b' l)) := hkl ▸ (hsR _).2 hk
      rw [hsR] at this; rw [hk, this]
    · by_cases hl : b' l = v'
      · exact absurd ((hsR _).1 (hkl ▸ (hsR _).2 hl)) hk
      · rw [sig_ne u w r hk, sig_ne u w r hl] at hkl
        exact Subtype.ext hkl
  · intro i j hij k hk
    obtain ⟨_, A1, B1, -, -⟩ := hQ i j hij
    by_cases hR : RS u v w (b k)
    · have hk' : b' k = v' := (hsR _).1 hR
      exact hbr i j hij k (hk' ▸ B1 _ hk hR)
    · obtain ⟨x, hx, hxe⟩ := A1 _ hk hR
      have hk' : b' k ≠ v' := fun h => hR ((hsR _).2 h)
      have : b' k = x := Subtype.ext ((sig_ne u w r hk').symm.trans hxe)
      exact hbr i j hij k (this ▸ hx)
  · intro i j i' j' hij hij' hne z hz hz'
    obtain ⟨_, A1, B1, C1, D1⟩ := hQ i j hij
    obtain ⟨_, A2, B2, C2, D2⟩ := hQ i' j' hij'
    by_cases hzR : RS u v w z
    · have hv1 := B1 z hz hzR
      have hv2 := B2 z hz' hzR
      obtain ⟨k, hk⟩ := hdisj i j i' j' hij hij' hne v' hv1 hv2
      refine ⟨k, ?_⟩
      show z = sig u w v' r (b' k)
      rw [← hk, sig_v']
      have hk1 := hbr i j hij k (hk ▸ hv1)
      have hk2 := hbr i' j' hij' k (hk ▸ hv2)
      have hg := hgood k hk.symm
      rcases hk1 with rfl | rfl <;> rcases hk2 with rfl | rfl
      · have hjj : j ≠ j' := fun e => hne (by rw [e])
        rcases hg j j' hij.ne' hij'.ne' hjj with h | h
        · simp only [Nb, if_pos hij] at h; exact C1 hk.symm h z hz hzR
        · simp only [Nb, if_pos hij'] at h; exact C2 hk.symm h z hz' hzR
      · rcases hg j i' hij.ne' hij'.ne (by intro e; subst e; exact absurd (hij.trans hij') (lt_irrefl _)) with h | h
        · simp only [Nb, if_pos hij] at h; exact C1 hk.symm h z hz hzR
        · simp only [Nb, if_neg (lt_asymm hij')] at h; exact D2 hk.symm h z hz' hzR
      · rcases hg i j' hij.ne hij'.ne' (by intro e; subst e; exact absurd (hij.trans hij') (lt_irrefl _)) with h | h
        · simp only [Nb, if_neg (lt_asymm hij)] at h; exact D1 hk.symm h z hz hzR
        · simp only [Nb, if_pos hij'] at h; exact C2 hk.symm h z hz' hzR
      · have hii : i ≠ i' := fun e => hne (by rw [e])
        rcases hg i i' hij.ne hij'.ne hii with h | h
        · simp only [Nb, if_neg (lt_asymm hij)] at h; exact D1 hk.symm h z hz hzR
        · simp only [Nb, if_neg (lt_asymm hij')] at h; exact D2 hk.symm h z hz' hzR
    · obtain ⟨x, hx, rfl⟩ := A1 z hz hzR
      obtain ⟨y, hy, hxy⟩ := A2 _ hz' hzR
      obtain rfl : x = y := Subtype.ext hxy
      obtain ⟨k, rfl⟩ := hdisj i j i' j' hij hij' hne x hx hy
      refine ⟨k, ?_⟩
      have hk' : b' k ≠ v' := fun h => hzR ((val_RS u v w hv' _).2 h)
      exact (sig_ne u w r hk').symm

end ChvatalPolytopes.SeriesParallel

open ChvatalPolytopes.SeriesParallel


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsSeriesParallel G)
    (u v w : V) (hvw : v ≠ w) (huv : G.Adj u v) (huw : G.Adj u w)
    (hdeg : G.degree u = 2) (hnadj : ¬ G.Adj v w) :
    IsSeriesParallel (deleteIdentify G u v w) := by
  exact deleteIdentify_isSeriesParallel_core G hG u v w hvw huv huw hdeg hnadj
