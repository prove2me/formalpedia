-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:34:57.560288+00:00
-- url     : https://prove2.me/submissions/3cff4463-9fe2-4df6-bbef-170cea1b93ee

import Definitions.Def_DistancePreserver934_Exact_Essential

set_option autoImplicit false
open Classical DistancePreserver934.Exact

lemma shortest_isPath {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V}
    {w : H.Walk s t} (hw : IsShortest w) : w.IsPath := by
  apply w.isPath_of_length_eq_dist
  exact congrArg ENat.toNat hw

lemma path_incident_bound {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V}
    (w : H.Walk s t) (hw : w.IsPath) (x : V) :
    (w.edges.toFinset.filter (fun e => x ∈ e)).card ≤ if x=s then 1 else 2 := by
  classical
  induction w with
  | nil => simp
  | @cons u v t h w ih =>
    obtain ⟨hw',hu⟩ := (SimpleGraph.Walk.cons_isPath_iff h w).mp hw
    have htail := ih hw'
    simp only [SimpleGraph.Walk.edges_cons,List.toFinset_cons,Finset.filter_insert]
    by_cases hxu : x=u
    · subst x
      have hempty : w.edges.toFinset.filter (fun e => u ∈ e) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        obtain ⟨he,hue⟩ := Finset.mem_filter.mp he
        exact hu (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
          (Or.inr ⟨e,List.mem_toFinset.mp he,hue⟩))
      simp [hempty]
    · by_cases hxv : x=v
      · have hxedge : x ∈ s(u,v) := by simp [hxv]
        rw [if_pos hxedge,if_neg hxu]
        have ht : (w.edges.toFinset.filter (fun e => x ∈ e)).card ≤ 1 := by simpa [hxv] using htail
        exact (Finset.card_insert_le _ _).trans (by omega)
      · have hxedge : x ∉ s(u,v) := by simpa using And.intro hxu hxv
        rw [if_neg hxedge,if_neg hxu]
        simpa [hxv] using htail

lemma essential_subpath {V : Type} [Fintype V] {H : SimpleGraph V} {q e : Sym2 V}
    (he : IsEssential H q e) {s t : V} (hst : s(s,t)=q) (w : H.Walk s t) (hw : IsShortest w)
    (a b : V) (p₁ : H.Walk s a) (P : H.Walk a b) (p₂ : H.Walk b t)
    (hdecomp : w=p₁.append (P.append p₂)) (heP : e ∈ P.edges)
    (P' : H.Walk a b) (hP' : IsShortest P') : e ∈ P'.edges := by
  have hle : P'.length ≤ P.length := by
    have h : (P'.length : ℕ∞) ≤ P.length := by rw [hP']; exact SimpleGraph.edist_le P
    exact_mod_cast h
  let w' := p₁.append (P'.append p₂)
  have hrev : w.length ≤ w'.length := by
    have h : (w.length : ℕ∞) ≤ w'.length := by rw [hw]; exact SimpleGraph.edist_le w'
    exact_mod_cast h
  have hlen : P'.length=P.length := by
    simp only [hdecomp,w',SimpleGraph.Walk.length_append] at hrev
    omega
  have hw' : IsShortest w' := by
    change (w'.length : ℕ∞)=H.edist s t
    rw [← hw,hdecomp]
    simp [w',SimpleGraph.Walk.length_append,hlen]
  have htrail := (shortest_isPath hw).isTrail
  rw [hdecomp,SimpleGraph.Walk.isTrail_append] at htrail
  have hnot₁ : e ∉ p₁.edges := fun h => htrail.2.2 h (by simp [heP])
  have hnot₂ : e ∉ p₂.edges := fun h =>
    ((SimpleGraph.Walk.isTrail_append P p₂).mp htrail.2.1).2.2 heP h
  have hess := he s t hst w' hw'
  simpa [w',SimpleGraph.Walk.edges_append,hnot₁,hnot₂] using hess

lemma shortest_prefix {V : Type} [Fintype V] {H : SimpleGraph V} {s a t : V}
    (p : H.Walk s a) (q : H.Walk a t) (hw : IsShortest (p.append q)) : IsShortest p := by
  obtain ⟨p',hp'⟩ := p.reachable.exists_walk_length_eq_edist
  have hle : p'.length ≤ p.length := by
    have h : (p'.length : ℕ∞) ≤ p.length := by rw [hp']; exact SimpleGraph.edist_le p
    exact_mod_cast h
  have hrev : p.length ≤ p'.length := by
    have h : ((p.append q).length : ℕ∞) ≤ (p'.append q).length := by
      rw [hw]; exact SimpleGraph.edist_le _
    have h' : (p.append q).length ≤ (p'.append q).length := by exact_mod_cast h
    simp only [SimpleGraph.Walk.length_append] at h'
    omega
  have heq := le_antisymm hle hrev
  change (p.length : ℕ∞) = H.edist s a
  rw [← heq]
  exact hp'

lemma shortest_support_dist {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V}
    (w : H.Walk s t) (hw : IsShortest w) (x : V) (hx : x ∈ w.support) :
    H.dist s x = w.support.idxOf x := by
  classical
  have hp := shortest_prefix (w.takeUntil x hx) (w.dropUntil x hx)
    (by rw [w.take_spec hx]; exact hw)
  have hnat := congrArg ENat.toNat hp
  simpa only [SimpleGraph.dist,ENat.toNat_natCast,SimpleGraph.Walk.length_takeUntil] using hnat.symm

lemma shortest_neighbors {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V}
    (w : H.Walk s t) (hw : IsShortest w) (u : V) :
    (w.support.toFinset.filter (fun v => H.Adj u v)).card ≤ 3 := by
  classical
  let S := w.support.toFinset.filter (fun v => H.Adj u v)
  have hinj : Set.InjOn (fun v => H.dist s v) (S : Set V) := by
    intro x hx y hy heq
    have hx' : x ∈ w.support := List.mem_toFinset.mp (Finset.mem_filter.mp hx).1
    have hy' : y ∈ w.support := List.mem_toFinset.mp (Finset.mem_filter.mp hy).1
    change H.dist s x = H.dist s y at heq
    rw [shortest_support_dist w hw x hx',shortest_support_dist w hw y hy'] at heq
    exact (List.idxOf_inj hx').mp heq
  have hsubset : S.image (fun v => H.dist s v) ⊆ Finset.Icc (H.dist s u-1) (H.dist s u+1) := by
    intro k hk
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
    have hadj := (Finset.mem_filter.mp hv).2
    have hd := hadj.diff_dist_adj (u := s)
    rw [Finset.mem_Icc]
    rcases hd with h | h | h <;> omega
  have hc := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injOn hinj] at hc
  have hinterval : (Finset.Icc (H.dist s u-1) (H.dist s u+1)).card ≤ 3 := by
    rw [Nat.card_Icc]
    omega
  exact hc.trans hinterval

theorem solution {V : Type} [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V))
    (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R) (q : Sym2 V) (hq : q ∈ R) :
    (∀ x : V, ((edgesF H).filter (fun e => x ∈ e ∧ IsEssential H q e)).card ≤ 2) ∧
    (∀ s t : V, s(s, t) = q → ∀ π : H.Walk s t, IsShortest π → ∀ u : V,
      (π.support.toFinset.filter (fun v => H.Adj u v)).card ≤ 3) ∧
    (∀ u : V, ((Finset.univ : Finset (V × Sym2 V)).filter (fun xe =>
        xe.2 ∈ H.edgeSet ∧ IsEssential H q xe.2 ∧ xe.1 ∈ xe.2 ∧ H.Adj u xe.1)).card ≤ 6) ∧
    (∀ e : Sym2 V, IsEssential H q e → ∀ s t : V, s(s, t) = q → ∀ π : H.Walk s t,
      IsShortest π → ∀ (a b : V) (p₁ : H.Walk s a) (P : H.Walk a b) (p₂ : H.Walk b t),
        π = p₁.append (P.append p₂) → e ∈ P.edges →
        ∀ P' : H.Walk a b, IsShortest P' → e ∈ P'.edges) := by
  classical
  have hpath : ∃ s t : V, s(s,t)=q ∧ ∃ w : H.Walk s t, IsShortest w := by
    induction q using Sym2.ind with
    | _ s t =>
      have hreach : H.Reachable s t := SimpleGraph.edist_ne_top_iff_reachable.mp (by
        rw [hH.1.2 s t hq]
        exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hR s t hq).2)
      obtain ⟨w,hw⟩ := hreach.exists_walk_length_eq_edist
      exact ⟨s,t,rfl,w,hw⟩
  obtain ⟨s,t,hst,w,hw⟩ := hpath
  have hinc : ∀ x : V, ((edgesF H).filter (fun e => x ∈ e ∧ IsEssential H q e)).card ≤ 2 := by
    intro x
    have hs : (edgesF H).filter (fun e => x ∈ e ∧ IsEssential H q e) ⊆
        w.edges.toFinset.filter (fun e => x ∈ e) := by
      intro e he
      obtain ⟨he,hxe,hess⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hess s t hst w hw),hxe⟩
    have hb := path_incident_bound w (shortest_isPath hw) x
    exact (Finset.card_le_card hs).trans (hb.trans (by split_ifs <;> omega))
  refine ⟨hinc,?_,?_,?_⟩
  · intro s' t' hst' π hπ u
    exact shortest_neighbors π hπ u
  · intro u
    let S := w.support.toFinset.filter (fun v => H.Adj u v)
    let T := (Finset.univ : Finset (V × Sym2 V)).filter (fun xe =>
      xe.2 ∈ H.edgeSet ∧ IsEssential H q xe.2 ∧ xe.1 ∈ xe.2 ∧ H.Adj u xe.1)
    have hfst : ∀ xe ∈ T, xe.1 ∈ S := by
      intro xe hxe
      obtain ⟨_,he,hess,hxe,hadj⟩ := Finset.mem_filter.mp hxe
      apply Finset.mem_filter.mpr
      refine ⟨List.mem_toFinset.mpr ?_,hadj⟩
      exact SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨xe.2,hess s t hst w hw,hxe⟩)
    have hsum : ∑ x ∈ S, (T.filter (fun xe => xe.1=x)).card = T.card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter T S Prod.fst]
      congr 1
      exact Finset.filter_eq_self.mpr hfst
    have hfiber : ∀ x ∈ S, (T.filter (fun xe => xe.1=x)).card ≤ 2 := by
      intro x hx
      let F := T.filter (fun xe => xe.1=x)
      have hinj : Set.InjOn Prod.snd (F : Set (V × Sym2 V)) := by
        intro a ha b hb heq
        apply Prod.ext
        · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
        · exact heq
      have hsub : F.image Prod.snd ⊆ (edgesF H).filter (fun e => x ∈ e ∧ IsEssential H q e) := by
        intro e he
        obtain ⟨xe,hxe,rfl⟩ := Finset.mem_image.mp he
        obtain ⟨hxe,hfirst⟩ := Finset.mem_filter.mp hxe
        obtain ⟨_,he,hess,hinc',hadj⟩ := Finset.mem_filter.mp hxe
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,?_,hess⟩
        simpa only [hfirst] using hinc'
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injOn hinj] at hc
      exact hc.trans (hinc x)
    change T.card ≤ 6
    calc
      T.card = ∑ x ∈ S, (T.filter (fun xe => xe.1=x)).card := hsum.symm
      _ ≤ ∑ _x ∈ S, 2 := Finset.sum_le_sum hfiber
      _ = S.card*2 := by simp
      _ ≤ 6 := by have hc := shortest_neighbors w hw u; change S.card ≤ 3 at hc; omega
  · intro e he s' t' hst' π hπ a b p₁ P p₂ hdecomp heP P' hP'
    exact essential_subpath he hst' π hπ a b p₁ P p₂ hdecomp heP P' hP'
