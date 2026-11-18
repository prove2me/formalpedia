-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:16:05.368171+00:00
-- url     : https://prove2.me/submissions/34c8a193-8811-4eba-b795-79b4e6ea604c

import Theorems.Thm_DistancePreserver934_Exact_lemma_12
import Definitions.Def_DistancePreserver934_Exact_LoyalCore

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
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


lemma endpoint_essential_unique {V : Type} [Fintype V] (H : SimpleGraph V) (a z : V)
    (hr : H.Reachable a z) (e f : Sym2 V) (hae : a ∈ e) (haf : a ∈ f)
    (he : IsEssential H s(a,z) e) (hf : IsEssential H s(a,z) f) : e=f := by
  classical
  obtain ⟨p,hp⟩ := hr.exists_walk_length_eq_edist
  have hc := path_incident_bound p (shortest_isPath hp) a
  simp only [ite_true] at hc
  have hmE : e ∈ p.edges.toFinset.filter (fun e => a ∈ e) :=
    Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (he a z rfl p hp),hae⟩
  have hmF : f ∈ p.edges.toFinset.filter (fun e => a ∈ e) :=
    Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hf a z rfl p hp),haf⟩
  exact (Finset.card_le_one.mp hc) e hmE f hmF

lemma private_length_le_walk {V : Type} [Fintype V] (H : SimpleGraph V)
    (R : Finset (Sym2 V)) (q : Sym2 V) (s t : V) (hst : s(s,t)=q)
    (w : H.Walk s t) (hw : IsShortest w) : privLen H R q ≤ w.length := by
  classical
  have hsub : privOf H R q ⊆ w.edges.toFinset := by
    intro e he
    have hset := (Finset.mem_filter.mp he).2
    have hq : q ∈ essSet H R e := by rw [hset]; simp
    have hess := (Finset.mem_filter.mp hq).2
    exact List.mem_toFinset.mpr (hess s t hst w hw)
  exact (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans_eq (w.length_edges))

lemma walk_hits_distance {V : Type} [Fintype V] {H : SimpleGraph V} {a b : V}
    (p : H.Walk a b) (u : V) (j : ℕ) (ha : H.dist u a<j) (hb : j ≤ H.dist u b) :
    ∃ z ∈ p.support, H.dist u z=j := by
  induction p with
  | nil => omega
  | @cons a v b hadj p ih =>
    by_cases hv : j ≤ H.dist u v
    · have hd := hadj.diff_dist_adj (u := u)
      have heq : H.dist u v=j := by rcases hd with h | h | h <;> omega
      exact ⟨v,by simp,heq⟩
    · obtain ⟨z,hz,hj⟩ := ih (lt_of_not_ge hv) hb
      exact ⟨z,by simp [hz],hj⟩

lemma first_edge_in_prefix {V : Type} [Fintype V] {H : SimpleGraph V} {a b : V}
    (p : H.Walk a b) (e : Sym2 V) (hp : 0<p.length)
    (he : e=s(p.getVert 0,p.getVert 1)) (z : V) (hz : z ∈ p.support) (hne : a ≠ z) :
    e ∈ (p.takeUntil z hz).edges := by
  classical
  cases p with
  | nil => simp at hp
  | @cons a v b hadj p =>
    have hz' : z ∈ p.support := by simpa only [SimpleGraph.Walk.support_cons,List.mem_cons,or_iff_right (Ne.symm hne)] using hz
    simp only [SimpleGraph.Walk.getVert_zero,SimpleGraph.Walk.getVert_cons_succ] at he
    rw [he,SimpleGraph.Walk.takeUntil_cons hz' hne hadj]
    simp

lemma inherited_essential {V : Type} [Fintype V] (G H : SimpleGraph V)
    (R : Finset (Sym2 V)) (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R)
    (q e : Sym2 V) (hq : q ∈ R) (he : IsEssential H q e) (s t : V) (hst : s(s,t)=q)
    (w : H.Walk s t) (hw : IsShortest w) (a b : V)
    (p₁ : H.Walk s a) (P : H.Walk a b) (p₂ : H.Walk b t)
    (hdecomp : w=p₁.append (P.append p₂)) (heP : e ∈ P.edges) :
    IsEssential H s(a,b) e := by
  have hpart := (DistancePreserver934.Exact.lemma_12 G H R hR hH q hq).2.2.2
    e he s t hst w hw a b p₁ P p₂ hdecomp heP
  intro x y hxy p hp
  rcases Sym2.eq_iff.mp hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hpart p hp
  · have hprev : IsShortest p.reverse := by simpa [IsShortest,SimpleGraph.edist_comm] using hp
    simpa using hpart p.reverse hprev

lemma exit_layer_essential {V : Type} [Fintype V] (G H : SimpleGraph V)
    (R : Finset (Sym2 V)) (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R)
    (q e : Sym2 V) (hq : q ∈ R) (he : IsEssential H q e) (s t u : V)
    (hst : s(s,t)=q) (w : H.Walk s t) (hw : IsShortest w) (j : ℕ) (hj : 1 ≤ j)
    (hends : ∀ a ∈ e, a ∈ ball H u ((j-1:ℕ):ℝ))
    (ht : t ∉ ball H u ((j-1:ℕ):ℝ)) :
    ∃ z : V, H.edist u z=(j:ℕ∞) ∧ ∃ a ∈ e,
      H.Reachable a z ∧ IsEssential H s(a,z) e := by
  classical
  have hew : e ∈ w.edges := he s t hst w hw
  obtain ⟨i,hi,hei⟩ := List.mem_iff_getElem.mp hew
  have hiw : i<w.length := by simpa only [SimpleGraph.Walk.length_edges] using hi
  have hed : s(w.getVert i,w.getVert (i+1))=e := (w.getElem_edges hi).symm.trans hei
  let a := w.getVert i
  have hae : a ∈ e := by rw [← hed]; simp [a]
  obtain ⟨k,hk,hkbound⟩ := (Finset.mem_filter.mp (hends a hae)).2
  have hka : H.dist u a=k := by
    dsimp [SimpleGraph.dist]
    rw [hk]
    simp
  have hk' : k ≤ j-1 := by exact_mod_cast hkbound
  have ha : H.dist u a<j := by omega
  have hua : H.Reachable u a := SimpleGraph.edist_ne_top_iff_reachable.mp (by rw [hk]; simp)
  let p := w.drop i
  have hut : H.Reachable u t := hua.trans p.reachable
  have ht' : j ≤ H.dist u t := by
    by_contra! hsmall
    apply ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,H.dist u t,hut.coe_dist_eq_edist.symm,?_⟩
    exact_mod_cast (show H.dist u t ≤ j-1 by omega)
  obtain ⟨z,hzp,hzj⟩ := walk_hits_distance p u j ha ht'
  have hne : a ≠ z := by intro h; rw [h,hzj] at ha; omega
  have hplen : 0<p.length := by simp only [p,SimpleGraph.Walk.drop_length]; omega
  have hfirst : e=s(p.getVert 0,p.getVert 1) := by
    dsimp [p]
    rw [SimpleGraph.Walk.drop_getVert,SimpleGraph.Walk.drop_getVert]
    simpa only [add_zero] using hed.symm
  have heP := first_edge_in_prefix p e hplen hfirst z hzp hne
  have hdecomp : w=(w.take i).append ((p.takeUntil z hzp).append (p.dropUntil z hzp)) := by
    rw [p.take_spec hzp]
    exact (w.append_take_drop_eq i).symm
  have hessaz := inherited_essential G H R hR hH q e hq he s t hst w hw a z
    (w.take i) (p.takeUntil z hzp) (p.dropUntil z hzp) hdecomp heP
  have huz : H.Reachable u z := hua.trans (p.takeUntil z hzp).reachable
  refine ⟨z,?_,a,hae,(p.takeUntil z hzp).reachable,hessaz⟩
  rw [← huz.coe_dist_eq_edist,hzj]

lemma ball_pairwise {V : Type} [Fintype V] (H : SimpleGraph V) (c x y : V) (a : ℝ)
    (hx : x ∈ ball H c a) (hy : y ∈ ball H c a) :
    ∃ k : ℕ, H.edist x y = (k : ℕ∞) ∧ (k : ℝ) ≤ 2*a := by
  obtain ⟨i,hi,hia⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨j,hj,hja⟩ := (Finset.mem_filter.mp hy).2
  have hxy : H.edist x y ≤ ((i+j : ℕ) : ℕ∞) := by
    calc
      _ ≤ H.edist x c+H.edist c y := SimpleGraph.edist_triangle
      _ = _ := by rw [SimpleGraph.edist_comm (u := x),hi,hj]; simp
  obtain ⟨k,hk,hkle⟩ := ENat.le_natCast_iff.mp hxy
  refine ⟨k,hk,?_⟩
  have hk' : (k : ℝ) ≤ (i : ℝ)+j := by exact_mod_cast hkle
  linarith


lemma layer_private_edge {V : Type} [Fintype V] (G H : SimpleGraph V)
    (R : Finset (Sym2 V)) (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R)
    (l : ℝ) (hlam : ∀ q ∈ R, l ≤ (privLen H R q:ℝ))
    (u : V) (j : ℕ) (hj : 1 ≤ j) (hjl : 2*((j-1:ℕ):ℝ)<l)
    (e : Sym2 V) (he : e ∈ privEdges H R)
    (hends : ∀ a ∈ e, a ∈ ball H u ((j-1:ℕ):ℝ)) :
    ∃ z : V, H.edist u z=(j:ℕ∞) ∧ ∃ a ∈ e,
      H.Reachable a z ∧ IsEssential H s(a,z) e := by
  classical
  have hcard := (Finset.mem_filter.mp he).2
  obtain ⟨q,hsetq⟩ := Finset.card_eq_one.mp hcard
  have hqess : q ∈ essSet H R e := by rw [hsetq]; simp
  obtain ⟨hq,hess⟩ := Finset.mem_filter.mp hqess
  let s := q.out.1
  let t := q.out.2
  have hrep : s(s,t)=q := Quot.out_eq q
  have hreach : H.Reachable s t := SimpleGraph.edist_ne_top_iff_reachable.mp (by
    rw [hH.1.2 s t (by rw [hrep]; exact hq)]
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hR s t (by rw [hrep]; exact hq)).2)
  obtain ⟨w,hw⟩ := hreach.exists_walk_length_eq_edist
  have hlen : l ≤ (w.length:ℝ) :=
    (hlam q hq).trans (by exact_mod_cast private_length_le_walk H R q s t hrep w hw)
  by_cases ht : t ∈ ball H u ((j-1:ℕ):ℝ)
  · have hs : s ∉ ball H u ((j-1:ℕ):ℝ) := by
      intro hs
      obtain ⟨k,hk,hkb⟩ := ball_pairwise H u s t ((j-1:ℕ):ℝ) hs ht
      have hlenk : w.length=k := by exact_mod_cast hw.trans hk
      rw [← hlenk] at hkb
      linarith
    have hwrev : IsShortest w.reverse := by simpa [IsShortest,SimpleGraph.edist_comm] using hw
    have hrep' : s(t,s)=q := Sym2.eq_swap.trans hrep
    exact exit_layer_essential G H R hR hH q e hq hess t s u hrep' w.reverse hwrev j hj hends hs
  · exact exit_layer_essential G H R hR hH q e hq hess s t u hrep w hw j hj hends ht

lemma rooted_edge_count {V : Type} [Fintype V] (H : SimpleGraph V)
    (E : Finset (Sym2 V)) (W : Finset V) (z : V)
    (hends : ∀ e ∈ E, ∀ a ∈ e, a ∈ W)
    (hroot : ∀ e ∈ E, ∃ a ∈ e, H.Reachable a z ∧ IsEssential H s(a,z) e) :
    E.card ≤ W.card := by
  classical
  let owner : Sym2 V → V := fun e => if he : e ∈ E then (hroot e he).choose else e.out.1
  have howner (e : Sym2 V) (he : e ∈ E) : owner e ∈ e ∧
      H.Reachable (owner e) z ∧ IsEssential H s(owner e,z) e := by
    simpa only [owner,dif_pos he] using (hroot e he).choose_spec
  have hinj : Set.InjOn owner (E:Set (Sym2 V)) := by
    intro e he f hf heq
    have he' := howner e he
    have hf' := howner f hf
    exact endpoint_essential_unique H (owner e) z he'.2.1 e f he'.1
      (by simpa only [heq] using hf'.1) he'.2.2 (by simpa only [heq] using hf'.2.2)
  have hsub : E.image owner ⊆ W := by
    intro a ha
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
    exact hends e he (owner e) (howner e he).1
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj] at hc


noncomputable def otherEnd {V : Type*} (x : V) (e : Sym2 V) : V :=
  if h : x ∈ e then (Sym2.mem_iff_exists.mp h).choose else x

lemma otherEnd_spec {V : Type*} (x : V) (e : Sym2 V) (hx : x ∈ e) : e=s(x,otherEnd x e) := by
  classical
  dsimp [otherEnd]
  rw [dif_pos hx]
  exact (Sym2.mem_iff_exists.mp hx).choose_spec

lemma otherEnd_mem {V : Type*} (x : V) (e : Sym2 V) (hx : x ∈ e) : otherEnd x e ∈ e := by
  apply Sym2.mem_iff_exists.mpr
  exact ⟨x,(otherEnd_spec x e hx).trans Sym2.eq_swap⟩

lemma incidence_sum {V : Type*} [Fintype V] (E : Finset (Sym2 V)) (W : Finset V)
    (hends : ∀ e ∈ E, ∀ x ∈ e, x ∈ W) (hdiag : ∀ e ∈ E, ¬e.IsDiag) :
    ∑ x ∈ W, (E.filter (fun e => x ∈ e)).card = 2*E.card := by
  classical
  have hsum : (∑ x ∈ W, (E.filter (fun e => x ∈ e)).card) =
      ∑ e ∈ E, (W.filter (fun x => x ∈ e)).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hsum]
  have heq : ∀ e ∈ E, (W.filter (fun x => x ∈ e)).card=2 := by
    intro e he
    have hfin : W.filter (fun x => x ∈ e)=e.toFinset := by
      ext x
      simp only [Finset.mem_filter,Sym2.mem_toFinset]
      exact ⟨And.right,fun hx => ⟨hends e he x hx,hx⟩⟩
    rw [hfin,Sym2.card_toFinset_of_not_isDiag e (hdiag e he)]
  rw [Finset.sum_congr rfl heq]
  simp [mul_comm]

lemma incidence_boundary_bound {V : Type*} [Fintype V]
    (E : Finset (Sym2 V)) (W B : Finset V)
    (hdiag : ∀ e ∈ E, ¬e.IsDiag)
    (hboundary : ∀ x ∈ W, ∀ e ∈ E, x ∈ e → ¬(∀ v ∈ e, v ∈ W) → otherEnd x e ∈ B) :
    ∑ x ∈ W, (E.filter (fun e => x ∈ e)).card ≤
      2*(E.filter (fun e => ∀ v ∈ e, v ∈ W)).card + W.card*B.card := by
  classical
  let I := E.filter (fun e => ∀ v ∈ e, v ∈ W)
  have hsumI : ∑ x ∈ W, (I.filter (fun e => x ∈ e)).card = 2*I.card :=
    incidence_sum I W (fun e he => (Finset.mem_filter.mp he).2)
      (fun e he => hdiag e (Finset.mem_filter.mp he).1)
  have hpoint : ∀ x ∈ W, (E.filter (fun e => x ∈ e)).card ≤
      (I.filter (fun e => x ∈ e)).card+B.card := by
    intro x hx
    let S := E.filter (fun e => x ∈ e)
    let T := I.filter (fun e => x ∈ e)
    have hTS : T ⊆ S := by
      intro e he
      obtain ⟨he,hxe⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,hxe⟩
    have hsub : (S \ T).image (otherEnd x) ⊆ B := by
      intro y hy
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨heS,heT⟩ := Finset.mem_sdiff.mp he
      obtain ⟨heE,hxe⟩ := Finset.mem_filter.mp heS
      apply hboundary x hx e heE hxe
      intro heW
      exact heT (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heE,heW⟩,hxe⟩)
    have hinj : Set.InjOn (otherEnd x) ((S \ T : Finset (Sym2 V)) : Set (Sym2 V)) := by
      intro e he f hf heq
      have hxe := (Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1).2
      have hxf := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hf).1).2
      rw [otherEnd_spec x e hxe,otherEnd_spec x f hxf,heq]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj] at hc
    have hcard := Finset.card_sdiff_add_card_eq_card hTS
    change S.card ≤ T.card+B.card
    omega
  calc
    _ ≤ ∑ x ∈ W, ((I.filter (fun e => x ∈ e)).card+B.card) := Finset.sum_le_sum hpoint
    _ = 2*I.card+W.card*B.card := by rw [Finset.sum_add_distrib,hsumI]; simp

lemma ball_layer_bound {V : Type} [Fintype V] (G H : SimpleGraph V)
    (R : Finset (Sym2 V)) (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R)
    (l δ : ℝ) (Vs : Finset V) (hlam : ∀ q ∈ R, l ≤ (privLen H R q:ℝ))
    (hdeg : ∀ x ∈ Vs, δ ≤ (coreDeg H R Vs x:ℝ))
    (u : V) (hu : u ∈ Vs) (j : ℕ) (hj : 1 ≤ j) (hjl : 2*((j-1:ℕ):ℝ)<l) :
    δ/3 ≤ ((Finset.univ.filter (fun z => H.edist u z=(j:ℕ∞))).card:ℝ) := by
  classical
  let W := Vs.filter (fun x => x ∈ ball H u ((j-1:ℕ):ℝ))
  let L := Finset.univ.filter (fun z => H.edist u z=(j:ℕ∞))
  let E := coreEdges H R Vs
  let I := E.filter (fun e => ∀ v ∈ e, v ∈ W)
  have hW : W.Nonempty := by
    refine ⟨u,Finset.mem_filter.mpr ⟨hu,?_⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,0,by simp,by simp only [Nat.cast_zero]; exact Nat.cast_nonneg _⟩
  have hEedge : ∀ e ∈ E, e ∈ H.edgeSet := by
    intro e he
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1).2
  have hdiag : ∀ e ∈ E, ¬e.IsDiag := fun e he => H.not_isDiag_of_mem_edgeSet (hEedge e he)
  have hboundary : ∀ x ∈ W, ∀ e ∈ E, x ∈ e → ¬(∀ v ∈ e, v ∈ W) → otherEnd x e ∈ L := by
    intro x hx e he hxe hnot
    let y := otherEnd x e
    have hyE : y ∈ e := otherEnd_mem x e hxe
    have hyVs : y ∈ Vs := (Finset.mem_filter.mp he).2 y hyE
    have hrep : e=s(x,y) := otherEnd_spec x e hxe
    have hxy : H.Adj x y := by have h := hEedge e he; rwa [hrep] at h
    have hnotW : y ∉ W := by
      intro hyW
      apply hnot
      intro v hv
      rw [hrep] at hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact hx
      · exact hyW
    obtain ⟨i,hi,hib⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).2).2
    have hib' : i ≤ j-1 := by exact_mod_cast hib
    have hyDist : H.edist u y ≤ (j:ℕ∞) := by
      calc
        _ ≤ H.edist u x+H.edist x y := SimpleGraph.edist_triangle
        _ = (i:ℕ∞)+1 := by rw [hi,SimpleGraph.edist_eq_one_iff_adj.mpr hxy]
        _ ≤ j := by exact_mod_cast (show i+1 ≤ j by omega)
    obtain ⟨k,hk,hkj⟩ := ENat.le_natCast_iff.mp hyDist
    have hkEq : k=j := by
      by_contra hne
      have hkle : k ≤ j-1 := by omega
      apply hnotW
      apply Finset.mem_filter.mpr
      refine ⟨hyVs,Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,hk,?_⟩⟩
      exact_mod_cast hkle
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rwa [hkEq] at hk⟩
  have hinc := incidence_boundary_bound E W L hdiag hboundary
  have hδsum : δ*(W.card:ℝ) ≤ ∑ x ∈ W, (coreDeg H R Vs x:ℝ) := by
    calc
      _ = ∑ _x ∈ W, δ := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun x hx => hdeg x (Finset.mem_filter.mp hx).1)
  have hinc' : (∑ x ∈ W, (coreDeg H R Vs x:ℝ)) ≤ 2*(I.card:ℝ)+(W.card:ℝ)*(L.card:ℝ) := by
    exact_mod_cast hinc
  let Ew : V → Finset (Sym2 V) := fun z => I.filter
    (fun e => ∃ a ∈ e, H.Reachable a z ∧ IsEssential H s(a,z) e)
  have hcover : I ⊆ L.biUnion Ew := by
    intro e he
    obtain ⟨heE,heW⟩ := Finset.mem_filter.mp he
    have hePriv : e ∈ privEdges H R := (Finset.mem_filter.mp heE).1
    have heBall : ∀ a ∈ e, a ∈ ball H u ((j-1:ℕ):ℝ) := fun a hae => (Finset.mem_filter.mp (heW a hae)).2
    obtain ⟨z,hz,a,hae,hra,hess⟩ := layer_private_edge G H R hR hH l hlam u j hj hjl e hePriv heBall
    exact Finset.mem_biUnion.mpr ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,
      Finset.mem_filter.mpr ⟨he,a,hae,hra,hess⟩⟩
  have hroot : ∀ z ∈ L, (Ew z).card ≤ W.card := by
    intro z hz
    apply rooted_edge_count H (Ew z) W z
    · intro e he
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    · intro e he
      exact (Finset.mem_filter.mp he).2
  have hIcard : I.card ≤ L.card*W.card := by
    calc
      I.card ≤ (L.biUnion Ew).card := Finset.card_le_card hcover
      _ ≤ ∑ z ∈ L, (Ew z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ L, W.card := Finset.sum_le_sum hroot
      _ = _ := by simp
  have hIcard' : (I.card:ℝ) ≤ (L.card:ℝ)*(W.card:ℝ) := by exact_mod_cast hIcard
  have hprod : δ*(W.card:ℝ) ≤ (3*(L.card:ℝ))*(W.card:ℝ) := by nlinarith
  have hWpos : 0 < (W.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hW
  have hδL := (mul_le_mul_iff_left₀ hWpos).mp hprod
  change δ/3 ≤ (L.card:ℝ)
  linarith

lemma growth_layer_parameters (a l : ℝ) (ha : 1 ≤ a) (hl : 1 ≤ l) :
    let J : ℕ := min ⌊a⌋₊ ⌈l/2⌉₊
    min a l/2 ≤ (J:ℝ) ∧ ∀ j ∈ Finset.Icc 1 J,
      (j:ℝ) ≤ a ∧ 2*((j-1:ℕ):ℝ)<l := by
  dsimp only
  have hafloor : a/2 ≤ (⌊a⌋₊:ℝ) := by
    have hone : 1 ≤ ⌊a⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using ha)
    have hone' : (1:ℝ) ≤ (⌊a⌋₊:ℝ) := by exact_mod_cast hone
    have hlt := Nat.lt_floor_add_one a
    linarith
  have hlceil : l/2 ≤ (⌈l/2⌉₊:ℝ) := Nat.le_ceil _
  constructor
  · rw [Nat.cast_min]
    apply le_min
    · have := min_le_left a l; linarith
    · have := min_le_right a l; linarith
  · intro j hj
    obtain ⟨hj1,hjJ⟩ := Finset.mem_Icc.mp hj
    have hjA : j ≤ ⌊a⌋₊ := hjJ.trans (min_le_left _ _)
    have hjL : j ≤ ⌈l/2⌉₊ := hjJ.trans (min_le_right _ _)
    constructor
    · exact (show (j:ℝ) ≤ (⌊a⌋₊:ℝ) by exact_mod_cast hjA).trans (Nat.floor_le (by linarith))
    · have hceil := Nat.ceil_lt_add_one (show 0 ≤ l/2 by linarith)
      have hjL' : (j:ℝ) ≤ (⌈l/2⌉₊:ℝ) := by exact_mod_cast hjL
      rw [Nat.cast_sub hj1,Nat.cast_one]
      linarith

lemma ball_growth_general {V : Type} [Fintype V] (G H : SimpleGraph V)
    (R : Finset (Sym2 V)) (l δ : ℝ) (Vs : Finset V)
    (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R)
    (hlam : ∀ q ∈ R, l ≤ (privLen H R q:ℝ)) (hl : 1 ≤ l)
    (hδ : 0 < δ) (hdeg : ∀ x ∈ Vs, δ ≤ (coreDeg H R Vs x:ℝ))
    (u : V) (hu : u ∈ Vs) (a : ℝ) (ha : 1 ≤ a) :
    δ/6*min a l ≤ ((ball H u a).card:ℝ) := by
  classical
  let J : ℕ := min ⌊a⌋₊ ⌈l/2⌉₊
  let I := Finset.Icc 1 J
  let L : ℕ → Finset V := fun j => Finset.univ.filter (fun v => H.edist u v=(j:ℕ∞))
  have hparams := growth_layer_parameters a l ha hl
  have hJ : min a l/2 ≤ (J:ℝ) := hparams.1
  have hbound : ∀ j ∈ I, δ/3 ≤ ((L j).card:ℝ) := by
    intro j hj
    exact ball_layer_bound G H R hR hH l δ Vs hlam hdeg u hu j (Finset.mem_Icc.mp hj).1 (hparams.2 j hj).2
  have hdis : (I:Set ℕ).PairwiseDisjoint L := by
    intro i hi j hj hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxi := (Finset.mem_filter.mp hx).2
    have hxj := (Finset.mem_filter.mp hy).2
    have : i=j := by exact_mod_cast hxi.symm.trans hxj
    exact hne this
  have hsub : I.biUnion L ⊆ ball H u a := by
    intro x hx
    obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,(Finset.mem_filter.mp hxj).2,(hparams.2 j hj).1⟩
  have hsum : (∑ j ∈ I, ((L j).card:ℝ)) ≤ ((ball H u a).card:ℝ) := by
    have hn := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdis] at hn
    exact_mod_cast hn
  have hsumlo : (J:ℝ)*(δ/3) ≤ ∑ j ∈ I, ((L j).card:ℝ) := by
    calc
      _ = ∑ _j ∈ I, δ/3 := by simp [I,Nat.card_Icc]
      _ ≤ _ := Finset.sum_le_sum hbound
  have hhalf := mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ δ/3)
  nlinarith

theorem solution {V : Type} [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V))
    (l : ℝ) (Vs : Finset V)
    (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R)
    (hlam : ∀ q ∈ R, l ≤ (privLen H R q:ℝ)) (hl : 1 ≤ l) :
    (∀ δ : ℝ, 0 < δ → (∀ x ∈ Vs, δ ≤ (coreDeg H R Vs x:ℝ)) →
      ∀ u ∈ Vs, ∀ a : ℝ, 1 ≤ a → δ/6*min a l ≤ ((ball H u a).card:ℝ)) ∧
    (∀ d : ℝ, 0 < d → (∀ x ∈ Vs, d/40 ≤ (coreDeg H R Vs x:ℝ)) →
      ∀ u ∈ Vs, ∀ a : ℝ, 1 ≤ a → d/240*min a l ≤ ((ball H u a).card:ℝ)) := by
  have hfirst := fun δ hδ hdeg u hu a ha => ball_growth_general G H R l δ Vs hR hH hlam hl hδ hdeg u hu a ha
  refine ⟨hfirst,?_⟩
  intro d hd hdeg u hu a ha
  have h := hfirst (d/40) (by positivity) hdeg u hu a ha
  convert h using 1 <;> ring
