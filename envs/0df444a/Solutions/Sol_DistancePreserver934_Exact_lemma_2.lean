-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:43:14.4109+00:00
-- url     : https://prove2.me/submissions/05ffd458-4f97-4dfb-901c-b9314e26529d

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


set_option autoImplicit false
open Classical DistancePreserver934.Exact

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


lemma shortest_suffix {V : Type} [Fintype V] {H : SimpleGraph V} {s a t : V}
    (p : H.Walk s a) (q : H.Walk a t) (hw : IsShortest (p.append q)) : IsShortest q := by
  have hrev : IsShortest (q.reverse.append p.reverse) := by
    simpa [IsShortest,← SimpleGraph.Walk.reverse_append,SimpleGraph.edist_comm] using hw
  have hq := shortest_prefix q.reverse p.reverse hrev
  simpa [IsShortest,SimpleGraph.edist_comm] using hq


lemma shortest_getVert_distance {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V}
    (w : H.Walk s t) (hw : IsShortest w) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ w.length) :
    H.edist (w.getVert i) (w.getVert j) = ((j-i:ℕ):ℕ∞) := by
  have hdrop := shortest_suffix (w.take i) (w.drop i) (by rw [w.append_take_drop_eq]; exact hw)
  have hseg := shortest_prefix ((w.drop i).take (j-i)) ((w.drop i).drop (j-i))
    (by rw [SimpleGraph.Walk.append_take_drop_eq]; exact hdrop)
  have hlen : ((w.drop i).take (j-i)).length = j-i := by
    simp only [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length]
    omega
  change (((w.drop i).take (j-i)).length:ℕ∞) = H.edist (w.getVert i) ((w.drop i).getVert (j-i)) at hseg
  rw [hlen,SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hij] at hseg
  exact hseg.symm

lemma shortest_support_metric {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V}
    (w : H.Walk s t) (hw : IsShortest w) (x y : V) (hx : x ∈ w.support) (hy : y ∈ w.support) :
    ∃ k : ℕ, H.edist x y=(k:ℕ∞) ∧ (k:ℝ)=|(H.dist s x:ℝ)-(H.dist s y:ℝ)| := by
  classical
  let i := w.support.idxOf x
  let j := w.support.idxOf y
  have hi : i ≤ w.length := by
    have h := List.idxOf_lt_length_of_mem hx
    rw [w.length_support] at h
    omega
  have hj : j ≤ w.length := by
    have h := List.idxOf_lt_length_of_mem hy
    rw [w.length_support] at h
    omega
  have hx' : w.getVert i=x := w.getVert_support_idxOf hx
  have hy' : w.getVert j=y := w.getVert_support_idxOf hy
  have hdx := shortest_support_dist w hw x hx
  have hdy := shortest_support_dist w hw y hy
  by_cases hij : i ≤ j
  · refine ⟨j-i,?_,?_⟩
    · simpa only [hx',hy'] using shortest_getVert_distance w hw i j hij hj
    · rw [hdx,hdy]
      change ((j-i:ℕ):ℝ) = |(i:ℝ)-(j:ℝ)|
      have hij' : (i:ℝ) ≤ j := by exact_mod_cast hij
      rw [Nat.cast_sub hij,abs_of_nonpos (by linarith)]
      ring
  · have hji : j ≤ i := le_of_not_ge hij
    refine ⟨i-j,?_,?_⟩
    · rw [SimpleGraph.edist_comm]
      simpa only [hx',hy'] using shortest_getVert_distance w hw j i hji hi
    · rw [hdx,hdy]
      change ((i-j:ℕ):ℝ) = |(i:ℝ)-(j:ℝ)|
      have hji' : (j:ℝ) ≤ i := by exact_mod_cast hji
      rw [Nat.cast_sub hji,abs_of_nonneg (by linarith)]

lemma pairwise_of_diamLE {V : Type} [Fintype V] (H : SimpleGraph V) (S : Finset V)
    (D : ℝ) (hD : DiamLE H S D) (x y : V) (hx : x ∈ S) (hy : y ∈ S) :
    ∃ k : ℕ, H.edist x y=(k:ℕ∞) ∧ (k:ℝ) ≤ D := by
  have hle : H.edist x y ≤ diam H S :=
    le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
  have hle' : H.edist x y ≤ ((diam H S).toNat:ℕ∞) := by
    rwa [ENat.natCast_toNat hD.1]
  obtain ⟨k,hk,hkbound⟩ := ENat.le_natCast_iff.mp hle'
  refine ⟨k,hk,?_⟩
  exact (show (k:ℝ) ≤ ((diam H S).toNat:ℝ) by exact_mod_cast hkbound).trans hD.2


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open Classical DistancePreserver934.Exact

lemma essential_symm {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V} {e : Sym2 V}
    (he : IsEssential H s(s,t) e) : IsEssential H s(t,s) e := by
  simpa only [Sym2.eq_swap] using he

lemma essential_prefix {V : Type} [Fintype V] (G H : SimpleGraph V)
    (R : Finset (Sym2 V)) (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R)
    (q e : Sym2 V) (hq : q ∈ R) (he : IsEssential H q e) (s t : V) (hst : s(s,t)=q)
    (w : H.Walk s t) (hw : IsShortest w) (i : ℕ) (hi : i < w.length)
    (hei : e=s(w.getVert i,w.getVert (i+1))) :
    IsEssential H s(s,w.getVert (i+1)) e := by
  apply inherited_essential G H R hR hH q e hq he s t hst w hw s (w.getVert (i+1))
    .nil (w.take (i+1)) (w.drop (i+1))
  · simp only [SimpleGraph.Walk.nil_append]
    exact (w.append_take_drop_eq (i+1)).symm
  · rw [SimpleGraph.Walk.edges_take,hei]
    have hidx : i < w.edges.length := by simpa using hi
    have hget := w.getElem_edges hidx
    have hmem : w.edges[i] ∈ w.edges.take (i+1) := by
      apply List.mem_iff_getElem.mpr
      refine ⟨i,by simp only [List.length_take]; omega,?_⟩
      simp only [List.getElem_take]
    simpa only [hget] using hmem

lemma shortest_segment {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V}
    (w : H.Walk s t) (hw : IsShortest w) (x y : V)
    (hx : x ∈ w.support) (hy : y ∈ w.support) :
    ∃ P : H.Walk x y, IsShortest P ∧ P.edges ⊆ w.edges := by
  obtain ⟨P,hP⟩ := ((w.takeUntil x hx).reachable.symm.trans (w.takeUntil y hy).reachable).exists_walk_length_eq_edist
  -- Every shortest x-y walk need not lie on w; choose the actual segment instead.
  let i := w.support.idxOf x
  let j := w.support.idxOf y
  have hix : w.getVert i=x := w.getVert_support_idxOf hx
  have hjy : w.getVert j=y := w.getVert_support_idxOf hy
  have hi : i ≤ w.length := by
    have hh := List.idxOf_lt_length_of_mem hx
    rw [w.length_support] at hh
    omega
  have hj : j ≤ w.length := by
    have hh := List.idxOf_lt_length_of_mem hy
    rw [w.length_support] at hh
    omega
  have hseg : ∀ a b : ℕ, a≤b → b≤w.length →
      ∃ Q : H.Walk (w.getVert a) (w.getVert b), IsShortest Q ∧ Q.edges ⊆ w.edges := by
    intro a b hab hb
    let Q := ((w.drop a).take (b-a)).copy rfl (by rw [SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hab])
    refine ⟨Q,?_,?_⟩
    · change (Q.length:ℕ∞)=_
      have hlen : Q.length=b-a := by simp [Q,SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length]; omega
      rw [hlen]
      exact (shortest_getVert_distance w hw a b hab hb).symm
    · intro e he
      have he' : e ∈ (w.edges.drop a).take (b-a) := by simpa [Q,SimpleGraph.Walk.edges_take,SimpleGraph.Walk.edges_drop] using he
      exact (List.drop_subset _ _) ((List.take_subset _ _) he')
  by_cases hij : i≤j
  · obtain ⟨Q,hQ,hsub⟩ := hseg i j hij hj
    exact ⟨Q.copy hix hjy,by simpa [IsShortest,hix,hjy] using hQ,by simpa using hsub⟩
  · obtain ⟨Q,hQ,hsub⟩ := hseg j i (by omega) hi
    refine ⟨Q.reverse.copy hix hjy,?_,?_⟩
    · simpa [IsShortest,hix,hjy,SimpleGraph.edist_comm] using hQ
    · simpa using hsub

lemma shortest_endpoint_avoids {V : Type} [Fintype V] {H : SimpleGraph V} {u x y : V}
    (P : H.Walk u x) (hP : IsShortest P) (hxy : H.dist u x < H.dist u y)
    (e : Sym2 V) (hye : y ∈ e) : e ∉ P.edges := by
  intro he
  have hy : y ∈ P.support := SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e,he,hye⟩)
  have hd := shortest_support_dist P hP y hy
  have hidx := List.idxOf_lt_length_of_mem hy
  have hlen : P.length=H.dist u x := congrArg ENat.toNat hP
  rw [P.length_support] at hidx
  omega

lemma shortest_reroute {V : Type} [Fintype V] {H : SimpleGraph V} {u x y : V}
    (P : H.Walk u x) (Q : H.Walk x y) (hP : IsShortest P) (hQ : IsShortest Q)
    (hadd : H.dist u y=H.dist u x+H.dist x y) (huy : H.Reachable u y) :
    IsShortest (P.append Q) := by
  have hPlen := congrArg ENat.toNat hP
  have hQlen := congrArg ENat.toNat hQ
  change (((P.append Q).length):ℕ∞)=_
  rw [SimpleGraph.Walk.length_append]
  change ((P.length+Q.length:ℕ):ℕ∞)=_
  rw [show P.length=H.dist u x from hPlen,show Q.length=H.dist x y from hQlen,← hadd]
  exact huy.coe_dist_eq_edist

lemma earlier_in_prefix {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V}
    (w : H.Walk s t) (hw : IsShortest w) (x y : V) (hx : x∈w.support) (hy : y∈w.support)
    (hxy : H.dist s x ≤ H.dist s y) : x∈(w.takeUntil y hy).support := by
  classical
  have hidx : w.support.idxOf x ≤ w.support.idxOf y := by
    simpa only [shortest_support_dist w hw x hx,shortest_support_dist w hw y hy] using hxy
  rw [SimpleGraph.Walk.takeUntil_eq_take,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_take]
  exact (List.mem_take_iff_idxOf_lt hx).mpr (by omega)

lemma path_dist_add {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V}
    (w : H.Walk s t) (hw : IsShortest w) (x y : V) (hx : x∈w.support) (hy : y∈w.support)
    (hxy : H.dist s x ≤ H.dist s y) : H.dist s y=H.dist s x+H.dist x y := by
  classical
  let i := w.support.idxOf x
  let j := w.support.idxOf y
  have hdx := shortest_support_dist w hw x hx
  have hdy := shortest_support_dist w hw y hy
  have hij : i≤j := by simpa only [hdx,hdy] using hxy
  have hj : j≤w.length := by
    have hh := List.idxOf_lt_length_of_mem hy
    rw [w.length_support] at hh
    omega
  have hd := shortest_getVert_distance w hw i j hij hj
  rw [w.getVert_support_idxOf hx,w.getVert_support_idxOf hy] at hd
  have hd' := congrArg ENat.toNat hd
  change H.dist x y=j-i at hd'
  rw [hdx,hdy]
  omega


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open Classical DistancePreserver934.Exact

lemma orientation_minimal_essential {V : Type} [Fintype V] (K : SimpleGraph V)
    (R : Finset (Sym2 V)) (hR : IsDemandSet K R) (hK : IsMinimalPreserver K K R)
    (e : Sym2 V) (he : e ∈ K.edgeSet) : (essSet K R e).Nonempty := by
  by_contra hn
  have hnone : ∀ q ∈ R, ¬ IsEssential K q e := by
    intro q hq hess
    exact hn ⟨q, Finset.mem_filter.mpr ⟨hq, hess⟩⟩
  apply hK.2 e he
  refine ⟨K.deleteEdges_le _, ?_⟩
  intro s t hst
  have hnot := hnone s(s,t) hst
  simp only [IsEssential, not_forall] at hnot
  obtain ⟨a,b,hab,w,hw,hew⟩ := hnot
  have hwlen : (w.length : ℕ∞) = K.edist s t := by
    rcases Sym2.eq_iff.mp hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hw
    · simpa [IsShortest, SimpleGraph.edist_comm] using hw
  have hdist : (K.deleteEdges {e}).edist a b ≤ K.edist a b := by
    calc
      _ ≤ ((w.toDeleteEdge e hew).length : ℕ∞) := SimpleGraph.edist_le _
      _ = K.edist a b := by simpa [IsShortest, SimpleGraph.Walk.toDeleteEdge,
        SimpleGraph.Walk.toDeleteEdges, SimpleGraph.Walk.length_transfer] using hw
  have hdeq : (K.deleteEdges {e}).edist a b = K.edist a b :=
    le_antisymm hdist (SimpleGraph.edist_anti (K.deleteEdges_le _))
  rcases Sym2.eq_iff.mp hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hdeq
  · simpa only [SimpleGraph.edist_comm] using hdeq


structure BranchOrientation {V : Type} [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V)) where
  subgraph : H ≤ G
  src : R → V
  dst : R → V
  pair : ∀ q, s(src q,dst q)=q.val
  path : ∀ q, H.Walk (src q) (dst q)
  shortest : ∀ q, IsShortest (path q)
  shortestG : ∀ q, IsShortest ((path q).mapLe subgraph)
  label : edgesF H → R
  head : edgesF H → V
  head_mem : ∀ e, head e ∈ e.val
  head_support : ∀ e, head e ∈ (path (label e)).support
  prefix_essential : ∀ e, IsEssential H s(src (label e),head e) e.val

lemma orientation_exists {V : Type} [Fintype V] (G H : SimpleGraph V)
    (R : Finset (Sym2 V)) (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R)
    (src dst : R → V) (hpair : ∀ q, s(src q,dst q)=q.val) :
    Nonempty (BranchOrientation G H R) := by
  classical
  have hRH : IsDemandSet H R := by
    intro s t hq
    refine ⟨(hR s t hq).1,?_⟩
    apply SimpleGraph.edist_ne_top_iff_reachable.mp
    rw [hH.1.2 s t hq]
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hR s t hq).2
  have hself : IsMinimalPreserver H H R := by
    refine ⟨⟨le_rfl,fun _ _ _ => rfl⟩,?_⟩
    intro e he hdel
    apply hH.2 e he
    exact ⟨hdel.1.trans hH.1.1,fun s t hq => (hdel.2 s t hq).trans (hH.1.2 s t hq)⟩
  have hpaths : ∀ q : R, ∃ p : H.Walk (src q) (dst q), IsShortest p := by
    intro q
    have hmem : s(src q,dst q) ∈ R := hpair q ▸ q.property
    exact (hRH _ _ hmem).2.exists_walk_length_eq_edist
  choose path hpath using hpaths
  have hlabels : ∀ e : edgesF H, ∃ q : R, IsEssential H q.val e.val := by
    intro e
    obtain ⟨q,hq⟩ := orientation_minimal_essential H R hRH hself e.val (Finset.mem_filter.mp e.property).2
    exact ⟨⟨q,(Finset.mem_filter.mp hq).1⟩,(Finset.mem_filter.mp hq).2⟩
  choose lab hlab using hlabels
  have hindices : ∀ e : edgesF H, ∃ i : ℕ, i<(path (lab e)).length ∧
      e.val=s((path (lab e)).getVert i,(path (lab e)).getVert (i+1)) := by
    intro e
    have hem := hlab e _ _ (hpair (lab e)) _ (hpath (lab e))
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hem
    refine ⟨i,by simpa using hi,?_⟩
    exact he.symm.trans ((path (lab e)).getElem_edges hi)
  choose idx hidx using hindices
  refine ⟨{ subgraph := hH.1.1, src := src, dst := dst, pair := hpair, path := path,
            shortest := hpath, shortestG := ?_, label := lab,
            head := fun e => (path (lab e)).getVert (idx e+1), head_mem := ?_, head_support := ?_,
            prefix_essential := ?_ }⟩
  · intro q
    have hmem : s(src q,dst q) ∈ R := hpair q ▸ q.property
    simpa [IsShortest,hH.1.2 _ _ hmem] using hpath q
  · intro e
    rw [(hidx e).2]
    simp
  · intro e
    exact (path (lab e)).getVert_mem_support _
  · intro e
    exact essential_prefix G H R hR hH _ _ (lab e).property (hlab e)
      _ _ (hpair (lab e)) _ (hpath (lab e)) _ (hidx e).1 (hidx e).2

namespace BranchOrientation
variable {V : Type} [Fintype V] {G H : SimpleGraph V} {R : Finset (Sym2 V)}
    (O : BranchOrientation G H R)

lemma prefix_dist (q : R) (x : V) (hx : x ∈ (O.path q).support) :
    G.dist (O.src q) x=H.dist (O.src q) x := by
  have hm : x ∈ ((O.path q).mapLe O.subgraph).support := by simpa using hx
  rw [shortest_support_dist _ (O.shortestG q) x hm,shortest_support_dist _ (O.shortest q) x hx]
  simp

lemma head_reachable (e : edgesF H) : H.Reachable (O.src (O.label e)) (O.head e) :=
  ((O.path (O.label e)).takeUntil (O.head e) (O.head_support e)).reachable

lemma incoming_unique (e f : edgesF H) (hhead : O.head e=O.head f)
    (hsrc : O.src (O.label e)=O.src (O.label f)) : e=f := by
  apply Subtype.ext
  apply endpoint_essential_unique H (O.head e) (O.src (O.label e)) (O.head_reachable e).symm
    e.val f.val (O.head_mem e) (hhead ▸ O.head_mem f) (essential_symm (O.prefix_essential e))
  have h := essential_symm (O.prefix_essential f)
  simpa only [← hhead,← hsrc] using h

lemma incoming_path_unique (e : edgesF H) (q : R) (x : V) (hx : x∈(O.path q).support)
    (heq : O.label e=q) (hex : O.head e=x) (f : Sym2 V)
    (hfx : x∈f) (hf : f∈((O.path q).takeUntil x hx).edges) : e.val=f := by
  let P := (O.path q).takeUntil x hx
  have hP : IsShortest P := shortest_prefix P ((O.path q).dropUntil x hx)
    (by rw [(O.path q).take_spec hx]; exact O.shortest q)
  have hess : IsEssential H s(O.src q,x) e.val := by simpa only [heq,hex] using O.prefix_essential e
  have he : e.val∈P.edges := hess _ _ rfl P hP
  have hbound := path_incident_bound P.reverse (shortest_isPath (by
    simpa [IsShortest,SimpleGraph.edist_comm] using hP)) x
  simp only [ite_true,SimpleGraph.Walk.edges_reverse,List.toFinset_reverse] at hbound
  apply Finset.card_le_one.mp hbound
  · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr he,by simpa only [hex] using O.head_mem e⟩
  · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hf,hfx⟩

end BranchOrientation


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open Classical DistancePreserver934.Exact

namespace BranchOrientation
variable {V : Type} [Fintype V] {G H : SimpleGraph V} {R : Finset (Sym2 V)}
    (O : BranchOrientation G H R)

lemma no_arrival (q : R) (f : edgesF H) (x : V)
    (hx : x∈(O.path q).support) (hy : O.head f∈(O.path q).support)
    (hxy : H.dist (O.src q) x < H.dist (O.src q) (O.head f))
    (hf : f.val ∉ ((O.path q).takeUntil (O.head f) hy).edges)
    (hr : H.Reachable (O.src (O.label f)) x)
    (hadd : H.dist (O.src (O.label f)) (O.head f)=
      H.dist (O.src (O.label f)) x+H.dist x (O.head f)) : False := by
  have hxpre := earlier_in_prefix (O.path q) (O.shortest q) x (O.head f) hx hy hxy.le
  let pref := (O.path q).takeUntil (O.head f) hy
  have hpref : IsShortest pref := shortest_prefix pref ((O.path q).dropUntil (O.head f) hy)
    (by rw [(O.path q).take_spec hy]; exact O.shortest q)
  obtain ⟨P,hP,hsub⟩ := shortest_segment pref hpref x (O.head f) hxpre pref.end_mem_support
  obtain ⟨A,hA⟩ := hr.exists_walk_length_eq_edist
  have hne : x≠O.head f := by intro h; rw [h] at hxy; omega
  have hdistpos : 0<H.dist x (O.head f) := Nat.pos_of_ne_zero (fun h => hne (P.reachable.dist_eq_zero_iff.mp h))
  have hshort := shortest_reroute A P hA hP hadd (O.head_reachable f)
  have hmem := O.prefix_essential f _ _ rfl (A.append P) hshort
  rcases List.mem_append.mp (by simpa only [SimpleGraph.Walk.edges_append] using hmem) with ha | hp
  · exact shortest_endpoint_avoids A hA (by omega) _ (O.head_mem f) ha
  · exact hf (hsub hp)

lemma forbidden_delta_injective (q : R) (e f : edgesF H)
    (hx : O.head e∈(O.path q).support) (hy : O.head f∈(O.path q).support)
    (he : e.val∉((O.path q).takeUntil (O.head e) hx).edges)
    (hf : f.val∉((O.path q).takeUntil (O.head f) hy).edges)
    (hs : O.src (O.label e)=O.src (O.label f))
    (hdelta : (H.dist (O.src (O.label e)) (O.head e):ℤ)-(H.dist (O.src q) (O.head e):ℤ)=
      (H.dist (O.src (O.label f)) (O.head f):ℤ)-(H.dist (O.src q) (O.head f):ℤ)) : e=f := by
  by_cases hh : O.head e=O.head f
  · exact O.incoming_unique e f hh hs
  have hdistne : H.dist (O.src q) (O.head e) ≠ H.dist (O.src q) (O.head f) := by
    intro hd
    have hi := (shortest_support_dist (O.path q) (O.shortest q) (O.head e) hx).symm.trans
      (hd.trans (shortest_support_dist (O.path q) (O.shortest q) (O.head f) hy))
    exact hh (List.idxOf_inj hx |>.mp hi)
  have run : ∀ a b : edgesF H, ∀ ha : O.head a∈(O.path q).support,
      ∀ hb : O.head b∈(O.path q).support,
      b.val∉((O.path q).takeUntil (O.head b) hb).edges →
      O.src (O.label a)=O.src (O.label b) →
      (H.dist (O.src (O.label a)) (O.head a):ℤ)-(H.dist (O.src q) (O.head a):ℤ)=
      (H.dist (O.src (O.label b)) (O.head b):ℤ)-(H.dist (O.src q) (O.head b):ℤ) →
      H.dist (O.src q) (O.head a)<H.dist (O.src q) (O.head b) → False := by
    intro a b ha hb hbnot hsrc hd hlt
    apply O.no_arrival q b (O.head a) ha hb hlt hbnot
    · simpa only [← hsrc] using O.head_reachable a
    · have hpath := path_dist_add (O.path q) (O.shortest q) (O.head a) (O.head b) ha hb hlt.le
      have hpint : (H.dist (O.src q) (O.head b):ℤ)=
          (H.dist (O.src q) (O.head a):ℤ)+(H.dist (O.head a) (O.head b):ℤ) := by exact_mod_cast hpath
      rw [hsrc] at hd
      omega
  rcases lt_or_gt_of_ne hdistne with hlt | hgt
  · exact False.elim (run e f hx hy hf hs hdelta hlt)
  · exact False.elim (run f e hy hx he hs.symm hdelta.symm hgt)

lemma outside_path_unique (q r : R) (e f : edgesF H)
    (hle : O.label e=r) (hlf : O.label f=r)
    (hx : O.head e∈(O.path q).support) (hy : O.head f∈(O.path q).support)
    (he : e.val∉(O.path q).edges) (hf : f.val∉(O.path q).edges) : e=f := by
  by_cases hh : O.head e=O.head f
  · exact O.incoming_unique e f hh (by rw [hle,hlf])
  have her : O.head e∈(O.path r).support := by
      have hh := O.head_support e
      rw [hle] at hh
      exact hh
  have hfr : O.head f∈(O.path r).support := by
      have hh := O.head_support f
      rw [hlf] at hh
      exact hh
  have hdistne : H.dist (O.src r) (O.head e) ≠ H.dist (O.src r) (O.head f) := by
    intro hd
    rw [shortest_support_dist (O.path r) (O.shortest r) _ her,
      shortest_support_dist (O.path r) (O.shortest r) _ hfr] at hd
    exact hh (List.idxOf_inj her |>.mp hd)
  have run : ∀ a b : edgesF H, O.label a=r → O.label b=r →
      O.head a∈(O.path q).support → O.head b∈(O.path q).support →
      b.val∉(O.path q).edges →
      H.dist (O.src r) (O.head a)<H.dist (O.src r) (O.head b) → False := by
    intro a b hla hlb ha hb hbnot hlt
    have har : O.head a∈(O.path r).support := by
      have hh := O.head_support a
      rw [hla] at hh
      exact hh
    have hbr : O.head b∈(O.path r).support := by
      have hh := O.head_support b
      rw [hlb] at hh
      exact hh
    obtain ⟨P,hP,hsub⟩ := shortest_segment (O.path q) (O.shortest q) (O.head a) (O.head b) ha hb
    obtain ⟨A,hA⟩ := (O.head_reachable a).exists_walk_length_eq_edist
    have hdist := path_dist_add (O.path r) (O.shortest r) _ _ har hbr hlt.le
    have hdist' : H.dist (O.src (O.label a)) (O.head b)=
        H.dist (O.src (O.label a)) (O.head a)+H.dist (O.head a) (O.head b) := by simpa only [hla] using hdist
    have hreach : H.Reachable (O.src (O.label a)) (O.head b) := by simpa only [hla,hlb] using O.head_reachable b
    have hp := shortest_reroute A P hA hP hdist' hreach
    have hess : IsEssential H s(O.src (O.label a),O.head b) b.val := by
      simpa only [hla,hlb] using O.prefix_essential b
    have hmem := hess _ _ rfl (A.append P) hp
    rcases List.mem_append.mp (by simpa only [SimpleGraph.Walk.edges_append] using hmem) with hm | hm
    · exact shortest_endpoint_avoids A hA (by simpa only [hla] using hlt) _ (O.head_mem b) hm
    · exact hbnot (hsub hm)
  rcases lt_or_gt_of_ne hdistne with hlt | hgt
  · exact False.elim (run e f hle hlf hx hy hf hlt)
  · exact False.elim (run f e hlf hle hy hx he hgt)

end BranchOrientation


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open Classical DistancePreserver934.Exact

lemma fiber_square_bound {α V : Type} [Fintype α] [Fintype V] [DecidableEq α] [DecidableEq V]
    (A : Finset α) (U : Finset V) (head : α → V) (hh : ∀ a∈A, head a∈U) :
    (A.card:ℝ)^2 ≤ (U.card:ℝ)*(((A ×ˢ A).filter (fun p => head p.1=head p.2)).card:ℝ) := by
  classical
  let D := fun x => A.filter (fun a => head a=x)
  have hsum : ∑ x∈U, (D x).card=A.card := by
    simpa only [D,Finset.filter_eq_self.mpr hh] using Finset.sum_card_fiberwise_eq_card_filter A U head
  have hsum2 : ∑ x∈U, (D x).card^2=((A ×ˢ A).filter (fun p => head p.1=head p.2)).card := by
    let T := (A ×ˢ A).filter (fun p => head p.1=head p.2)
    have hT : ∀ p∈T, head p.1∈U := fun p hp => hh p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have h := Finset.sum_card_fiberwise_eq_card_filter T U (fun p => head p.1)
    rw [Finset.filter_eq_self.mpr hT] at h
    have heq : ∀ x∈U, T.filter (fun p => head p.1=x) = D x ×ˢ D x := by
      intro x hx
      ext p
      simp only [T,D,Finset.mem_filter,Finset.mem_product]
      aesop
    calc
      _ = ∑ x∈U, (T.filter (fun p => head p.1=x)).card := Finset.sum_congr rfl (fun x hx => by rw [heq x hx,Finset.card_product,pow_two])
      _ = _ := h
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1:ℝ)) (fun x => ((D x).card:ℝ))
  have hs : ∑ x∈U, ((D x).card:ℝ)=(A.card:ℝ) := by exact_mod_cast hsum
  have hs2 : ∑ x∈U, ((D x).card:ℝ)^2=(((A ×ˢ A).filter (fun p => head p.1=head p.2)).card:ℝ) := by exact_mod_cast hsum2
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,hs,hs2] using hcauchy

namespace BranchOrientation
variable {V : Type} [Fintype V] {G H : SimpleGraph V} {R : Finset (Sym2 V)}
    (O : BranchOrientation G H R)

lemma edge_path (e : edgesF H) : e.val∈(O.path (O.label e)).edges := by
  let P := (O.path (O.label e)).takeUntil (O.head e) (O.head_support e)
  have hP : IsShortest P := shortest_prefix P ((O.path (O.label e)).dropUntil (O.head e) (O.head_support e))
    (by rw [SimpleGraph.Walk.take_spec]; exact O.shortest _)
  exact (O.path (O.label e)).edges_takeUntil_subset_edges _
    (O.prefix_essential e _ _ rfl P hP)

lemma head_collisions_ce :
    (((Finset.univ : Finset (edgesF H × edgesF H)).filter (fun p => O.head p.1=O.head p.2)).card:ℝ)
      ≤ 2*(numEdges H:ℝ)+(R.card:ℝ)^2 := by
  classical
  let T := (Finset.univ : Finset (edgesF H × edgesF H)).filter (fun p => O.head p.1=O.head p.2)
  let F := T.filter (fun p => p.2.val∈(O.path (O.label p.1)).edges)
  let B := T.filter (fun p => p.2.val∉(O.path (O.label p.1)).edges)
  have hsplit : T.card=F.card+B.card := by
    exact (Finset.card_filter_add_card_filter_not (s := T) (fun p => p.2.val∈(O.path (O.label p.1)).edges)).symm
  have hF : F.card ≤ 2*(edgesF H).card := by
    have hrows : ∀ e : edgesF H, (F.filter (fun p => p.1=e)).card ≤ 2 := by
      intro e
      let L := (O.path (O.label e)).edges.toFinset.filter (fun f => O.head e∈f)
      have hb : L.card≤2 := (path_incident_bound _ (shortest_isPath (O.shortest (O.label e))) _).trans (by split_ifs <;> omega)
      apply le_trans (Finset.card_le_card_of_injOn (fun p : edgesF H × edgesF H => p.2.val) ?_ ?_) hb
      · intro p hp
        obtain ⟨hp,heq⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp,hpath⟩ := Finset.mem_filter.mp hp
        have hhead := (Finset.mem_filter.mp hp).2
        subst e
        exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hpath,hhead ▸ O.head_mem p.2⟩
      · intro p hp p' hp' heq
        have hpe := (Finset.mem_filter.mp hp).2
        have hp'e := (Finset.mem_filter.mp hp').2
        exact Prod.ext (hpe.trans hp'e.symm) (Subtype.ext heq)
    have hsum := Finset.sum_card_fiberwise_eq_card_filter F Finset.univ Prod.fst
    simp only [Finset.mem_univ,Finset.filter_true] at hsum
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (edgesF H))) (fun e _ => hrows e)
    rw [hsum] at hh
    simpa [mul_comm] using hh
  have hB : B.card ≤ R.card^2 := by
    have hinj : Set.InjOn (fun p : edgesF H × edgesF H => (O.label p.1,O.label p.2)) B := by
      intro p hp p' hp' heq
      have hpB := Finset.mem_filter.mp hp
      have hp'B := Finset.mem_filter.mp hp'
      have hhead := (Finset.mem_filter.mp hpB.1).2
      have hhead' := (Finset.mem_filter.mp hp'B.1).2
      have hl1 : O.label p.1=O.label p'.1 := congrArg Prod.fst heq
      have hl2 : O.label p.2=O.label p'.2 := congrArg Prod.snd heq
      have hx : O.head p.2∈(O.path (O.label p.1)).support := by rw [← hhead]; exact O.head_support p.1
      have hy : O.head p'.2∈(O.path (O.label p.1)).support := by rw [hl1,← hhead']; exact O.head_support p'.1
      have hff := O.outside_path_unique (O.label p.1) (O.label p.2) p.2 p'.2 rfl hl2.symm hx hy hpB.2
        (by rw [hl1]; exact hp'B.2)
      have hee := O.incoming_unique p.1 p'.1 (hhead.trans ((congrArg O.head hff).trans hhead'.symm))
        (congrArg O.src hl1)
      exact Prod.ext hee hff
    have hc := Finset.card_le_card_of_injOn (fun p : edgesF H × edgesF H => (O.label p.1,O.label p.2))
      (fun _ _ => Finset.mem_univ _) hinj
    simpa [Fintype.card_prod,Fintype.card_coe,pow_two] using hc
  change (T.card:ℝ)≤_
  have hf' : (F.card:ℝ)≤2*(numEdges H:ℝ) := by exact_mod_cast hF
  have hb' : (B.card:ℝ)≤(R.card:ℝ)^2 := by exact_mod_cast hB
  have hs' : (T.card:ℝ)=(F.card:ℝ)+(B.card:ℝ) := by exact_mod_cast hsplit
  linarith

end BranchOrientation


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open Classical DistancePreserver934.Exact

theorem solution : ∃ C : ℝ, 0<C ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V)),
      IsDemandSet G R → IsMinimalPreserver G H R →
      (numEdges H:ℝ)≤C*((Fintype.card V:ℝ)+(R.card:ℝ)*Real.sqrt (Fintype.card V:ℝ)) := by
  refine ⟨3,by norm_num,?_⟩
  intro V _ G H R hR hH
  let src : R → V := fun q => q.val.out.1
  let dst : R → V := fun q => q.val.out.2
  have hpair : ∀ q : R, s(src q,dst q)=q.val := fun q => Quot.out_eq q.val
  obtain ⟨O⟩ := orientation_exists G H R hR hH src dst hpair
  have hsq := fiber_square_bound (Finset.univ : Finset (edgesF H)) Finset.univ O.head
    (fun _ _ => Finset.mem_univ _)
  have hcount := O.head_collisions_ce
  have hsq' : (numEdges H:ℝ)^2 ≤ (Fintype.card V:ℝ)*(2*(numEdges H:ℝ)+(R.card:ℝ)^2) := by
    have hbase : (numEdges H:ℝ)^2 ≤ (Fintype.card V:ℝ)*
        (((Finset.univ : Finset (edgesF H × edgesF H)).filter (fun p => O.head p.1=O.head p.2)).card:ℝ) := by
      simpa only [Finset.univ_product_univ,Finset.card_univ,Fintype.card_coe,numEdges] using hsq
    exact hbase.trans (mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg _))
  let m := (numEdges H:ℝ)
  let n := (Fintype.card V:ℝ)
  let p := (R.card:ℝ)
  let q := p*Real.sqrt n
  have hn : 0≤n := Nat.cast_nonneg _
  have hq : 0≤q := by positivity
  have hq2 : q^2=n*p^2 := by dsimp [q]; rw [mul_pow,Real.sq_sqrt hn]; ring
  have hm : m≤2*n+q := by
    by_contra! hh
    have hmp : 0 < m := by linarith
    have h2 : q < m-2*n := by linarith
    have h1 : q ≤ m := by linarith
    have hp1 := mul_le_mul_of_nonneg_right h1 hq
    have hp2 := mul_lt_mul_of_pos_left h2 hmp
    change m^2≤n*(2*m+p^2) at hsq'
    nlinarith
  change m≤3*(n+q)
  linarith

