-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:35:19.198207+00:00
-- url     : https://prove2.me/submissions/5776e838-e10b-4f2b-b898-81c1f0f40abc

import Theorems.Thm_DistancePreserver934_Exact_lemma_4
import Theorems.Thm_DistancePreserver934_Exact_lemma_12
import Theorems.Thm_DistancePreserver934_Exact_lemma_14
import Definitions.Def_DistancePreserver934_Exact_LoyalCore

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open Classical DistancePreserver934.Exact



private lemma shortest_prefix {V : Type} [Fintype V] {H : SimpleGraph V} {s a t : V}
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


private lemma minimal_within {V : Type} [Fintype V] (G K : SimpleGraph V)
    (R R' : Finset (Sym2 V)) (hK : IsPreserver G K R) (hR : R' ⊆ R) :
    ∃ K' : SimpleGraph V, K' ≤ K ∧ IsMinimalPreserver G K' R' := by
  obtain ⟨K',⟨hpres,hsub⟩,hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun J : SimpleGraph V => IsPreserver G J R' ∧ J ≤ K)
    ⟨K,⟨hK.1,fun s t hst => hK.2 s t (hR hst)⟩,le_rfl⟩
  refine ⟨K',hsub,hpres,?_⟩
  intro e he hdel
  have hh := hmin ⟨hdel,(K'.deleteEdges_le _).trans hsub⟩ (K'.deleteEdges_le _)
  have heq : K' = K'.deleteEdges {e} := le_antisymm hh (K'.deleteEdges_le _)
  have : e ∈ (K'.deleteEdges {e}).edgeSet := heq ▸ he
  simpa [SimpleGraph.edgeSet_deleteEdges] using this


private lemma shortest_suffix {V : Type} [Fintype V] {H : SimpleGraph V} {s a t : V}
    (p : H.Walk s a) (q : H.Walk a t) (hw : IsShortest (p.append q)) : IsShortest q := by
  have hrev : IsShortest (q.reverse.append p.reverse) := by
    simpa [IsShortest,← SimpleGraph.Walk.reverse_append,SimpleGraph.edist_comm] using hw
  have hq := shortest_prefix q.reverse p.reverse hrev
  simpa [IsShortest,SimpleGraph.edist_comm] using hq

private lemma covered_split {V : Type} [Fintype V] (K : SimpleGraph V)
    (S : Finset V) (Q : Finset (Sym2 V)) (hset : IsDemandSet K Q) (hS : S.Nonempty)
    (hcov : Covers K S Q) :
    ∃ T : Finset (Sym2 V), IsDemandSet K T ∧ T.card ≤ 2*Q.card ∧
      (∀ a b : V, s(a,b) ∈ T → a ∈ S ∨ b ∈ S) ∧
      ∀ J : SimpleGraph V, IsPreserver K J T → IsPreserver K J Q := by
  classical
  have hrep (q : Sym2 V) : s(q.out.1,q.out.2)=q := Quot.out_eq q
  have hex (q : Sym2 V) (hq : q ∈ Q) : ∃ x ∈ S,
      K.Reachable x q.out.1 ∧ K.Reachable x q.out.2 ∧
      K.edist q.out.1 q.out.2 = K.edist q.out.1 x+K.edist x q.out.2 := by
    obtain ⟨x,hx,e,he,hxe,hess⟩ := hcov q hq
    have hreach := (hset q.out.1 q.out.2 (by rwa [hrep])).2
    obtain ⟨w,hw⟩ := hreach.exists_walk_length_eq_edist
    have hxw : x ∈ w.support := SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
      (Or.inr ⟨e,hess _ _ (hrep q) w hw,hxe⟩)
    have hp := shortest_prefix (w.takeUntil x hxw) (w.dropUntil x hxw)
      (by rw [w.take_spec hxw]; exact hw)
    have ht := shortest_suffix (w.takeUntil x hxw) (w.dropUntil x hxw)
      (by rw [w.take_spec hxw]; exact hw)
    refine ⟨x,hx,(w.takeUntil x hxw).reachable.symm,(w.dropUntil x hxw).reachable,?_⟩
    rw [← hp,← ht,← hw,← Nat.cast_add,← SimpleGraph.Walk.length_append,w.take_spec hxw]
  obtain ⟨x₀,hx₀⟩ := hS
  let x : Sym2 V → V := fun q => if hq : q ∈ Q then (hex q hq).choose else x₀
  have hx (q : Sym2 V) (hq : q ∈ Q) : x q ∈ S ∧
      K.Reachable (x q) q.out.1 ∧ K.Reachable (x q) q.out.2 ∧
      K.edist q.out.1 q.out.2 = K.edist q.out.1 (x q)+K.edist (x q) q.out.2 := by
    simpa only [x,dif_pos hq] using (hex q hq).choose_spec
  let U := Q.biUnion (fun q => {s(x q,q.out.1),s(x q,q.out.2)})
  let T := U.filter (fun e => ¬e.IsDiag)
  have hmember (a b : V) (hab : s(a,b) ∈ T) :
      ∃ q ∈ Q, s(a,b)=s(x q,q.out.1) ∨ s(a,b)=s(x q,q.out.2) := by
    have hu := (Finset.mem_filter.mp hab).1
    simpa only [U,Finset.mem_biUnion,Finset.mem_insert,Finset.mem_singleton] using hu
  have hvalid : IsDemandSet K T := by
    intro a b hab
    have habne : a ≠ b := by simpa using (Finset.mem_filter.mp hab).2
    obtain ⟨q,hq,heq | heq⟩ := hmember a b hab
    · rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨habne,(hx q hq).2.1⟩
      · exact ⟨habne,(hx q hq).2.1.symm⟩
    · rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨habne,(hx q hq).2.2.1⟩
      · exact ⟨habne,(hx q hq).2.2.1.symm⟩
  refine ⟨T,hvalid,?_,?_,?_⟩
  · calc
      T.card ≤ U.card := Finset.card_filter_le _ _
      _ ≤ ∑ _q ∈ Q, 2 := Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q hq => by
        exact (Finset.card_insert_le _ _).trans (by simp))
      _ = 2*Q.card := by simp [mul_comm]
  · intro a b hab
    obtain ⟨q,hq,heq | heq⟩ := hmember a b hab <;>
      rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl (hx q hq).1
    · exact Or.inr (hx q hq).1
    · exact Or.inl (hx q hq).1
    · exact Or.inr (hx q hq).1
  · intro J hJ
    have hsplit (q : Sym2 V) (hq : q ∈ Q) (v : V) (hv : v=q.out.1 ∨ v=q.out.2) :
        J.edist (x q) v = K.edist (x q) v := by
      by_cases heq : x q=v
      · simp [heq]
      apply hJ.2 (x q) v
      refine Finset.mem_filter.mpr ⟨?_,by simpa using heq⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨q,hq,?_⟩
      rcases hv with rfl | rfl <;> simp
    refine ⟨hJ.1,?_⟩
    intro a b hab
    let q := s(a,b)
    have hq : q ∈ Q := hab
    have h1 := hsplit q hq q.out.1 (Or.inl rfl)
    have h2 := hsplit q hq q.out.2 (Or.inr rfl)
    have hdist : J.edist q.out.1 q.out.2 = K.edist q.out.1 q.out.2 := by
      apply le_antisymm _ (SimpleGraph.edist_anti hJ.1)
      calc
        _ ≤ J.edist q.out.1 (x q)+J.edist (x q) q.out.2 := SimpleGraph.edist_triangle
        _ = K.edist q.out.1 (x q)+K.edist (x q) q.out.2 := by
          rw [SimpleGraph.edist_comm (u := q.out.1),h1,h2,SimpleGraph.edist_comm (u := x q) (v := q.out.1)]
        _ = K.edist q.out.1 q.out.2 := (hx q hq).2.2.2.symm
    rcases Sym2.eq_iff.mp (hrep q) with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa only [ha,hb] using hdist
    · simpa only [ha,hb,SimpleGraph.edist_comm] using hdist


private lemma local_covered_estimate : ∃ C : ℝ, 0<C ∧
    ∀ (V : Type) [Fintype V] (H : SimpleGraph V) (Q : Finset (Sym2 V)) (S U : Finset V) (D : ℝ),
      IsDemandSet H Q → S.Nonempty → Covers H S Q → DiamLE H S D →
      ∃ J : SimpleGraph V, IsPreserver H J Q ∧
        ((inducedEdges J U).card:ℝ) ≤ C*((U.card:ℝ)+
          Real.sqrt ((U.card:ℝ)*(Q.card:ℝ)*(S.card:ℝ)*D)) := by
  obtain ⟨B,hB,h4⟩ := DistancePreserver934.Exact.lemma_4
  refine ⟨2*B,by positivity,?_⟩
  intro V inst H Q S U D hQ hS hcov hD
  classical
  obtain ⟨T,hT,hcard,hsource,hpres⟩ := covered_split H S Q hQ hS hcov
  obtain ⟨J,hJsub,hJmin⟩ := minimal_within H H T T ⟨le_rfl,by simp⟩ le_rfl
  refine ⟨J,hpres J hJmin.1,?_⟩
  have hb := h4 V H J S D T U hS hD hT hsource hJmin
  have hD0 : 0≤D := (Nat.cast_nonneg _).trans hD.2
  have hc : (T.card:ℝ) ≤ 2*(Q.card:ℝ) := by exact_mod_cast hcard
  have hsqrt2 : Real.sqrt (2:ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  calc
    _ ≤ B*((U.card:ℝ)+Real.sqrt ((U.card:ℝ)*(T.card:ℝ)*(S.card:ℝ)*D)) := hb
    _ ≤ B*((U.card:ℝ)+Real.sqrt ((U.card:ℝ)*(2*(Q.card:ℝ))*(S.card:ℝ)*D)) := by gcongr
    _ = B*((U.card:ℝ)+Real.sqrt 2*Real.sqrt ((U.card:ℝ)*(Q.card:ℝ)*(S.card:ℝ)*D)) := by
      congr 2
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
      congr 1
      ring
    _ ≤ B*((U.card:ℝ)+2*Real.sqrt ((U.card:ℝ)*(Q.card:ℝ)*(S.card:ℝ)*D)) := by gcongr
    _ ≤ (2*B)*((U.card:ℝ)+Real.sqrt ((U.card:ℝ)*(Q.card:ℝ)*(S.card:ℝ)*D)) := by
      have hn : 0≤(U.card:ℝ) := Nat.cast_nonneg _
      nlinarith




noncomputable def otherEnd {V : Type*} (x : V) (e : Sym2 V) : V :=
  if h : x ∈ e then (Sym2.mem_iff_exists.mp h).choose else x

private lemma otherEnd_spec {V : Type*} (x : V) (e : Sym2 V) (hx : x ∈ e) : e=s(x,otherEnd x e) := by
  classical
  dsimp [otherEnd]
  rw [dif_pos hx]
  exact (Sym2.mem_iff_exists.mp hx).choose_spec

private lemma otherEnd_mem {V : Type*} (x : V) (e : Sym2 V) (hx : x ∈ e) : otherEnd x e ∈ e := by
  apply Sym2.mem_iff_exists.mpr
  exact ⟨x,(otherEnd_spec x e hx).trans Sym2.eq_swap⟩

private lemma incidence_sum {V : Type*} [Fintype V] (E : Finset (Sym2 V)) (W : Finset V)
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

private lemma incidence_boundary_bound {V : Type*} [Fintype V]
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

noncomputable def coreNeighbors {V : Type} [Fintype V] (H : SimpleGraph V)
    (R : Finset (Sym2 V)) (Vs : Finset V) (x : V) : Finset V :=
  Finset.univ.filter (fun z => s(x,z) ∈ coreEdges H R Vs)

private lemma core_mem_edgeSet {V : Type} [Fintype V] (H : SimpleGraph V) (R : Finset (Sym2 V))
    (Vs : Finset V) (e : Sym2 V) (he : e ∈ coreEdges H R Vs) : e ∈ H.edgeSet := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1).2

private lemma otherEnd_mk {V : Type*} (x z : V) : otherEnd x s(x,z)=z := by
  have h := otherEnd_spec x s(x,z) (by simp)
  rcases Sym2.eq_iff.mp h with ⟨_,h⟩ | ⟨h1,h2⟩
  · exact h.symm
  · exact h1.symm.trans h2.symm

private lemma coreDeg_eq_neighbors {V : Type} [Fintype V] (H : SimpleGraph V)
    (R : Finset (Sym2 V)) (Vs : Finset V) (x : V) :
    coreDeg H R Vs x=(coreNeighbors H R Vs x).card := by
  classical
  apply Finset.card_bij (fun e he => otherEnd x e)
  · intro e he
    obtain ⟨he,hxe⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rwa [← otherEnd_spec x e hxe]⟩
  · intro e he f hf heq
    have hxe := (Finset.mem_filter.mp he).2
    have hxf := (Finset.mem_filter.mp hf).2
    rw [otherEnd_spec x e hxe,otherEnd_spec x f hxf,heq]
  · intro z hz
    have hcore := (Finset.mem_filter.mp hz).2
    refine ⟨s(x,z),Finset.mem_filter.mpr ⟨hcore,by simp⟩,?_⟩
    exact otherEnd_mk x z

private lemma core_neighbor_adj {V : Type} [Fintype V] (H : SimpleGraph V) (R : Finset (Sym2 V))
    (Vs : Finset V) (x z : V) (hz : z ∈ coreNeighbors H R Vs x) : H.Adj x z := by
  exact core_mem_edgeSet H R Vs s(x,z) (Finset.mem_filter.mp hz).2

private lemma core_neighbor_rich {V : Type} [Fintype V] (H : SimpleGraph V) (R : Finset (Sym2 V))
    (Vs : Finset V) (x z : V) (hz : z ∈ coreNeighbors H R Vs x) : x ∈ Vs ∧ z ∈ Vs := by
  have he := (Finset.mem_filter.mp hz).2
  have hends := (Finset.mem_filter.mp he).2
  exact ⟨hends x (by simp),hends z (by simp)⟩

private lemma core_neighbor_symm {V : Type} [Fintype V] (H : SimpleGraph V) (R : Finset (Sym2 V))
    (Vs : Finset V) (x z : V) : z ∈ coreNeighbors H R Vs x ↔ x ∈ coreNeighbors H R Vs z := by
  classical
  simp only [coreNeighbors,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [Sym2.eq_swap]

private lemma core_degrees_sum {V : Type} [Fintype V] (H : SimpleGraph V)
    (R : Finset (Sym2 V)) (Vs : Finset V) :
    ∑ x ∈ Vs, (coreNeighbors H R Vs x).card = 2*(coreEdges H R Vs).card := by
  simp_rw [← coreDeg_eq_neighbors]
  exact incidence_sum (coreEdges H R Vs) Vs (fun e he => (Finset.mem_filter.mp he).2)
    (fun e he => H.not_isDiag_of_mem_edgeSet (core_mem_edgeSet H R Vs e he))



private lemma balanced_partition {α : Type*} [DecidableEq α] (W : Finset α) (k : ℕ)
    (hk : 0<k) (hkW : k ≤ W.card) :
    ∃ Bs : Finset (Finset α), Bs.biUnion id=W ∧
      (Bs:Set (Finset α)).PairwiseDisjoint id ∧
      ∀ B ∈ Bs, k ≤ B.card ∧ B.card<2*k := by
  classical
  revert hkW
  induction W using Finset.strongInductionOn
  rename_i W ih
  intro hkW
  by_cases hsmall : W.card<2*k
  · refine ⟨{W},by simp,by simp,?_⟩
    intro B hB
    have heq := Finset.mem_singleton.mp hB
    subst B
    exact ⟨hkW,hsmall⟩
  obtain ⟨A,hAW,hAk⟩ := Finset.exists_subset_card_eq hkW
  let U := W \ A
  have hcard : U.card+k=W.card := by simpa only [U,hAk] using Finset.card_sdiff_add_card_eq_card hAW
  have hUk : k ≤ U.card := by omega
  have hUW : U ⊂ W := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset,?_⟩
    intro heq
    have hc := congrArg Finset.card heq
    omega
  obtain ⟨Bs,hunion,hdis,hsize⟩ := ih U hUW hUk
  have hsub : ∀ B ∈ Bs, B ⊆ U := by
    intro B hB x hx
    rw [← hunion]
    exact Finset.mem_biUnion.mpr ⟨B,hB,hx⟩
  have hAB : ∀ B ∈ Bs, Disjoint A B := by
    intro B hB
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp (hsub B hB hxB)).2 hxA
  refine ⟨insert A Bs,?_,?_,?_⟩
  · rw [Finset.biUnion_insert,hunion]
    change A ∪ (W \ A)=W
    exact Finset.union_sdiff_of_subset hAW
  · intro X hX Y hY hXY
    simp only [Finset.mem_coe,Finset.mem_insert] at hX hY
    rcases hX with rfl | hX <;> rcases hY with rfl | hY
    · exact (hXY rfl).elim
    · exact hAB Y hY
    · exact (hAB X hX).symm
    · exact hdis hX hY hXY
  · intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact ⟨hAk.ge,by omega⟩
    · exact hsize B hB

private lemma balanced_bundles {α : Type*} [DecidableEq α] (W : Finset α) (k : ℕ)
    (hk : 0<k) (hkW : k ≤ W.card) :
    ∃ b : α → Finset α,
      (∀ z ∈ W, z ∈ b z ∧ b z ⊆ W ∧ k ≤ (b z).card ∧ (b z).card<2*k) ∧
      (∀ z ∈ W, ∀ y ∈ W, y ∈ b z ↔ z ∈ b y) := by
  classical
  obtain ⟨Bs,hunion,hdis,hsize⟩ := balanced_partition W k hk hkW
  have hex : ∀ z ∈ W, ∃ B ∈ Bs, z ∈ B := by
    intro z hz
    rw [← hunion] at hz
    exact Finset.mem_biUnion.mp hz
  let b : α → Finset α := fun z => if hz : z ∈ W then (hex z hz).choose else ∅
  have hprops (z : α) (hz : z ∈ W) : b z ∈ Bs ∧ z ∈ b z := by
    simpa only [b,dif_pos hz] using (hex z hz).choose_spec
  have hsubset : ∀ z ∈ W, b z ⊆ W := by
    intro z hz x hx
    rw [← hunion]
    exact Finset.mem_biUnion.mpr ⟨b z,(hprops z hz).1,hx⟩
  refine ⟨b,?_,?_⟩
  · intro z hz
    exact ⟨(hprops z hz).2,hsubset z hz,(hsize (b z) (hprops z hz).1).1,(hsize (b z) (hprops z hz).1).2⟩
  · intro z hz y hy
    have hsame : y ∈ b z → b z=b y := by
      intro hyz
      by_contra hne
      have hd := hdis (hprops z hz).1 (hprops y hy).1 hne
      exact Finset.disjoint_left.mp hd hyz (hprops y hy).2
    have hsame' : z ∈ b y → b y=b z := by
      intro hzy
      by_contra hne
      have hd := hdis (hprops y hy).1 (hprops z hz).1 hne
      exact Finset.disjoint_left.mp hd hzy (hprops z hz).2
    constructor
    · intro h
      rw [← hsame h]
      exact (hprops z hz).2
    · intro h
      rw [← hsame' h]
      exact (hprops y hy).2



private lemma diamLE_of_pairwise {V : Type} [Fintype V] (H : SimpleGraph V) (S : Finset V)
    (D : ℝ) (hD : 0 ≤ D)
    (hp : ∀ x ∈ S, ∀ y ∈ S, ∃ k : ℕ, H.edist x y = (k : ℕ∞) ∧ (k : ℝ) ≤ D) :
    DiamLE H S D := by
  have hbound : diam H S ≤ (⌊D⌋₊ : ℕ∞) := by
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    obtain ⟨k,hk,hkD⟩ := hp x hx y hy
    rw [hk]
    exact_mod_cast (Nat.le_floor hkD)
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hbound,?_⟩
  have hnat := ENat.toNat_le_of_le_natCast hbound
  exact (show ((diam H S).toNat : ℝ) ≤ (⌊D⌋₊ : ℝ) by exact_mod_cast hnat).trans (Nat.floor_le hD)

private lemma ball_pairwise {V : Type} [Fintype V] (H : SimpleGraph V) (c x y : V) (a : ℝ)
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

private lemma diamLE_of_subset_ball {V : Type} [Fintype V] (H : SimpleGraph V)
    (S : Finset V) (c : V) (a : ℝ) (ha : 0 ≤ a) (hS : S ⊆ ball H c a) :
    DiamLE H S (2*a) := by
  apply diamLE_of_pairwise H S (2*a) (by positivity)
  intro x hx y hy
  exact ball_pairwise H c x y a (hS hx) (hS hy)



private lemma ball_mono {V : Type} [Fintype V] (H : SimpleGraph V) (x : V) (a b : ℝ) (hab : a≤b) :
    ball H x a ⊆ ball H x b := by
  intro v hv
  obtain ⟨k,hk,hka⟩ := (Finset.mem_filter.mp hv).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,hk,hka.trans hab⟩

private lemma ball_adj {V : Type} [Fintype V] (H : SimpleGraph V) (x y : V) (hxy : H.Adj x y)
    (a : ℝ) : ball H x a ⊆ ball H y (a+1) := by
  intro v hv
  obtain ⟨k,hk,hka⟩ := (Finset.mem_filter.mp hv).2
  have hdist : H.edist y v ≤ ((k+1:ℕ):ℕ∞) := by
    calc
      _ ≤ H.edist y x+H.edist x v := SimpleGraph.edist_triangle
      _ = _ := by rw [SimpleGraph.edist_eq_one_iff_adj.mpr hxy.symm,hk]; simp [add_comm]
  obtain ⟨j,hj,hjk⟩ := ENat.le_natCast_iff.mp hdist
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj,?_⟩
  have hreal : (j:ℝ) ≤ (k:ℝ)+1 := by exact_mod_cast hjk
  linarith

private lemma edge_ball_ends {V : Type} [Fintype V] (H : SimpleGraph V) (e : Sym2 V)
    (he : e ∈ H.edgeSet) (x : V) (a : ℝ) (hne : ∃ v ∈ e, v ∈ ball H x a) :
    ∀ z ∈ e, z ∈ ball H x (a+1) := by
  obtain ⟨v,hve,hvball⟩ := hne
  intro z hze
  by_cases hz : z=v
  · subst z
    exact ball_mono H x a (a+1) (by linarith) hvball
  have hrep : e=s(v,z) := Sym2.mem_and_mem_iff (Ne.symm hz) |>.mp ⟨hve,hze⟩
  have hvz : H.Adj v z := by rwa [hrep] at he
  obtain ⟨k,hk,hka⟩ := (Finset.mem_filter.mp hvball).2
  have hdist : H.edist x z ≤ ((k+1:ℕ):ℕ∞) := by
    calc
      _ ≤ H.edist x v+H.edist v z := SimpleGraph.edist_triangle
      _ = _ := by rw [hk,SimpleGraph.edist_eq_one_iff_adj.mpr hvz]; simp
  obtain ⟨j,hj,hjk⟩ := ENat.le_natCast_iff.mp hdist
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj,?_⟩
  have hreal : (j:ℝ) ≤ (k:ℝ)+1 := by exact_mod_cast hjk
  linarith

private lemma charged_ends {V : Type} [Fintype V] (H : SimpleGraph V) (R : Finset (Sym2 V))
    (Vs : Finset V) (x y : V) (hxy : H.Adj x y) (r : ℝ)
    (f : Sym2 V) (D : Finset (Sym2 V)) (hf : f ∈ lamStarSet H R Vs x (r/2) D) :
    ∀ z ∈ f, z ∈ ball H y (r/2+2) := by
  obtain ⟨hcore,hnear,hlabel⟩ := Finset.mem_filter.mp hf
  have hedge : f ∈ H.edgeSet := (Finset.mem_filter.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hcore).1).1).2
  intro z hz
  have hxball := edge_ball_ends H f hedge x (r/2) hnear z hz
  have hyball := ball_adj H x y hxy (r/2+1) hxball
  simpa only [add_assoc,show (1:ℝ)+1=2 by norm_num] using hyball

private lemma comparison_ball_subset {V : Type} [Fintype V] (H : SimpleGraph V)
    (x y : V) (hxy : H.Adj x y) (r : ℝ) (hr : 6≤r) :
    ball H y (r/2+2) ⊆ ball H x r := by
  exact (ball_adj H y x hxy.symm (r/2+2)).trans (ball_mono H x _ _ (by linarith))



private lemma sum_indicator_subset {α : Type*} [DecidableEq α] (S T : Finset α) (a : ℝ) (hT : T ⊆ S) :
    (∑ x ∈ S, if x ∈ T then a else 0) = (T.card:ℝ)*a := by
  classical
  rw [← Finset.sum_filter]
  have heq : S.filter (fun x => x ∈ T)=T := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hx => ⟨hT hx,hx⟩⟩
  rw [heq]
  simp

private lemma sum_rectangle {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S B : Finset α) (T L : Finset β) (a : ℝ) (hB : B ⊆ S) (hL : L ⊆ T) :
    (∑ x ∈ S, ∑ y ∈ T, if x ∈ B ∧ y ∈ L then a else 0) =
      (B.card:ℝ)*(L.card:ℝ)*a := by
  classical
  have hinner : ∀ x, (∑ y ∈ T, if x ∈ B ∧ y ∈ L then a else 0) =
      if x ∈ B then (L.card:ℝ)*a else 0 := by
    intro x
    by_cases hx : x ∈ B
    · simp only [hx,true_and,ite_true]
      exact sum_indicator_subset T L a hL
    · simp [hx]
  simp_rw [hinner]
  rw [sum_indicator_subset S B _ hB]
  ring

private lemma sparse_weighted_charge {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (E J : Finset β) (charge : α → β → Prop) (w : α → ℝ) (k : ℕ) (u : ℝ)
    (hu : 0<u) (hcount : ∀ f ∈ E, (I.filter (fun a => charge a f)).card ≤ k)
    (hweight : ∀ a ∈ I, ∀ f ∈ E, charge a f → w a ≤ 1/u)
    (hsupport : ∀ a ∈ I, ∀ f ∈ E, charge a f → f ∈ J) :
    (∑ a ∈ I, ∑ f ∈ E, if charge a f then w a else 0) ≤ (k:ℝ)*(J.card:ℝ)/u := by
  classical
  rw [Finset.sum_comm]
  have hinner : ∀ f ∈ E, (∑ a ∈ I, if charge a f then w a else 0) ≤
      if f ∈ J then (k:ℝ)/u else 0 := by
    intro f hf
    by_cases hJ : f ∈ J
    · rw [if_pos hJ,← Finset.sum_filter]
      calc
        _ ≤ ∑ _a ∈ I.filter (fun a => charge a f), 1/u := Finset.sum_le_sum (fun a ha =>
          hweight a (Finset.mem_filter.mp ha).1 f hf (Finset.mem_filter.mp ha).2)
        _ = ((I.filter (fun a => charge a f)).card:ℝ)*(1/u) := by simp
        _ ≤ (k:ℝ)*(1/u) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount f hf) (by positivity)
        _ = _ := by ring
    · have hfalse : ∀ a ∈ I, ¬charge a f := fun a ha hc => hJ (hsupport a ha f hf hc)
      simp only [if_neg hJ]
      apply le_of_eq
      exact Finset.sum_eq_zero (fun a ha => by rw [if_neg (hfalse a ha)])
  calc
    _ ≤ ∑ f ∈ E, if f ∈ J then (k:ℝ)/u else 0 := Finset.sum_le_sum hinner
    _ = ((E.filter (fun f => f ∈ J)).card:ℝ)*((k:ℝ)/u) := by rw [← Finset.sum_filter]; simp
    _ ≤ (J.card:ℝ)*((k:ℝ)/u) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card (show E.filter (fun f => f ∈ J) ⊆ J from
        fun f hf => (Finset.mem_filter.mp hf).2)
    _ = _ := by ring


private lemma local_conflict_numeric (B u d r y m : ℝ) (hB : 0≤B) (hu : 0<u) (hd : 0<d)
    (hr : 0<r) (hy : 0≤y) (hvolume : d*r/480 ≤ u)
    (hm : m ≤ B*(u+Real.sqrt (u*(2*d*y)*y*2))) :
    6*m/u ≤ 6*B*(1+60*y/Real.sqrt r) := by
  have hs : 0<Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsr : Real.sqrt r^2=r := Real.sq_sqrt hr.le
  have hprod : (Real.sqrt (d*u)*Real.sqrt r)^2 ≤ (30*u)^2 := by
    calc
      _ = (d*u)*r := by rw [mul_pow,Real.sq_sqrt (by positivity),hsr]
      _ ≤ 480*u^2 := by
        have h := mul_le_mul_of_nonneg_left hvolume hu.le
        nlinarith
      _ ≤ _ := by nlinarith [sq_nonneg u]
  have hlow : 0≤Real.sqrt (d*u)*Real.sqrt r := by positivity
  have hsu : Real.sqrt (d*u)*Real.sqrt r ≤ 30*u := by nlinarith
  have hsu' : Real.sqrt (d*u) ≤ 30*u/Real.sqrt r := (le_div_iff₀ hs).mpr hsu
  have hid : Real.sqrt (u*(2*d*y)*y*2)=2*y*Real.sqrt (d*u) := by
    have heq : u*(2*d*y)*y*2=(2*y)^2*(d*u) := by ring
    rw [heq,Real.sqrt_mul (by positivity),Real.sqrt_sq (by positivity)]
  have hm' : m ≤ B*(u+2*y*(30*u/Real.sqrt r)) := by
    rw [hid] at hm
    exact hm.trans (by gcongr)
  calc
    6*m/u ≤ 6*(B*(u+2*y*(30*u/Real.sqrt r)))/u := by gcongr
    _ = 6*B*(1+60*y/Real.sqrt r) := by field_simp; ring

private lemma essential_mem {V : Type} [Fintype V] (K K' : SimpleGraph V)
    (R : Finset (Sym2 V)) (hR : IsDemandSet K R) (hK' : IsPreserver K K' R)
    (q e : Sym2 V) (hq : q ∈ R) (he : IsEssential K q e) : e ∈ K'.edgeSet := by
  induction q using Sym2.ind with
  | _ s t =>
    have hr : K'.Reachable s t := SimpleGraph.edist_ne_top_iff_reachable.mp (by
      rw [hK'.2 s t hq]; exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hR s t hq).2)
    obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_edist
    have hw' : IsShortest (w.mapLe hK'.1) := by
      simpa [IsShortest, hK'.2 s t hq] using hw
    have hm := he s t rfl (w.mapLe hK'.1) hw'
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hm
    exact w.edges_subset_edgeSet hm


private lemma vol_pos {V : Type} [Fintype V] (H : SimpleGraph V) (x : V) (r : ℝ) (hr : 0≤r) :
    0<vol H x r := by
  apply Finset.card_pos.mpr
  exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,0,by simp,by simpa only [Nat.cast_zero] using hr⟩⟩

theorem solution : ∃ C₀ : ℝ, 0<C₀ ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V)) (n : ℕ) (d l r : ℝ)
      (Vs : Finset V),
      Sec5Context G H R n d l → Eq5 d l r → Eq6 H R Vs n d →
      conflictSum H R Vs r ≤ C₀*((coreEdges H R Vs).card:ℝ)/(d*Real.sqrt r) := by
  obtain ⟨B,hB,hlocal⟩ := local_covered_estimate
  refine ⟨40000*B,by positivity,?_⟩
  intro V inst G H R n d l r Vs hctx h5 h6
  classical
  have hv : 0<Fintype.card V := (Finset.card_pos.mpr h6.1).trans_le (Finset.card_le_univ _)
  have hn : 0<(n:ℝ) := by exact_mod_cast hv.trans_le hctx.2.2.1
  have hnd : 0≤(n:ℝ)*d := (Nat.cast_nonneg (numEdges H)).trans hctx.2.2.2.1
  have hd : 0<d := by have := h5.1; have := (le_min_iff.mp h5.2).1; nlinarith
  have hr : 0<r := lt_of_lt_of_le (by norm_num : (0:ℝ)<6) h5.1
  have hd2 : 2≤d := by have := h5.1; have := (le_min_iff.mp h5.2).1; nlinarith
  let E := coreEdges H R Vs
  let nb : V → Finset V := coreNeighbors H R Vs
  let dy : V → ℝ := fun y => (nb y).card
  let U : V → Finset V := fun y => ball H y (r/2+2)
  let uy : V → ℝ := fun y => (U y).card
  let k : ℕ := ⌈d/40⌉₊
  have hk : 0<k := by
    have h : 1≤⌈d/40⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
    exact h
  have hkd : (k:ℝ) ≤ d := by
    have hceil := Nat.ceil_lt_add_one (show 0≤d/40 by positivity)
    change (⌈d/40⌉₊:ℝ) ≤ d
    nlinarith
  have hklo : d/40 ≤ (k:ℝ) := Nat.le_ceil _
  have hkNB : ∀ x ∈ Vs, k ≤ (nb x).card := by
    intro x hx
    apply Nat.ceil_le.mpr
    change d/40 ≤ ((coreNeighbors H R Vs x).card:ℝ)
    rw [← coreDeg_eq_neighbors]
    exact h6.2.2 x hx
  let bun : V → V → Finset V := fun x => if hx : x ∈ Vs then
    (balanced_bundles (nb x) k hk (hkNB x hx)).choose else fun _ => ∅
  have hbun (x : V) (hx : x ∈ Vs) :
      (∀ z ∈ nb x, z ∈ bun x z ∧ bun x z ⊆ nb x ∧ k ≤ (bun x z).card ∧ (bun x z).card<2*k) ∧
      (∀ z ∈ nb x, ∀ y ∈ nb x, y ∈ bun x z ↔ z ∈ bun x y) := by
    simpa only [bun,dif_pos hx] using (balanced_bundles (nb x) k hk (hkNB x hx)).choose_spec
  obtain ⟨x₀,hx₀⟩ := h6.1
  let lab : Sym2 V → Sym2 V := fun e => if h : (essSet H R e).card=1 then
    (Finset.card_eq_one.mp h).choose else s(x₀,x₀)
  have hlabel : ∀ e ∈ E, essSet H R e={lab e} := by
    intro e he
    have hpriv := (Finset.mem_filter.mp he).1
    have hcard := (Finset.mem_filter.mp hpriv).2
    dsimp [lab]
    rw [dif_pos hcard]
    exact (Finset.card_eq_one.mp hcard).choose_spec
  have hlabR : ∀ e ∈ E, lab e ∈ R := by
    intro e he
    have hm : lab e ∈ essSet H R e := by rw [hlabel e he]; simp
    exact (Finset.mem_filter.mp hm).1
  have hlabess : ∀ e ∈ E, IsEssential H (lab e) e := by
    intro e he
    have hm : lab e ∈ essSet H R e := by rw [hlabel e he]; simp
    exact (Finset.mem_filter.mp hm).2
  have hRH : IsDemandSet H R := by
    intro s t hst
    refine ⟨(hctx.1 s t hst).1,?_⟩
    apply SimpleGraph.edist_ne_top_iff_reachable.mp
    rw [hctx.2.1.1.2 s t hst]
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hctx.1 s t hst).2
  let Q : V → Finset (Sym2 V) := fun y => (nb y).biUnion
    (fun x => (bun x y).image (fun z => lab s(x,z)))
  have hQR : ∀ y : V, Q y ⊆ R := by
    intro y q hq
    obtain ⟨x,hx,hqimage⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hqimage
    have hxrich := (core_neighbor_rich H R Vs y x hx).2
    have hyNB := (core_neighbor_symm H R Vs y x).mp hx
    have hzNB := (hbun x hxrich).1 y hyNB |>.2.1 hz
    exact hlabR s(x,z) (Finset.mem_filter.mp hzNB).2
  have hQcover : ∀ y : V, Covers H (nb y) (Q y) := by
    intro y q hq
    obtain ⟨x,hx,hqimage⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hqimage
    have hxrich := (core_neighbor_rich H R Vs y x hx).2
    have hyNB := (core_neighbor_symm H R Vs y x).mp hx
    have hzNB := (hbun x hxrich).1 y hyNB |>.2.1 hz
    have he : s(x,z) ∈ E := (Finset.mem_filter.mp hzNB).2
    exact ⟨x,hx,s(x,z),core_mem_edgeSet H R Vs _ he,by simp,hlabess _ he⟩
  have hQcard : ∀ y : V, (Q y).card ≤ 2*k*(nb y).card := by
    intro y
    calc
      (Q y).card ≤ ∑ x ∈ nb y, ((bun x y).image (fun z => lab s(x,z))).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ nb y, 2*k := Finset.sum_le_sum (fun x hx => by
        have hxrich := (core_neighbor_rich H R Vs y x hx).2
        have hyNB := (core_neighbor_symm H R Vs y x).mp hx
        exact Finset.card_image_le.trans ((hbun x hxrich).1 y hyNB).2.2.2.le)
      _ = _ := by simp [mul_comm]
  have hnbpos : ∀ y ∈ Vs, (nb y).Nonempty := by
    intro y hy
    exact Finset.card_pos.mp (hk.trans_le (hkNB y hy))
  have hnbball : ∀ y : V, nb y ⊆ ball H y 1 := by
    intro y x hx
    have hxy := core_neighbor_adj H R Vs y x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,1,SimpleGraph.edist_eq_one_iff_adj.mpr hxy,by norm_num⟩
  have hnbdiam : ∀ y : V, DiamLE H (nb y) 2 := by
    intro y
    simpa using diamLE_of_subset_ball H (nb y) y 1 (by norm_num) (hnbball y)
  have hJex : ∀ y ∈ Vs, ∃ J : SimpleGraph V, IsPreserver H J (Q y) ∧
      ((inducedEdges J (U y)).card:ℝ) ≤ B*(uy y+Real.sqrt (uy y*((Q y).card:ℝ)*dy y*2)) := by
    intro y hy
    exact hlocal V H (Q y) (nb y) (U y) 2 (fun s t hst => hRH s t (hQR y hst))
      (hnbpos y hy) (hQcover y) (hnbdiam y)
  let J : V → SimpleGraph V := fun y => if hy : y ∈ Vs then (hJex y hy).choose else ⊥
  have hJ (y : V) (hy : y ∈ Vs) : IsPreserver H (J y) (Q y) ∧
      ((inducedEdges (J y) (U y)).card:ℝ) ≤ B*(uy y+Real.sqrt (uy y*((Q y).card:ℝ)*dy y*2)) := by
    simpa only [J,dif_pos hy] using (hJex y hy).choose_spec
  have huy : ∀ y : V, 0<uy y := by
    intro y
    change 0<((ball H y (r/2+2)).card:ℝ)
    exact_mod_cast vol_pos H y (r/2+2) (by positivity)
  have hvolume : ∀ y ∈ Vs, d*r/480 ≤ uy y := by
    intro y hy
    have hl1 : 1≤l := le_trans (by linarith [h5.1] : 1≤r) (le_min_iff.mp h5.2).2
    have hg := (DistancePreserver934.Exact.lemma_14 G H R l Vs hctx.1 hctx.2.1 hctx.2.2.2.2 hl1).2
      d hd h6.2.2 y hy (r/2+2) (by linarith [h5.1])
    have hmin : r/2 ≤ min (r/2+2) l := le_min (by linarith) (by have := (le_min_iff.mp h5.2).2; linarith)
    have hm := mul_le_mul_of_nonneg_left hmin (by positivity : 0≤d/240)
    change d/240*min (r/2+2) l ≤ uy y at hg
    nlinarith
  have hJnum : ∀ y ∈ Vs,
      6*((inducedEdges (J y) (U y)).card:ℝ)/uy y ≤ 6*B*(1+60*dy y/Real.sqrt r) := by
    intro y hy
    have hqcard : ((Q y).card:ℝ) ≤ 2*d*dy y := by
      have hc : ((Q y).card:ℝ) ≤ 2*(k:ℝ)*dy y := by
        change ((Q y).card:ℝ) ≤ 2*(k:ℝ)*((nb y).card:ℝ)
        exact_mod_cast hQcard y
      exact hc.trans (mul_le_mul_of_nonneg_right (by linarith) (by dsimp [dy]; positivity))
    have hsize : ((inducedEdges (J y) (U y)).card:ℝ) ≤
        B*(uy y+Real.sqrt (uy y*(2*d*dy y)*dy y*2)) := by
      exact (hJ y hy).2.trans (by gcongr)
    exact local_conflict_numeric B (uy y) d r (dy y) ((inducedEdges (J y) (U y)).card:ℝ)
      hB.le (huy y) hd hr (by dsimp [dy]; positivity) (hvolume y hy) hsize
  let Inc := Vs.product E
  let charge : (V × Sym2 V) → V → Sym2 V → Prop := fun a y f =>
    a.1 ∈ a.2 ∧ y ∈ bun a.1 (otherEnd a.1 a.2) ∧
      f ∈ lamStarSet H R Vs a.1 (r/2) (essSet H R a.2)
  let weight : (V × Sym2 V) → ℝ := fun a => 1/(vol H a.1 r:ℝ)
  let T : ℝ := ∑ a ∈ Inc, ∑ y ∈ Vs, ∑ f ∈ E, if charge a y f then weight a else 0
  have hother : ∀ x ∈ Vs, ∀ e ∈ E, x ∈ e → otherEnd x e ∈ nb x := by
    intro x hx e he hxe
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rwa [← otherEnd_spec x e hxe]⟩
  have hchargeAdj : ∀ a ∈ Inc, ∀ y f, charge a y f → H.Adj a.1 y := by
    intro a ha y f hc
    obtain ⟨hx,he⟩ := Finset.mem_product.mp ha
    obtain ⟨hxe,hy,hf⟩ := hc
    have hzNB := hother a.1 hx a.2 he hxe
    have hyNB := ((hbun a.1 hx).1 (otherEnd a.1 a.2) hzNB).2.1 hy
    exact core_neighbor_adj H R Vs a.1 y hyNB
  have hchargeQ : ∀ a ∈ Inc, ∀ y f, charge a y f → lab a.2 ∈ Q y := by
    intro a ha y f hc
    obtain ⟨hx,he⟩ := Finset.mem_product.mp ha
    obtain ⟨hxe,hy,hf⟩ := hc
    have hzNB := hother a.1 hx a.2 he hxe
    have hyNB := ((hbun a.1 hx).1 (otherEnd a.1 a.2) hzNB).2.1 hy
    have hxNB := (core_neighbor_symm H R Vs a.1 y).mp hyNB
    have hzy := ((hbun a.1 hx).2 (otherEnd a.1 a.2) hzNB y hyNB).mp hy
    apply Finset.mem_biUnion.mpr
    refine ⟨a.1,hxNB,Finset.mem_image.mpr ⟨otherEnd a.1 a.2,hzy,?_⟩⟩
    rw [← otherEnd_spec a.1 a.2 hxe]
  have hchargeSupport : ∀ y ∈ Vs, ∀ a ∈ Inc, ∀ f ∈ E, charge a y f →
      f ∈ inducedEdges (J y) (U y) := by
    intro y hy a ha f hf hc
    have hadj := hchargeAdj a ha y f hc
    obtain ⟨hx,he⟩ := Finset.mem_product.mp ha
    obtain ⟨hxe,hybun,hfLam⟩ := hc
    have hsets := (Finset.mem_filter.mp hfLam).2.2
    have hqf : lab a.2 ∈ essSet H R f := by rw [hsets,hlabel a.2 he]; simp
    have hessf := (Finset.mem_filter.mp hqf).2
    have hqQ := hchargeQ a ha y f ⟨hxe,hybun,hfLam⟩
    have hfeJ := essential_mem H (J y) (Q y) (fun s t hst => hRH s t (hQR y hst))
      (hJ y hy).1 (lab a.2) f hqQ hessf
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfeJ⟩,
      charged_ends H R Vs a.1 y hadj r f (essSet H R a.2) hfLam⟩
  have hchargeCount : ∀ y ∈ Vs, ∀ f ∈ E,
      (Inc.filter (fun a => charge a y f)).card ≤ 6 := by
    intro y hy f hf
    have hsub : Inc.filter (fun a => charge a y f) ⊆
        (Finset.univ : Finset (V × Sym2 V)).filter (fun a =>
          a.2 ∈ H.edgeSet ∧ IsEssential H (lab f) a.2 ∧ a.1 ∈ a.2 ∧ H.Adj y a.1) := by
      intro a ha
      obtain ⟨ha,hc⟩ := Finset.mem_filter.mp ha
      obtain ⟨hx,he⟩ := Finset.mem_product.mp ha
      obtain ⟨hxe,hybun,hfLam⟩ := hc
      have hsets := (Finset.mem_filter.mp hfLam).2.2
      have heq : lab a.2=lab f := Finset.singleton_injective
        ((hlabel a.2 he).symm.trans (hsets.symm.trans (hlabel f hf)))
      have hess : IsEssential H (lab f) a.2 := by simpa only [heq] using hlabess a.2 he
      have hadj := (hchargeAdj a ha y f ⟨hxe,hybun,hfLam⟩).symm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,core_mem_edgeSet H R Vs _ he,hess,hxe,hadj⟩
    exact (Finset.card_le_card hsub).trans
      ((DistancePreserver934.Exact.lemma_12 G H R hctx.1 hctx.2.1 (lab f) (hlabR f hf)).2.2.1 y)
  have hchargeWeight : ∀ y ∈ Vs, ∀ a ∈ Inc, ∀ f ∈ E, charge a y f → weight a ≤ 1/uy y := by
    intro y hy a ha f hf hc
    have hadj := hchargeAdj a ha y f hc
    have hsub := comparison_ball_subset H a.1 y hadj r h5.1
    have hvolcomp : uy y ≤ (vol H a.1 r:ℝ) := by
      change ((ball H y (r/2+2)).card:ℝ) ≤ ((ball H a.1 r).card:ℝ)
      exact_mod_cast Finset.card_le_card hsub
    exact one_div_le_one_div_of_le (huy y) hvolcomp
  have hTy : ∀ y ∈ Vs,
      (∑ a ∈ Inc, ∑ f ∈ E, if charge a y f then weight a else 0) ≤
        6*((inducedEdges (J y) (U y)).card:ℝ)/uy y := by
    intro y hy
    convert sparse_weighted_charge Inc E (inducedEdges (J y) (U y)) (fun a f => charge a y f)
      weight 6 (uy y) (huy y) (fun f hf => by
        convert hchargeCount y hy f hf using 1
        congr 1
        ext a
        simp only [Finset.mem_filter]) (hchargeWeight y hy) (hchargeSupport y hy) using 1
    · apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro f hf
      split_ifs <;> rfl
    · norm_num
  have hrow : ∀ a ∈ Inc,
      (d/40)*(if a.1 ∈ a.2 then (lamStar H R Vs a.1 (r/2) (essSet H R a.2):ℝ)/(vol H a.1 r:ℝ) else 0) ≤
        ∑ y ∈ Vs, ∑ f ∈ E, if charge a y f then weight a else 0 := by
    intro a ha
    obtain ⟨hx,he⟩ := Finset.mem_product.mp ha
    by_cases hxe : a.1 ∈ a.2
    swap
    · simp [charge,hxe]
    have hzNB := hother a.1 hx a.2 he hxe
    have hprops := (hbun a.1 hx).1 (otherEnd a.1 a.2) hzNB
    have hBsub : bun a.1 (otherEnd a.1 a.2) ⊆ Vs := by
      intro y hy
      exact (core_neighbor_rich H R Vs a.1 y (hprops.2.1 hy)).2
    let Lset := lamStarSet H R Vs a.1 (r/2) (essSet H R a.2)
    have hLsub : Lset ⊆ E := fun f hf => (Finset.mem_filter.mp hf).1
    have hrect := sum_rectangle Vs (bun a.1 (otherEnd a.1 a.2)) E Lset (weight a) hBsub hLsub
    have hrowEq : (∑ y ∈ Vs, ∑ f ∈ E, if charge a y f then weight a else 0) =
        ((bun a.1 (otherEnd a.1 a.2)).card:ℝ)*(lamStar H R Vs a.1 (r/2) (essSet H R a.2):ℝ)/(vol H a.1 r:ℝ) := by
      simpa only [charge,hxe,true_and,weight,lamStar,Lset,div_eq_mul_inv,one_mul,mul_assoc] using hrect
    have hBcard : d/40 ≤ ((bun a.1 (otherEnd a.1 a.2)).card:ℝ) :=
      hklo.trans (by exact_mod_cast hprops.2.2.1)
    rw [if_pos hxe,hrowEq]
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hBcard
      (show 0≤(lamStar H R Vs a.1 (r/2) (essSet H R a.2):ℝ)/(vol H a.1 r:ℝ) by positivity)
  have hZeq : (d/40)*conflictSum H R Vs r =
      ∑ a ∈ Inc, (d/40)*(if a.1 ∈ a.2 then
        (lamStar H R Vs a.1 (r/2) (essSet H R a.2):ℝ)/(vol H a.1 r:ℝ) else 0) := by
    simp only [Inc,conflictSum,Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero,E]
    rw [show Vs.product (coreEdges H R Vs) = Vs ×ˢ (coreEdges H R Vs) from rfl]
    rw [Finset.sum_product]
  have hTlower : (d/40)*conflictSum H R Vs r ≤ T := by
    rw [hZeq]
    exact Finset.sum_le_sum hrow
  have hTupper : T ≤ ∑ y ∈ Vs, 6*B*(1+60*dy y/Real.sqrt r) := by
    change (∑ a ∈ Inc, ∑ y ∈ Vs, ∑ f ∈ E, if charge a y f then weight a else 0) ≤ _
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun y hy => (hTy y hy).trans (hJnum y hy))
  have hdySum : ∑ y ∈ Vs, dy y = 2*(E.card:ℝ) := by
    change (∑ y ∈ Vs, ((coreNeighbors H R Vs y).card:ℝ)) = 2*((coreEdges H R Vs).card:ℝ)
    exact_mod_cast core_degrees_sum H R Vs
  have hsumNumeric : (∑ y ∈ Vs, 6*B*(1+60*dy y/Real.sqrt r)) =
      6*B*((Vs.card:ℝ)+120*(E.card:ℝ)/Real.sqrt r) := by
    rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,
      ← Finset.sum_div,← Finset.mul_sum,hdySum]
    simp only [nsmul_eq_mul,mul_one]
    ring
  have hs : 0<Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsd : Real.sqrt r ≤ d := by
    have hrD := (le_min_iff.mp h5.2).1
    nlinarith [Real.sq_sqrt hr.le,Real.sqrt_nonneg r]
  have hmass : (n:ℝ)*d/40 ≤ (E.card:ℝ) := h6.2.1
  have hVsN : (Vs.card:ℝ) ≤ n := by exact_mod_cast (Finset.card_le_univ Vs).trans hctx.2.2.1
  have hNnorm : (Vs.card:ℝ) ≤ 40*(E.card:ℝ)/Real.sqrt r := by
    apply hVsN.trans
    apply (le_div_iff₀ hs).mpr
    have hnss := mul_le_mul_of_nonneg_left hsd (Nat.cast_nonneg n)
    nlinarith
  have hTupper' : T ≤ 960*B*(E.card:ℝ)/Real.sqrt r := by
    calc
      T ≤ ∑ y ∈ Vs, 6*B*(1+60*dy y/Real.sqrt r) := hTupper
      _ = 6*B*((Vs.card:ℝ)+120*(E.card:ℝ)/Real.sqrt r) := hsumNumeric
      _ ≤ 6*B*((40*(E.card:ℝ)/Real.sqrt r)+120*(E.card:ℝ)/Real.sqrt r) := by gcongr
      _ = _ := by ring
  have hclear := (le_div_iff₀ hs).mp (hTlower.trans hTupper')
  apply (le_div_iff₀ (mul_pos hd hs)).mpr
  have hBm : 0≤B*(E.card:ℝ) := mul_nonneg hB.le (Nat.cast_nonneg _)
  nlinarith
