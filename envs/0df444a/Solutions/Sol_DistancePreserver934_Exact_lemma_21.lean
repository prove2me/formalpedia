-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_21
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:40:05.72667+00:00
-- url     : https://prove2.me/submissions/71ae7bf0-9fb5-4dac-98ce-e49190a6f7b7

import Theorems.Thm_DistancePreserver934_Exact_lemma_4
import Definitions.Def_DistancePreserver934_Exact_Essential

set_option autoImplicit false
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

private lemma minimal_essential {V : Type} [Fintype V] (K : SimpleGraph V)
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

private lemma removed_bound {V : Type} [Fintype V] (K : SimpleGraph V)
    (R Q : Finset (Sym2 V)) (hR : IsDemandSet K R) (hK : IsMinimalPreserver K K R)
    (hQR : Q ⊆ R) (HQ : SimpleGraph V) (hHQ : IsPreserver K HQ Q)
    (K' : SimpleGraph V) (hK' : IsPreserver K K' (R \ Q)) :
    (numEdges K : ℝ)-(numEdges K' : ℝ) ≤ (numEdges HQ : ℝ) := by
  classical
  have hsub : edgesF K' ⊆ edgesF K := by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,SimpleGraph.edgeSet_mono hK'.1 (Finset.mem_filter.mp he).2⟩
  have hdiff : edgesF K \ edgesF K' ⊆ edgesF HQ := by
    intro e he
    obtain ⟨heK,heK'⟩ := Finset.mem_sdiff.mp he
    have heK0 : e ∈ K.edgeSet := (Finset.mem_filter.mp heK).2
    obtain ⟨q,hq⟩ := minimal_essential K R hR hK e heK0
    obtain ⟨hqR,hess⟩ := Finset.mem_filter.mp hq
    by_cases hqQ : q ∈ Q
    · have hm := essential_mem K HQ Q (fun a b hab => hR a b (hQR hab)) hHQ q e hqQ hess
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩
    · have hm := essential_mem K K' (R \ Q) (fun a b hab => hR a b (Finset.mem_sdiff.mp hab).1)
        hK' q e (Finset.mem_sdiff.mpr ⟨hqR,hqQ⟩) hess
      exact (heK' (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩)).elim
  have hc := Finset.card_le_card hdiff
  have hd := Finset.card_sdiff_add_card_eq_card hsub
  have hc' : ((edgesF K \ edgesF K').card : ℝ) ≤ (numEdges HQ : ℝ) := by exact_mod_cast hc
  have hd' : ((edgesF K \ edgesF K').card : ℝ)+(numEdges K' : ℝ) = (numEdges K : ℝ) := by exact_mod_cast hd
  linarith

theorem solution : ∃ A : ℝ, 0 < A ∧
    ∀ (V : Type) [Fintype V] (K : SimpleGraph V) (R : Finset (Sym2 V)) (n : ℕ)
      (S : Finset V) (Q : Finset (Sym2 V)),
      IsDemandSet K R → IsMinimalPreserver K K R → Fintype.card V ≤ n →
      S.Nonempty → Q.Nonempty → Q ⊆ R → Covers K S Q → diam K S ≠ ⊤ →
      ∃ HQ : SimpleGraph V, IsPreserver K HQ Q ∧
        (∀ K' : SimpleGraph V, IsPreserver K K' (R \ Q) →
          (numEdges K : ℝ)-(numEdges K' : ℝ) ≤ (numEdges HQ : ℝ)) ∧
        (numEdges HQ : ℝ) ≤ A*((n : ℝ)+
          Real.sqrt ((n : ℝ)*(Q.card : ℝ)*(S.card : ℝ)*((diam K S).toNat : ℝ))) := by
  obtain ⟨B,hB,h4⟩ := DistancePreserver934.Exact.lemma_4
  refine ⟨2*B,by positivity,?_⟩
  intro V inst K R n S Q hR hK hV hS hQ hQR hcov hdiam
  classical
  have hQset : IsDemandSet K Q := fun a b hab => hR a b (hQR hab)
  obtain ⟨T,hT,hcard,hsource,hpres⟩ := covered_split K S Q hQset hS hcov
  obtain ⟨HQ,hHQsub,hHQmin⟩ := minimal_within K K T T ⟨le_rfl,by simp⟩ le_rfl
  have hHQ : IsPreserver K HQ Q := hpres HQ hHQmin.1
  refine ⟨HQ,hHQ,?_,?_⟩
  · intro K' hK'
    exact removed_bound K R Q hR hK hQR HQ hHQ K' hK'
  · let D : ℝ := (diam K S).toNat
    have hD : 0 ≤ D := Nat.cast_nonneg _
    have hdiamD : DiamLE K S D := ⟨hdiam,le_rfl⟩
    have hlocal := h4 V K HQ S D T Finset.univ hS hdiamD hT hsource hHQmin
    have hind : inducedEdges HQ Finset.univ = edgesF HQ := by simp [inducedEdges]
    rw [hind,Finset.card_univ] at hlocal
    change (numEdges HQ : ℝ) ≤ B*((Fintype.card V : ℝ)+
      Real.sqrt ((Fintype.card V : ℝ)*(T.card : ℝ)*(S.card : ℝ)*D)) at hlocal
    have hV' : (Fintype.card V : ℝ) ≤ n := by exact_mod_cast hV
    have hcard' : (T.card : ℝ) ≤ 2*(Q.card : ℝ) := by exact_mod_cast hcard
    have hsqrt2 : Real.sqrt (2:ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
    calc
      _ ≤ B*((Fintype.card V : ℝ)+Real.sqrt ((Fintype.card V : ℝ)*(T.card : ℝ)*(S.card : ℝ)*D)) := hlocal
      _ ≤ B*((n : ℝ)+Real.sqrt ((n : ℝ)*(2*(Q.card : ℝ))*(S.card : ℝ)*D)) := by gcongr
      _ = B*((n : ℝ)+Real.sqrt 2*Real.sqrt ((n : ℝ)*(Q.card : ℝ)*(S.card : ℝ)*D)) := by
        congr 2
        rw [← Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
        congr 1
        ring
      _ ≤ B*((n : ℝ)+2*Real.sqrt ((n : ℝ)*(Q.card : ℝ)*(S.card : ℝ)*D)) := by gcongr
      _ ≤ (2*B)*((n : ℝ)+Real.sqrt ((n : ℝ)*(Q.card : ℝ)*(S.card : ℝ)*D)) := by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        nlinarith
