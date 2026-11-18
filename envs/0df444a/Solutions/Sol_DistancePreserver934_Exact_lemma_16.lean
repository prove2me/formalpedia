-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:55:56.510802+00:00
-- url     : https://prove2.me/submissions/15ec5d52-f878-4abc-8869-39a8dd3a2098

import Definitions.Def_DistancePreserver934_Exact_LoyalCore

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
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

private lemma shortest_support_dist {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V}
    (w : H.Walk s t) (hw : IsShortest w) (x : V) (hx : x ∈ w.support) :
    H.dist s x = w.support.idxOf x := by
  classical
  have hp := shortest_prefix (w.takeUntil x hx) (w.dropUntil x hx)
    (by rw [w.take_spec hx]; exact hw)
  have hnat := congrArg ENat.toNat hp
  simpa only [SimpleGraph.dist,ENat.toNat_natCast,SimpleGraph.Walk.length_takeUntil] using hnat.symm


private lemma shortest_suffix {V : Type} [Fintype V] {H : SimpleGraph V} {s a t : V}
    (p : H.Walk s a) (q : H.Walk a t) (hw : IsShortest (p.append q)) : IsShortest q := by
  have hrev : IsShortest (q.reverse.append p.reverse) := by
    simpa [IsShortest,← SimpleGraph.Walk.reverse_append,SimpleGraph.edist_comm] using hw
  have hq := shortest_prefix q.reverse p.reverse hrev
  simpa [IsShortest,SimpleGraph.edist_comm] using hq


private lemma shortest_getVert_distance {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V}
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

private lemma shortest_support_metric {V : Type} [Fintype V] {H : SimpleGraph V} {s t : V}
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

private lemma pairwise_of_diamLE {V : Type} [Fintype V] (H : SimpleGraph V) (S : Finset V)
    (D : ℝ) (hD : DiamLE H S D) (x y : V) (hx : x ∈ S) (hy : y ∈ S) :
    ∃ k : ℕ, H.edist x y=(k:ℕ∞) ∧ (k:ℝ) ≤ D := by
  have hle : H.edist x y ≤ diam H S :=
    le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
  have hle' : H.edist x y ≤ ((diam H S).toNat:ℕ∞) := by
    rwa [ENat.natCast_toNat hD.1]
  obtain ⟨k,hk,hkbound⟩ := ENat.le_natCast_iff.mp hle'
  refine ⟨k,hk,?_⟩
  exact (show (k:ℝ) ≤ ((diam H S).toNat:ℝ) by exact_mod_cast hkbound).trans hD.2


private lemma interval_bin_bound (z m t L : ℝ) (ht : 0 < t) (hz : z-m ≤ L*t) :
    ⌊(z-m)/t⌋₊ ≤ ⌊L⌋₊ := by
  apply Nat.floor_mono
  exact (div_le_iff₀ ht).mpr hz

private lemma same_interval_bin_close (z w m t : ℝ) (ht : 0 < t) (hz : m ≤ z) (hw : m ≤ w)
    (hb : ⌊(z-m)/t⌋₊ = ⌊(w-m)/t⌋₊) : |z-w| < t := by
  have hz0 : 0 ≤ (z-m)/t := div_nonneg (sub_nonneg.mpr hz) ht.le
  have hw0 : 0 ≤ (w-m)/t := div_nonneg (sub_nonneg.mpr hw) ht.le
  have hzl := Nat.floor_le hz0
  have hzu := Nat.lt_floor_add_one ((z-m)/t)
  have hwl := Nat.floor_le hw0
  have hwu := Nat.lt_floor_add_one ((w-m)/t)
  rw [hb] at hzl hzu
  have hzlo := (le_div_iff₀ ht).mp hzl
  have hzup := (div_lt_iff₀ ht).mp hzu
  have hwlo := (le_div_iff₀ ht).mp hwl
  have hwup := (div_lt_iff₀ ht).mp hwu
  apply abs_lt.mpr
  constructor <;> nlinarith

theorem solution : ∀ A : ℝ, 0 ≤ A → ∀ Cg : ℝ, ∃ K : ℝ, 0 < K ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V)) (n : ℕ) (d l r : ℝ)
      (Vs : Finset V),
      Sec5Context G H R n d l → Eq5 d l r → Eq6 H R Vs n d →
      ∀ Λ' : Finset (Sym2 V), Λ' ⊆ coreEdges H R Vs → (∀ e ∈ Λ', IsGoodEdge H R Vs d r Cg e) →
      ∀ F : Finset (Sym2 V), F ⊆ Λ' → ∀ xe : Sym2 V → V, (∀ e ∈ F, xe e ∈ e) →
      ∀ N : ℝ, 0 ≤ N → (∀ e ∈ F, (vol H (xe e) r : ℝ) ≤ N) →
      DiamLE H (F.image xe) (A*r) →
      ∀ q ∈ R, ((F.filter (fun e => essSet H R e={q})).card:ℝ) ≤ K*N/(d*Real.sqrt r) := by
  intro A hA Cg
  let B : ℕ := ⌊2*A⌋₊+1
  let Cpos : ℝ := 1+max Cg 0
  have hB : 0 < B := by dsimp [B]; omega
  have hCpos : 0 < Cpos := by dsimp [Cpos]; have := le_max_right Cg 0; linarith
  have hCg : Cg ≤ Cpos := by dsimp [Cpos]; have := le_max_left Cg 0; linarith
  refine ⟨(B:ℝ)*Cpos,by positivity,?_⟩
  intro V inst G H R n d l r Vs hctx h5 h6 Λ' hΛ hgood F hF xe hxe N hN hvol hdiam q hq
  classical
  have hv : 0 < Fintype.card V := (Finset.card_pos.mpr h6.1).trans_le (Finset.card_le_univ _)
  have hn : 0 < (n:ℝ) := by exact_mod_cast hv.trans_le hctx.2.2.1
  have hnd : 0 ≤ (n:ℝ)*d := (Nat.cast_nonneg (numEdges H)).trans hctx.2.2.2.1
  have hd : 0 < d := by have := (le_min_iff.mp h5.2).1; have := h5.1; nlinarith
  have hr : 0 < r := lt_of_lt_of_le (by norm_num : (0:ℝ)<6) h5.1
  have hb : 0 < d*Real.sqrt r := mul_pos hd (Real.sqrt_pos.mpr hr)
  let T := F.filter (fun e => essSet H R e={q})
  by_cases hT : T.Nonempty
  swap
  · have hempty : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    change (T.card:ℝ) ≤ _
    rw [hempty,Finset.card_empty,Nat.cast_zero]
    positivity
  have hTF : T ⊆ F := Finset.filter_subset _ _
  have hess : ∀ e ∈ T, IsEssential H q e := by
    intro e he
    have hset := (Finset.mem_filter.mp he).2
    have hm : q ∈ essSet H R e := by rw [hset]; simp
    exact (Finset.mem_filter.mp hm).2
  let s := q.out.1
  let t := q.out.2
  have hrep : s(s,t)=q := Quot.out_eq q
  have hreach : H.Reachable s t := SimpleGraph.edist_ne_top_iff_reachable.mp (by
    rw [hctx.2.1.1.2 s t (by rw [hrep]; exact hq)]
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hctx.1 s t (by rw [hrep]; exact hq)).2)
  obtain ⟨w,hw⟩ := hreach.exists_walk_length_eq_edist
  have hxw : ∀ e ∈ T, xe e ∈ w.support := by
    intro e he
    exact SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
      (Or.inr ⟨e,hess e he s t hrep w hw,hxe e (hTF he)⟩)
  let pos : Sym2 V → ℝ := fun e => H.dist s (xe e)
  obtain ⟨e₀,he₀,hmin⟩ := Finset.exists_min_image T pos hT
  let m := pos e₀
  have hspan : ∀ e ∈ T, 0 ≤ pos e-m ∧ pos e-m ≤ A*r := by
    intro e he
    have hlow : m ≤ pos e := hmin e he
    obtain ⟨k,hk,hkD⟩ := pairwise_of_diamLE H (F.image xe) (A*r) hdiam (xe e) (xe e₀)
      (Finset.mem_image_of_mem xe (hTF he)) (Finset.mem_image_of_mem xe (hTF he₀))
    obtain ⟨j,hj,hjpos⟩ := shortest_support_metric w hw (xe e) (xe e₀) (hxw e he) (hxw e₀ he₀)
    have hkj : k=j := by exact_mod_cast hk.symm.trans hj
    have habs : |pos e-m| ≤ A*r := by
      change |(H.dist s (xe e):ℝ)-(H.dist s (xe e₀):ℝ)| ≤ A*r
      rw [← hjpos,← hkj]
      exact hkD
    exact ⟨sub_nonneg.mpr hlow,by simpa only [abs_of_nonneg (sub_nonneg.mpr hlow)] using habs⟩
  let bin : Sym2 V → ℕ := fun e => ⌊(pos e-m)/(r/2)⌋₊
  have hbin : ∀ e ∈ T, bin e ∈ Finset.range B := by
    intro e he
    have hbnd := interval_bin_bound (pos e) m (r/2) (2*A) (by positivity)
      (by have := (hspan e he).2; nlinarith)
    exact Finset.mem_range.mpr (by dsimp [B,bin]; omega)
  have hclose : ∀ e ∈ T, ∀ f ∈ T, bin e=bin f → xe e ∈ ball H (xe f) (r/2) := by
    intro e he f hf hbf
    have hnear := same_interval_bin_close (pos e) (pos f) m (r/2) (by positivity)
      (by have := (hspan e he).1; linarith) (by have := (hspan f hf).1; linarith) hbf
    obtain ⟨k,hk,hkpos⟩ := shortest_support_metric w hw (xe e) (xe f) (hxw e he) (hxw f hf)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,k,?_,?_⟩
    · rwa [SimpleGraph.edist_comm]
    · change (k:ℝ) ≤ r/2
      rw [hkpos]
      exact hnear.le
  have hbinCard : ∀ i ∈ Finset.range B,
      ((T.filter (fun e => bin e=i)).card:ℝ) ≤ Cpos*N/(d*Real.sqrt r) := by
    intro i hi
    let U := T.filter (fun e => bin e=i)
    by_cases hU : U.Nonempty
    swap
    · have hempty : U=∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      change (U.card:ℝ) ≤ _
      rw [hempty,Finset.card_empty,Nat.cast_zero]
      positivity
    obtain ⟨a,ha⟩ := hU
    have haT : a ∈ T := (Finset.mem_filter.mp ha).1
    have haF : a ∈ F := hTF haT
    have haΛ : a ∈ Λ' := hF haF
    have hsubset : U ⊆ lamStarSet H R Vs (xe a) (r/2) {q} := by
      intro e he
      obtain ⟨heT,hbe⟩ := Finset.mem_filter.mp he
      have heF := hTF heT
      refine Finset.mem_filter.mpr ⟨hΛ (hF heF),?_,(Finset.mem_filter.mp heT).2⟩
      refine ⟨xe e,hxe e heF,?_⟩
      exact hclose e heT a haT (hbe.trans (Finset.mem_filter.mp ha).2.symm)
    have hcard : (U.card:ℝ) ≤ (lamStar H R Vs (xe a) (r/2) {q}:ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hg := hgood a haΛ (xe a) (hxe a haF)
    rw [(Finset.mem_filter.mp haT).2] at hg
    have hvola : (vol H (xe a) r:ℝ) ≤ N := hvol a haF
    have hposvol : 0 ≤ (vol H (xe a) r:ℝ) := Nat.cast_nonneg _
    calc
      (U.card:ℝ) ≤ (lamStar H R Vs (xe a) (r/2) {q}:ℝ) := hcard
      _ ≤ Cg*(vol H (xe a) r:ℝ)/(d*Real.sqrt r) := hg
      _ ≤ Cpos*N/(d*Real.sqrt r) := by
        apply div_le_div_of_nonneg_right _ hb.le
        exact (mul_le_mul_of_nonneg_right hCg hposvol).trans (mul_le_mul_of_nonneg_left hvola hCpos.le)
  have hsum : ∑ i ∈ Finset.range B, (T.filter (fun e => bin e=i)).card = T.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter T (Finset.range B) bin]
    congr 1
    exact Finset.filter_eq_self.mpr hbin
  change (T.card:ℝ) ≤ ((B:ℝ)*Cpos)*N/(d*Real.sqrt r)
  calc
    (T.card:ℝ) = ∑ i ∈ Finset.range B, ((T.filter (fun e => bin e=i)).card:ℝ) := by exact_mod_cast hsum.symm
    _ ≤ ∑ _i ∈ Finset.range B, Cpos*N/(d*Real.sqrt r) := Finset.sum_le_sum hbinCard
    _ = ((B:ℝ)*Cpos)*N/(d*Real.sqrt r) := by simp; ring
