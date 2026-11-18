-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:50:06.424087+00:00
-- url     : https://prove2.me/submissions/c28a9467-89dd-4b4d-890a-f455d9bb4f5b

import Theorems.Thm_DistancePreserver934_Exact_lemma_12
import Theorems.Thm_DistancePreserver934_Exact_lemma_13
import Theorems.Thm_DistancePreserver934_Exact_lemma_15
import Theorems.Thm_DistancePreserver934_Exact_lemma_16
import Theorems.Thm_DistancePreserver934_Exact_lemma_18
import Theorems.Thm_DistancePreserver934_Exact_lemma_19

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
open Classical DistancePreserver934.Exact



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



private lemma card_fiber_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset β) (f : β → α) (k : ℕ)
    (hf : ∀ a ∈ s.image f, (s.filter (fun b => f b=a)).card ≤ k) :
    s.card ≤ k*(s.image f).card := by
  have heq : ∑ a ∈ s.image f, (s.filter (fun b => f b=a)).card = s.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter s (s.image f) f]
    congr 1
    exact Finset.filter_eq_self.mpr (fun b hb => Finset.mem_image_of_mem f hb)
  calc
    s.card = ∑ a ∈ s.image f, (s.filter (fun b => f b=a)).card := heq.symm
    _ ≤ ∑ _a ∈ s.image f, k := Finset.sum_le_sum hf
    _ = _ := by simp [mul_comm]

private lemma edge_incidence_sum {V : Type} [Fintype V] (E : Finset (Sym2 V)) (W : Finset V)
    (xe : Sym2 V → V) (hxe : ∀ e ∈ E, xe e ∈ e ∧ xe e ∈ W) :
    E.card ≤ ∑ x ∈ W, (E.filter (fun e => x ∈ e)).card := by
  classical
  have heq : ∑ x ∈ W, (E.filter (fun e => xe e=x)).card = E.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter E W xe]
    congr 1
    exact Finset.filter_eq_self.mpr (fun e he => (hxe e he).2)
  rw [← heq]
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.card_le_card
  intro e he
  obtain ⟨he,hx⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨he,by simpa only [hx] using (hxe e he).1⟩

private lemma label_vertex_bound {V α : Type*} [DecidableEq V] [DecidableEq α]
    (E : Finset (Sym2 V)) (W : Finset V) (lab : Sym2 V → α) (q : α) :
    (W.filter (fun x => ∃ e ∈ E, x ∈ e ∧ lab e=q)).card ≤
      2*(E.filter (fun e => lab e=q)).card := by
  classical
  let F := E.filter (fun e => lab e=q)
  have hsub : W.filter (fun x => ∃ e ∈ E, x ∈ e ∧ lab e=q) ⊆ F.biUnion Sym2.toFinset := by
    intro x hx
    obtain ⟨_,e,he,hxe,hlab⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_biUnion.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hlab⟩,Sym2.mem_toFinset.mpr hxe⟩
  calc
    _ ≤ (F.biUnion Sym2.toFinset).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ F, e.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum (fun e he => by rw [Sym2.card_toFinset]; split_ifs <;> omega)
    _ = _ := by simp [F,mul_comm]

private lemma exists_weighted_block {ι : Type*} [DecidableEq ι] (I : Finset ι) (m w : ι → ℝ)
    (n d : ℝ) (hn : 0 < n) (hd : 0 < d)
    (hm : n*d/80 ≤ ∑ i ∈ I, m i) (hw : ∑ i ∈ I, w i ≤ 2*n) :
    ∃ i ∈ I, d/320*w i ≤ m i := by
  classical
  by_contra! hnone
  have hle : ∑ i ∈ I, m i ≤ d/320*∑ i ∈ I, w i := by
    calc
      _ ≤ ∑ i ∈ I, d/320*w i := Finset.sum_le_sum (fun i hi => (hnone i hi).le)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hprod := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ d/320)
  nlinarith

private lemma vol_pos {V : Type} [Fintype V] (H : SimpleGraph V) (x : V)
    (r : ℝ) (hr : 0 ≤ r) : 0 < vol H x r := by
  apply Finset.card_pos.mpr
  exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,0,by simp,by simpa using hr⟩⟩

private lemma batch_from_core {V : Type} [Fintype V] (Cg K : ℝ) (hK : 0 < K)
    (G H : SimpleGraph V) (R : Finset (Sym2 V)) (n : ℕ) (d l r : ℝ) (Vs : Finset V)
    (hctx : Sec5Context G H R n d l) (h5 : Eq5 d l r) (h6 : Eq6 H R Vs n d)
    (E₀ : Finset (Sym2 V)) (hE₀ : E₀ ⊆ coreEdges H R Vs)
    (hEgood : ∀ e ∈ E₀, IsGoodEdge H R Vs d r Cg e)
    (hEmass : (n:ℝ)*d/80 ≤ (E₀.card:ℝ))
    (hlocal : ∀ F : Finset (Sym2 V), F ⊆ E₀ → ∀ xe : Sym2 V → V, (∀ e ∈ F, xe e ∈ e) →
      ∀ N : ℝ, 0 ≤ N → (∀ e ∈ F, (vol H (xe e) r:ℝ) ≤ N) →
      DiamLE H (F.image xe) (4*r) →
      ∀ q ∈ R, ((F.filter (fun e => essSet H R e={q})).card:ℝ) ≤ K*N/(d*Real.sqrt r)) :
    ∃ Q : Finset (Sym2 V), Q ⊆ R ∧ ∃ S : Finset V, Covers H S Q ∧
      (1/(2560*K))*d^2*Real.sqrt r ≤ (Q.card:ℝ) ∧
      (S.card:ℝ) ≤ 1280*(Q.card:ℝ)/d ∧ DiamLE H S (4*r) := by
  classical
  have hv : 0 < Fintype.card V := (Finset.card_pos.mpr h6.1).trans_le (Finset.card_le_univ _)
  have hn : 0 < (n:ℝ) := by exact_mod_cast hv.trans_le hctx.2.2.1
  have hnd : 0 ≤ (n:ℝ)*d := (Nat.cast_nonneg (numEdges H)).trans hctx.2.2.2.1
  have hd : 0 < d := by have := (le_min_iff.mp h5.2).1; have := h5.1; nlinarith
  have hr : 0 < r := lt_of_lt_of_le (by norm_num : (0:ℝ)<6) h5.1
  obtain ⟨Cs,σ,hCs,hσ,hsurj,hball,hvol,hsumvol,hsumblocks,hVscard⟩ :=
    DistancePreserver934.Exact.lemma_18 H n hctx.2.2.1 Vs r hr
  let xe : Sym2 V → V := fun e => if vol H e.out.1 r ≤ vol H e.out.2 r then e.out.2 else e.out.1
  have hxe (e : Sym2 V) : xe e ∈ e := by
    dsimp [xe]; split_ifs
    · exact Sym2.out_snd_mem e
    · exact Sym2.out_fst_mem e
  have hxeVs : ∀ e ∈ E₀, xe e ∈ Vs := by
    intro e he
    exact (Finset.mem_filter.mp (hE₀ he)).2 (xe e) (hxe e)
  let Eblock : V → Finset (Sym2 V) := fun c => E₀.filter (fun e => σ (xe e)=c)
  let Wblock : V → Finset V := fun c => Vs.filter (fun x => σ x=c)
  have hsumE : ∑ c ∈ Cs, (Eblock c).card = E₀.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter E₀ Cs (fun e => σ (xe e))]
    congr 1
    exact Finset.filter_eq_self.mpr (fun e he => hσ (xe e) (hxeVs e he))
  have hweights : ∑ c ∈ Cs, ((vol H c r:ℝ)+((Wblock c).card:ℝ)) ≤ 2*(n:ℝ) := by
    rw [Finset.sum_add_distrib]
    have hv' : (∑ c ∈ Cs, (vol H c r:ℝ)) ≤ n := by exact_mod_cast hsumvol
    have hw' : (∑ c ∈ Cs, ((Wblock c).card:ℝ)) ≤ n := by
      have hnat : (∑ c ∈ Cs, (Wblock c).card) ≤ n := hsumblocks.trans_le hVscard
      exact_mod_cast hnat
    linarith
  have hmass : (n:ℝ)*d/80 ≤ ∑ c ∈ Cs, ((Eblock c).card:ℝ) := by
    have heq : (∑ c ∈ Cs, ((Eblock c).card:ℝ)) = (E₀.card:ℝ) := by exact_mod_cast hsumE
    rw [heq]; exact hEmass
  obtain ⟨c,hc,hblock⟩ := exists_weighted_block Cs (fun c => ((Eblock c).card:ℝ))
    (fun c => (vol H c r:ℝ)+((Wblock c).card:ℝ)) n d hn hd hmass hweights
  let E := Eblock c
  let W := Wblock c
  let N : ℝ := vol H c r
  have hN : 0 < N := by
    change 0 < (vol H c r:ℝ)
    exact_mod_cast vol_pos H c r hr.le
  have hEE : E ⊆ E₀ := Finset.filter_subset _ _
  have howner : ∀ e ∈ E, xe e ∈ e ∧ xe e ∈ W := by
    intro e he
    obtain ⟨he,hσe⟩ := Finset.mem_filter.mp he
    exact ⟨hxe e,Finset.mem_filter.mpr ⟨hxeVs e he,hσe⟩⟩
  have hEpos : 0 < (E.card:ℝ) := by
    change d/320*(N+(W.card:ℝ)) ≤ (E.card:ℝ) at hblock
    have hW : 0 ≤ (W.card:ℝ) := Nat.cast_nonneg _
    nlinarith
  have hWpos : W.Nonempty := by
    have he : E.Nonempty := Finset.card_pos.mp (by exact_mod_cast hEpos)
    obtain ⟨e,he⟩ := he
    exact ⟨xe e,(howner e he).2⟩
  have hWball : W ⊆ ball H c (2*r) := by
    intro x hx
    obtain ⟨hx,hσx⟩ := Finset.mem_filter.mp hx
    simpa only [hσx] using hball x hx
  have hdiam : DiamLE H (E.image xe) (4*r) := by
    have hs : E.image xe ⊆ ball H c (2*r) := by
      intro x hx
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
      exact hWball (howner e he).2
    convert diamLE_of_subset_ball H (E.image xe) c (2*r) (by positivity) hs using 1 <;> ring
  have hlabelLocal : ∀ q ∈ R, ((E.filter (fun e => essSet H R e={q})).card:ℝ) ≤ K*N/(d*Real.sqrt r) := by
    apply hlocal E hEE xe (fun e he => hxe e) N hN.le _ hdiam
    intro e he
    have hv' := hvol (xe e) (hxeVs e (hEE he))
    have hvnat : vol H (xe e) r ≤ vol H c r := by simpa only [(Finset.mem_filter.mp he).2] using hv'
    change (vol H (xe e) r:ℝ) ≤ (vol H c r:ℝ)
    exact_mod_cast hvnat
  obtain ⟨x₀,hx₀⟩ := h6.1
  let lab : Sym2 V → Sym2 V := fun e => if h : (essSet H R e).card=1 then
    (Finset.card_eq_one.mp h).choose else s(x₀,x₀)
  have hlabel : ∀ e ∈ E₀, essSet H R e={lab e} := by
    intro e he
    have hpriv : e ∈ privEdges H R := (Finset.mem_filter.mp (hE₀ he)).1
    have hcard := (Finset.mem_filter.mp hpriv).2
    dsimp [lab]
    rw [dif_pos hcard]
    exact (Finset.card_eq_one.mp hcard).choose_spec
  have hlabR : ∀ e ∈ E₀, lab e ∈ R := by
    intro e he
    have hm : lab e ∈ essSet H R e := by rw [hlabel e he]; simp
    exact (Finset.mem_filter.mp hm).1
  have hlabess : ∀ e ∈ E₀, IsEssential H (lab e) e := by
    intro e he
    have hm : lab e ∈ essSet H R e := by rw [hlabel e he]; simp
    exact (Finset.mem_filter.mp hm).2
  let A₀ : V → Finset (Sym2 V) := fun x => (E.filter (fun e => x ∈ e)).image lab
  let A : W → Finset (Sym2 V) := fun x => A₀ x.val
  let Δ : ℕ := ∑ x : W, (A x).card
  have hΔeq : (∑ x ∈ W, (A₀ x).card) = Δ := (Finset.sum_coe_sort W (fun x => (A₀ x).card)).symm
  have hincBound : ∀ x ∈ W, (E.filter (fun e => x ∈ e)).card ≤ 2*(A₀ x).card := by
    intro x hx
    apply card_fiber_bound (E.filter (fun e => x ∈ e)) lab 2
    intro q hq
    obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hq
    have hqR : q ∈ R := by simpa only [heq] using hlabR e (hEE (Finset.mem_filter.mp he).1)
    have hsub : (E.filter (fun e => x ∈ e)).filter (fun e => lab e=q) ⊆
        (edgesF H).filter (fun e => x ∈ e ∧ IsEssential H q e) := by
      intro f hf
      obtain ⟨hf,hlab⟩ := Finset.mem_filter.mp hf
      obtain ⟨hf,hxf⟩ := Finset.mem_filter.mp hf
      have hcore := hE₀ (hEE hf)
      have hpriv := (Finset.mem_filter.mp hcore).1
      have hedge := (Finset.mem_filter.mp hpriv).1
      refine Finset.mem_filter.mpr ⟨hedge,hxf,?_⟩
      simpa only [hlab] using hlabess f (hEE hf)
    exact (Finset.card_le_card hsub).trans
      ((DistancePreserver934.Exact.lemma_12 G H R hctx.1 hctx.2.1 q hqR).1 x)
  have hEΔ : E.card ≤ 2*Δ := by
    have hsum := Finset.sum_le_sum hincBound
    have heInc := edge_incidence_sum E W xe howner
    have hraw : (∑ x ∈ W, (E.filter (fun e => x ∈ e)).card) ≤ 2*Δ := by
      simpa only [← Finset.mul_sum,hΔeq] using hsum
    exact heInc.trans hraw
  have hΔ : 0 < Δ := by
    have he : 0 < E.card := by exact_mod_cast hEpos
    omega
  have hM : 1 ≤ Fintype.card W := by
    simpa only [Fintype.card_coe] using Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Finset.card_pos.mpr hWpos))
  let γ := 2*K*N/(d*Real.sqrt r)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hμ : ∀ q : Sym2 V, ((Finset.univ.filter (fun x : W => q ∈ A x)).card:ℝ) ≤ γ := by
    intro q
    let Fq := (Finset.univ : Finset W).filter (fun x => q ∈ A x)
    by_cases hqR : q ∈ R
    · have hinj : Set.InjOn (Subtype.val : W → V) (Fq : Set W) := fun a ha b hb h => Subtype.ext h
      have hsub : Fq.image (Subtype.val : W → V) ⊆
          W.filter (fun x => ∃ e ∈ E, x ∈ e ∧ lab e=q) := by
        intro x hx
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
        have hqA := (Finset.mem_filter.mp hy).2
        obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hqA
        obtain ⟨he,hye⟩ := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨y.property,e,he,hye,heq⟩
      have hcount : Fq.card ≤ 2*(E.filter (fun e => lab e=q)).card := by
        have hc := (Finset.card_le_card hsub).trans (label_vertex_bound E W lab q)
        rwa [Finset.card_image_of_injOn hinj] at hc
      have heq : E.filter (fun e => lab e=q) = E.filter (fun e => essSet H R e={q}) := by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨he,hlab⟩
          exact ⟨he,by rw [hlabel e (hEE he),hlab]⟩
        · rintro ⟨he,hess⟩
          exact ⟨he,Finset.singleton_injective ((hlabel e (hEE he)).symm.trans hess)⟩
      rw [heq] at hcount
      have hcount' : (Fq.card:ℝ) ≤ 2*((E.filter (fun e => essSet H R e={q})).card:ℝ) := by exact_mod_cast hcount
      have hloc := hlabelLocal q hqR
      change (Fq.card:ℝ) ≤ γ
      calc
        (Fq.card:ℝ) ≤ 2*((E.filter (fun e => essSet H R e={q})).card:ℝ) := hcount'
        _ ≤ 2*(K*N/(d*Real.sqrt r)) := mul_le_mul_of_nonneg_left hloc (by norm_num)
        _ = γ := by dsimp [γ]; ring
    · have hF : Fq = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        have hqA := (Finset.mem_filter.mp hx).2
        obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hqA
        exact hqR (heq ▸ hlabR e (hEE (Finset.mem_filter.mp he).1))
      change (Fq.card:ℝ) ≤ γ
      rw [hF,Finset.card_empty,Nat.cast_zero]
      exact hγ.le
  obtain ⟨J,hQsize,hJsize⟩ := DistancePreserver934.Exact.lemma_19 A γ hM hΔ hμ
  let Q := J.biUnion A
  let S := J.image (Subtype.val : W → V)
  have hQR : Q ⊆ R := by
    intro q hq
    obtain ⟨x,hx,hqA⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hqA
    exact hlabR e (hEE (Finset.mem_filter.mp he).1)
  have hcover : Covers H S Q := by
    intro q hq
    obtain ⟨x,hx,hqA⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hqA
    obtain ⟨he,hxe'⟩ := Finset.mem_filter.mp he
    have hcore := hE₀ (hEE he)
    have hpriv := (Finset.mem_filter.mp hcore).1
    have hedge : e ∈ H.edgeSet := (Finset.mem_filter.mp (Finset.mem_filter.mp hpriv).1).2
    exact ⟨x.val,Finset.mem_image_of_mem _ hx,e,hedge,hxe',hlabess e (hEE he)⟩
  have hScard : S.card = J.card := Finset.card_image_of_injOn (fun a ha b hb h => Subtype.ext h)
  have hSball : S ⊆ ball H c (2*r) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hWball y.property
  have hSdiam : DiamLE H S (4*r) := by
    convert diamLE_of_subset_ball H S c (2*r) (by positivity) hSball using 1 <;> ring
  let δ : ℝ := Δ
  let M : ℝ := W.card
  have hδ : 0 < δ := by change 0 < (Δ:ℝ); exact_mod_cast hΔ
  have hMpos : 0 < M := by change 0 < (W.card:ℝ); exact_mod_cast Finset.card_pos.mpr hWpos
  have hEΔ' : (E.card:ℝ) ≤ 2*δ := by
    change (E.card:ℝ) ≤ 2*(Δ:ℝ)
    exact_mod_cast hEΔ
  change d/320*(N+M) ≤ (E.card:ℝ) at hblock
  have hδN : d*N/640 ≤ δ := by nlinarith
  have hδM : d*M/640 ≤ δ := by nlinarith
  refine ⟨Q,hQR,S,hcover,?_,?_,hSdiam⟩
  · change δ/(2*γ) ≤ (Q.card:ℝ) at hQsize
    have hq := (div_le_iff₀ (by positivity : 0 < 2*γ)).mp hQsize
    have hrew : (Q.card:ℝ)*(2*γ) = ((Q.card:ℝ)*(4*K*N))/(d*Real.sqrt r) := by dsimp [γ]; ring
    rw [hrew] at hq
    have hclear := (le_div_iff₀ (mul_pos hd (Real.sqrt_pos.mpr hr))).mp hq
    have hδb := mul_le_mul_of_nonneg_right hδN (mul_nonneg hd.le (Real.sqrt_nonneg r))
    have hnineq : d^2*Real.sqrt r ≤ (Q.card:ℝ)*(2560*K) := by
      apply (mul_le_mul_iff_left₀ hN).mp
      nlinarith
    have hfinal := (div_le_iff₀ (by positivity : 0 < 2560*K)).mpr hnineq
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,one_mul] using hfinal
  · change (J.card:ℝ) ≤ 2*(Fintype.card W:ℝ)/δ*(Q.card:ℝ) at hJsize
    have hMcard : (Fintype.card W:ℝ) = M := by simp only [Fintype.card_coe]; rfl
    rw [hMcard] at hJsize
    have hratio : 2*M/δ ≤ 1280/d := by
      apply (div_le_div_iff₀ hδ hd).mpr
      nlinarith
    have hsize := hJsize.trans (mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg Q.card))
    rw [hScard]
    simpa only [div_mul_eq_mul_div] using hsize

theorem solution : ∃ c₀ c₁ c₂ : ℝ, 0 < c₀ ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V)) (n : ℕ) (d l r : ℝ),
      0 < Fintype.card V → Sec5Context G H R n d l →
      (n:ℝ)*d/20 ≤ ((privEdges H R).card:ℝ) → Eq5 d l r →
      ∃ Q : Finset (Sym2 V), Q ⊆ R ∧ ∃ S : Finset V, Covers H S Q ∧
        c₀*d^2*Real.sqrt r ≤ (Q.card:ℝ) ∧ (S.card:ℝ) ≤ c₁*(Q.card:ℝ)/d ∧ DiamLE H S (c₂*r) := by
  obtain ⟨Cg,hCg,h15⟩ := DistancePreserver934.Exact.lemma_15
  obtain ⟨K,hK,h16⟩ := DistancePreserver934.Exact.lemma_16 4 (by norm_num) Cg
  refine ⟨1/(2560*K),1280,4,by positivity,?_⟩
  intro V inst G H R n d l r hV hctx hΛ h5
  obtain ⟨Vs,h6⟩ := DistancePreserver934.Exact.lemma_13 G H R n d hV hctx.1 hctx.2.1
    hctx.2.2.1 hctx.2.2.2.1 hΛ
  obtain ⟨E₀,hE₀,hhalf,hmass,hgood⟩ := h15 V G H R n d l r Vs hctx h5 h6
  apply batch_from_core Cg K hK G H R n d l r Vs hctx h5 h6 E₀ hE₀ hgood hmass
  exact h16 V G H R n d l r Vs hctx h5 h6 E₀ hE₀ hgood
