-- Prove2me | solution 1 for DirectedHamiltonicity.Main.lemma8
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T06:47:46.006276+00:00
-- url     : https://prove2.me/submissions/113ebae7-6513-4b72-8b45-f866ab8a8041

import Definitions.Def_DirectedHamiltonicity_Main_DetSum
import Theorems.Thm_DirectedHamiltonicity_Main_lemma7

open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph Classical
open scoped BigOperators

namespace DHCDetSum

private abbrev R := Polynomial (ZMod 2)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Multidigraph V E) (s t : V)
private abbrev Pos := Fin (Fintype.card V - 1)
private def Edges (P : Pos (V := V) → E) := Finset.univ.image P
private def Covers (T : Finset E) := ∀ v : Internal s t, ∃ e ∈ T, G.tail e = v.1

omit [Fintype E] [DecidableEq E] in
private theorem heads_card {T : Finset E} (h : G.IsOutArborescence s T) :
    T.card = Fintype.card V - 1 := by
  classical
  let f (e : T) : {v : V // v ≠ s} := ⟨G.head e.1,h.1 e.1 e.2⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro a b he
      have hh : G.head a.1 = G.head b.1 := congrArg Subtype.val he
      apply Subtype.ext
      exact (h.2.1 _ (h.1 _ b.2)).unique ⟨a.2,hh⟩ ⟨b.2,rfl⟩
    · intro v
      obtain ⟨e, ⟨he,hh⟩, _⟩ := h.2.1 v.1 v.2
      exact ⟨⟨e,he⟩,Subtype.ext hh⟩
  simpa [Fintype.card_subtype_compl] using Fintype.card_of_bijective hbij

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
private theorem path_vertex_surj (P : Pos (V := V) → E) (hp : G.IsHamPath s t P) :
    Function.Surjective (G.walkVerts s P) := by
  have : Nonempty V := ⟨s⟩
  have hn := Fintype.card_pos (α := V)
  apply ((Fintype.bijective_iff_injective_and_card _).2 ⟨hp.2.1, ?_⟩).2
  simp only [Fintype.card_fin]
  omega

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
private theorem path_head_inj (P : Pos (V := V) → E) (hp : G.IsHamPath s t P) :
    Function.Injective (fun i => G.head (P i)) := by
  intro i j h
  exact Fin.succ_injective _ (hp.2.1 (by simpa [walkVerts] using h : G.walkVerts s P i.succ = G.walkVerts s P j.succ))

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
private theorem path_tail_inj (P : Pos (V := V) → E) (hp : G.IsHamPath s t P) :
    Function.Injective (fun i => G.tail (P i)) := by
  intro i j h
  apply Fin.castSucc_injective
  exact hp.2.1 ((hp.1 i).symm.trans (h.trans (hp.1 j)))

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
private theorem path_inj (P : Pos (V := V) → E) (hp : G.IsHamPath s t P) :
    Function.Injective P := fun _ _ h => path_head_inj G s t P hp (congrArg G.head h)

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
private theorem path_tail_ne (P : Pos (V := V) → E) (hp : G.IsHamPath s t P) (i) :
    G.tail (P i) ≠ t := by
  intro h
  have he := hp.2.1 ((hp.1 i).symm.trans (h.trans hp.2.2.symm))
  exact Fin.castSucc_ne_last i he

omit [DecidableEq V] [Fintype E] in
private theorem path_tree (P : Pos (V := V) → E) (hp : G.IsHamPath s t P) :
    G.IsOutArborescence s (Edges P) ∧ Covers G s t (Edges P) := by
  classical
  let vs := G.walkVerts s P
  have headAt (i) : G.head (P i) = vs i.succ := by simp [vs,walkVerts]
  have h0 : vs 0 = s := Fin.cons_zero ..
  have mem (i) : P i ∈ Edges P := Finset.mem_image.mpr ⟨i, Finset.mem_univ _,rfl⟩
  have pathTo (j) : Relation.ReflTransGen (fun u v => ∃ e ∈ Edges P, G.tail e = u ∧ G.head e = v) s (vs j) := by
    induction j using Fin.induction with
    | zero => rw [h0]
    | succ i ih => exact ih.tail ⟨P i, mem i, hp.1 i, headAt i⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rintro e he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    intro hh
    exact Fin.succ_ne_zero i (hp.2.1 ((headAt i).symm.trans (hh.trans h0.symm)))
  · intro v hv
    obtain ⟨j,hj⟩ := path_vertex_surj G s t P hp v
    refine Fin.cases ?_ (fun i hi => ?_) j hj
    · intro he; exact (hv (he.symm.trans h0)).elim
    · have hh : G.head (P i) = v := (headAt i).trans hi
      refine ⟨P i, ⟨mem i,hh⟩, ?_⟩
      rintro e ⟨he,hev⟩
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp he
      exact congrArg P (path_head_inj G s t P hp (hev.trans hh.symm))
  · intro v
    obtain ⟨j,hj⟩ := path_vertex_surj G s t P hp v
    exact hj ▸ pathTo j
  · intro v
    obtain ⟨j,hj⟩ := path_vertex_surj G s t P hp v.1
    refine Fin.lastCases ?_ (fun i hi => ?_) j hj
    · intro he; exact (v.2.2 (he.symm.trans hp.2.2)).elim
    · exact ⟨P i,mem i,(hp.1 i).trans hi⟩

omit [DecidableEq V] [Fintype E] in
private theorem determined_by_edges (P Q : Pos (V := V) → E)
    (hp : G.IsHamPath s t P) (hq : G.IsHamPath s t Q) (hsame : Edges P = Edges Q) : P = Q := by
  classical
  have step (i) (h : G.walkVerts s P i.castSucc = G.walkVerts s Q i.castSucc) : P i = Q i := by
    have hm : P i ∈ Edges Q := hsame ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hm
    have hidx : j = i := path_tail_inj G s t Q hq
      ((congrArg G.tail hj).trans ((hp.1 i).trans (h.trans (hq.1 i).symm)))
    exact hidx ▸ hj.symm
  have verts (j) : G.walkVerts s P j = G.walkVerts s Q j := by
    induction j using Fin.induction with
    | zero => simp [walkVerts]
    | succ i ih => simpa [walkVerts] using congrArg G.head (step i ih)
  exact funext fun i => step i (verts i.castSucc)

/-- Up to the first visit to an absorbing terminal, the iterates of a deterministic
successor enumerate every reachable vertex exactly once. -/
private theorem enumerate_orbit (f : V → V) (hfix : f t = t)
    (hvisit : ∀ x, ∃ n : ℕ, f^[n] s = x) :
    (∀ i j : Fin ((Fintype.card V - 1) + 1), f^[i.1] s = f^[j.1] s → i = j) ∧
    f^[Fintype.card V - 1] s = t ∧ ∀ i : Pos (V := V), f^[i.1] s ≠ t := by
  classical
  let n := Nat.find (hvisit t)
  have last : f^[n] s = t := Nat.find_spec (hvisit t)
  have earlier {i : ℕ} (hi : i < n) : f^[i] s ≠ t := Nat.find_min (hvisit t) hi
  have strict {i j : ℕ} (hij : i < j) (hj : j ≤ n) (he : f^[i] s = f^[j] s) : False := by
    have h1 := congrArg (f^[n-j]) he
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      Nat.sub_add_cancel hj, last] at h1
    exact earlier (by omega) h1
  have inj : Function.Injective (fun i : Fin (n+1) => f^[i.1] s) := by
    intro i j h
    rcases lt_trichotomy i.1 j.1 with hlt | he | hgt
    · exact (strict hlt (by omega) h).elim
    · exact Fin.ext he
    · exact (strict hgt (by omega) h.symm).elim
  have surj : Function.Surjective (fun i : Fin (n+1) => f^[i.1] s) := by
    intro v
    obtain ⟨k,hk⟩ := hvisit v
    by_cases hkn : k ≤ n
    · exact ⟨⟨k,by omega⟩,hk⟩
    · refine ⟨Fin.last n, ?_⟩
      change f^[n] s = v
      rw [last]
      have he : f^[k] s = t := by
        conv_lhs => rw [show k = (k-n)+n by omega, Function.iterate_add_apply, last]
        exact Function.iterate_fixed hfix _
      exact he.symm.trans hk
  have hcard := Fintype.card_of_bijective (show Function.Bijective _ from ⟨inj,surj⟩)
  simp only [Fintype.card_fin] at hcard
  have hn : Fintype.card V - 1 = n := by omega
  refine ⟨?_, by simpa only [hn] using last, fun i => earlier (lt_of_lt_of_eq i.isLt hn)⟩
  rw [hn]
  exact fun _ _ h => inj h


omit [Fintype E] in
/-- In a spanning out-tree with every internal vertex represented as a tail,
the tail map hits every vertex except the terminal, so the tree is a single path. -/
private theorem path_of_cover {T : Finset E} (hst : s ≠ t)
    (hT : G.IsOutArborescence s T) (hc : Covers G s t T) :
    ∃ P : Pos (V := V) → E, G.IsHamPath s t P ∧ Edges P = T := by
  classical
  have start : ∃ e ∈ T, G.tail e = s := by
    rcases (hT.2.2 t).cases_head with he | ⟨v,⟨e,he,h,_⟩,_⟩
    · exact (hst he).elim
    · exact ⟨e,he,h⟩
  have existsOut (v : {v : V // v ≠ t}) : ∃ e : T, G.tail e.1 = v.1 := by
    have h : ∃ e ∈ T, G.tail e = v.1 := by
      by_cases hvs : v.1 = s
      · simpa [hvs] using start
      · exact hc ⟨v.1,hvs,v.2⟩
    obtain ⟨e,he,hh⟩ := h
    exact ⟨⟨e,he⟩,hh⟩
  let out (v : {v : V // v ≠ t}) := Classical.choose (existsOut v)
  have hout (v) : G.tail (out v).1 = v.1 := Classical.choose_spec (existsOut v)
  have bij : Function.Bijective out := by
    apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · intro u v he
      exact Subtype.ext ((hout u).symm.trans ((congrArg (fun e : T => G.tail e.1) he).trans (hout v)))
    · simp [Fintype.card_subtype_compl, heads_card G s hT]
  let f (v : V) := if h : v ≠ t then G.head (out ⟨v,h⟩).1 else t
  have next (v : V) (h : v ≠ t) : f v = G.head (out ⟨v,h⟩).1 := dif_pos h
  have fixed : f t = t := by simp [f]
  have edge (e) (he : e ∈ T) : f (G.tail e) = G.head e := by
    obtain ⟨v,hv⟩ := bij.2 ⟨e,he⟩
    have heq : (out v).1 = e := congrArg Subtype.val hv
    rw [← heq, hout, show f v.1 = G.head (out v).1 by simp [f,v.2]]
  have visits (v : V) : ∃ n : ℕ, f^[n] s = v := by
    induction (hT.2.2 v) with
    | refl => exact ⟨0,rfl⟩
    | tail _ h ih =>
      obtain ⟨e,he,ht,hh⟩ := h
      obtain ⟨n,hn⟩ := ih
      exact ⟨n+1, by rw [Function.iterate_succ_apply',hn,← ht,edge e he,hh]⟩
  obtain ⟨inj,last,early⟩ := enumerate_orbit s t f fixed visits
  let P (i : Pos (V := V)) := (out ⟨f^[i.1] s,early i⟩).1
  have step (i : Pos (V := V)) : G.head (P i) = f^[i.1+1] s := by
    rw [Function.iterate_succ_apply']
    exact (next _ (early i)).symm
  have vertex (j) : G.walkVerts s P j = f^[j.1] s := by
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · exact (Fin.cons_succ ..).trans (step i)
  have hp : G.IsHamPath s t P :=
    ⟨fun i => (hout _).trans (vertex i.castSucc).symm,
     fun i j he => inj i j ((vertex i).symm.trans (he.trans (vertex j))),
     (vertex (Fin.last _)).trans last⟩
  refine ⟨P,hp,Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro e he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    exact (out ⟨_,early i⟩).2
  · rw [heads_card G s hT, Edges, Finset.card_image_of_injective _ (path_inj G s t P hp)]
    simp [Pos]

private theorem path_sum (hst : s ≠ t) (p : E → R) :
    G.hamPathPoly p s t =
      ∑ T ∈ Finset.univ.filter (fun T : Finset E => G.IsOutArborescence s T ∧ Covers G s t T),
        ∏ e ∈ T, p e := by
  classical
  unfold hamPathPoly
  apply Finset.sum_bij (fun P _ => Edges P)
  · intro P hP
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,path_tree G s t P (Finset.mem_filter.mp hP).2⟩
  · intro P hP Q hQ he
    exact determined_by_edges G s t P Q (Finset.mem_filter.mp hP).2 (Finset.mem_filter.mp hQ).2 he
  · intro T hT
    obtain ⟨ht,hc⟩ := (Finset.mem_filter.mp hT).2
    obtain ⟨P,hp,he⟩ := path_of_cover G s t hst ht hc
    exact ⟨P,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,he⟩
  · intro P hP
    rw [Edges,Finset.prod_image]
    exact (path_inj G s t P (Finset.mem_filter.mp hP).2).injOn


open Classical in
private noncomputable def mask (p : E → R) (X : Finset (Internal s t)) (e : E) : R :=
  if G.KeepArc s t X e then p e else 0

omit [Fintype E] [DecidableEq E] in
private theorem sum_masks (T : Finset E) (p : E → R) :
    (∑ X : Finset (Internal s t), ∏ e ∈ T, mask G s t p X e) =
      if Covers G s t T then ∏ e ∈ T, p e else 0 := by
  classical
  let U := Finset.univ.filter (fun v : Internal s t => ∃ e ∈ T, G.tail e = v.1)
  have kept (X : Finset (Internal s t)) : (∀ e ∈ T, G.KeepArc s t X e) ↔ U ⊆ X := by
    constructor
    · intro h v hmem
      obtain ⟨e,he,eq⟩ := (Finset.mem_filter.mp hmem).2
      obtain ⟨v,hv⟩ := v
      change G.tail e = v at eq
      subst v
      exact h e he hv
    · intro h e he hv
      exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,he,rfl⟩)
  have covered : U = Finset.univ ↔ Covers G s t T := by
    constructor
    · intro h v
      exact (Finset.mem_filter.mp (show v ∈ U from h ▸ Finset.mem_univ v)).2
    · intro h
      exact Finset.eq_univ_of_forall (fun v => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h v⟩)
  simp_rw [mask,Finset.prod_ite_zero,kept]
  rw [← Finset.sum_filter,Finset.sum_const]
  have interval : Finset.univ.filter (fun X : Finset (Internal s t) => U ⊆ X) =
      Finset.Icc U Finset.univ := by ext X; simp
  rw [interval,Finset.card_Icc_finset (Finset.subset_univ U)]
  by_cases hu : U = Finset.univ
  · simp [hu,covered.mp hu]
  · have hlt : U.card < (Finset.univ : Finset (Internal s t)).card :=
      Finset.card_lt_card (lt_of_le_of_ne (Finset.subset_univ U) hu)
    rw [if_neg (mt covered.mpr hu), nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
      (CharTwo.two_eq_zero : (2 : R) = 0),zero_pow (by omega),zero_mul]

variable {F : Type} [Fintype F] [DecidableEq F] (A : Multidigraph V F)
omit [DecidableEq V] [DecidableEq E] [DecidableEq F] in
private theorem add_path_sum (hAt : ∀ a, A.tail a = t) (p : E → R) (pA : F → R) :
    G.hamPathPoly p s t = (G.addArcs A).hamPathPoly (Sum.elim p pA) s t := by
  classical
  let lift (P : Pos (V := V) → E) := fun i => (Sum.inl (P i) : E ⊕ F)
  have path (P) : (G.addArcs A).IsHamPath s t (lift P) ↔ G.IsHamPath s t P := Iff.rfl
  unfold hamPathPoly
  apply Finset.sum_bij (fun P _ => lift P)
  · intro P hP
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(path P).2 (Finset.mem_filter.mp hP).2⟩
  · intro P _ Q _ he
    exact funext fun i => Sum.inl.inj (congrFun he i)
  · intro Q hQ
    have hq := (Finset.mem_filter.mp hQ).2
    have existsPre (i) : ∃ e : E, (Sum.inl e : E ⊕ F) = Q i := by
      cases he : Q i with
      | inl e => exact ⟨e,rfl⟩
      | inr a =>
        have h := path_tail_ne (G.addArcs A) s t Q hq i
        exact (h (by rw [he]; exact hAt a)).elim
    let P (i) := Classical.choose (existsPre i)
    have he : lift P = Q := funext fun i => Classical.choose_spec (existsPre i)
    refine ⟨P,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(path P).1 ?_⟩,he⟩
    rwa [he]
  · intro P _
    rfl

open Classical in
private noncomputable def mass (q : V → V → Prop) [DecidableRel q] (p : E → R) : R :=
  ∑ e, if q (G.tail e) (G.head e) then p e else 0

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
private theorem filtered_sum (X : Finset (Internal s t)) (b : E → R) :
    (∑ e : {e // G.KeepArc s t X e}, b e.1) =
      ∑ e, if G.KeepArc s t X e then b e else 0 := by
  classical
  let U := Finset.univ.filter (G.KeepArc s t X)
  have hU : ∀ e, e ∈ U ↔ G.KeepArc s t X e := by simp [U]
  rw [← Finset.sum_subtype U hU]
  simp [U,Finset.sum_filter]

omit [Fintype V] [DecidableEq V] [DecidableEq E] [DecidableEq F] in
private theorem mass_mask (hAt : ∀ a, A.tail a = t) (p : E → R) (pA : F → R)
    (X : Finset (Internal s t)) (q : V → V → Prop) [DecidableRel q] :
    mass ((G.subX s t X).addArcs A) q (Sum.elim (fun e => p e.1) pA) =
      mass (G.addArcs A) q (mask (G.addArcs A) s t (Sum.elim p pA) X) := by
  classical
  have keepA (a : F) : (G.addArcs A).KeepArc s t X (Sum.inr a) := by
    intro hv
    exact (hv.2 (hAt a)).elim
  simp only [mass,Fintype.sum_sum_type]
  congr 1
  · change (∑ e : {e // G.KeepArc s t X e}, if q (G.tail e.1) (G.head e.1) then p e.1 else 0) =
        ∑ e, if q (G.tail e) (G.head e) then mask (G.addArcs A) s t (Sum.elim p pA) X (.inl e) else 0
    rw [filtered_sum G s t X (fun e => if q (G.tail e) (G.head e) then p e else 0)]
    apply Finset.sum_congr rfl
    intro e _
    have hk : (G.addArcs A).KeepArc s t X (.inl e) ↔ G.KeepArc s t X e := Iff.rfl
    by_cases h : G.KeepArc s t X e <;> simp [mask,hk,h]
  · apply Finset.sum_congr rfl
    intro a _
    change (if q (A.tail a) (A.head a) then pA a else 0) =
      if q (A.tail a) (A.head a) then mask (G.addArcs A) s t (Sum.elim p pA) X (.inr a) else 0
    simp [mask,keepA]

omit [Fintype V] [DecidableEq E] [DecidableEq F] in
private theorem lap_mask (hAt : ∀ a, A.tail a = t) (p : E → R) (pA : F → R)
    (X : Finset (Internal s t)) :
    ((G.subX s t X).addArcs A).reducedLaplacian (Sum.elim (fun e => p e.1) pA) s =
      (G.addArcs A).reducedLaplacian (mask (G.addArcs A) s t (Sum.elim p pA) X) s := by
  classical
  ext i j : 1
  simp only [reducedLaplacian,Matrix.submatrix_apply,laplacian,Finset.sum_filter]
  by_cases h : i.1 = j.1
  · simp only [if_pos h]
    convert! mass_mask G s t A hAt p pA X (fun _ v => v = i.1) using 1 <;>
      unfold mass <;> apply Finset.sum_congr rfl <;> intro a _ <;> split_ifs <;> rfl
  · simp only [if_neg h,neg_inj]
    convert! mass_mask G s t A hAt p pA X (fun u v => u = i.1 ∧ v = j.1) using 1 <;>
      unfold mass <;> apply Finset.sum_congr rfl <;> intro a _ <;> split_ifs <;> rfl


open Classical in
private theorem via_trees (hst : s ≠ t) (hAt : ∀ a, A.tail a = t)
    (p : E → R) (pA : F → R)
    (tree : ∀ w : E ⊕ F → R, ((G.addArcs A).reducedLaplacian w s).det =
      ∑ T ∈ Finset.univ.filter (fun T : Finset (E ⊕ F) => (G.addArcs A).IsOutArborescence s T),
        ∏ e ∈ T, w e) :
    G.hamPathPoly p s t =
      ∑ X : Finset (Internal s t),
        (((G.subX s t X).addArcs A).reducedLaplacian (Sum.elim (fun e => p e.1) pA) s).det := by
  classical
  rw [add_path_sum G s t A hAt p pA, path_sum (G.addArcs A) s t hst]
  simp_rw [lap_mask G s t A hAt p pA,tree]
  rw [Finset.sum_comm]
  simp_rw [sum_masks (G.addArcs A) s t]
  rw [← Finset.sum_filter,Finset.filter_filter]

end DHCDetSum

open Polynomial in
theorem solution {V E EA : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype EA] [DecidableEq EA]
    (H : Multidigraph V E) (s t : V) (hst : s ≠ t) (hloop : H.Loopless)
    (_hs : ∀ e, H.head e ≠ s) (_ht : ∀ e, H.tail e ≠ t) (p : E → (ZMod 2)[X])
    (A : Multidigraph V EA) (hAt : ∀ a, A.tail a = t) (hAloop : ∀ a, A.head a ≠ t)
    (pA : EA → (ZMod 2)[X]) :
    H.hamPathPoly p s t =
      ∑ X : Finset (Internal s t),
        (((H.subX s t X).addArcs A).reducedLaplacian (Sum.elim (fun e => p e.1) pA) s).det := by
  classical
  apply DHCDetSum.via_trees H s t A hst hAt p pA
  have loopless : (H.addArcs A).Loopless := by
    rintro (e | a)
    · exact hloop e
    · exact fun he => hAloop a (he.symm.trans (hAt a))
  exact fun w => DirectedHamiltonicity.Main.lemma7 (H.addArcs A) loopless w s

