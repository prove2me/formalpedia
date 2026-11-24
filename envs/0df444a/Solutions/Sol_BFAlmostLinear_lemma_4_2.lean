-- Prove2me | solution 1 for BFAlmostLinear.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-24T11:49:50.567822+00:00
-- url     : https://prove2.me/submissions/677a1512-f0f4-4114-ad6d-2416abde7ac1

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph_I1
import Definitions.Def_BFAlmostLinear_auxGraph

namespace BFAlmostLinear.WGraph

/-- Adding a finite real translates the entire extended real line, including the two infinities. -/
private noncomputable def shiftOrder (c : ℝ) : EReal ≃o EReal where
  toFun x := x + (c : EReal)
  invFun x := x + ((-c : ℝ) : EReal)
  left_inv x := by
    change (x + (c : EReal)) + ((-c : ℝ) : EReal) = x
    rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  right_inv x := by
    change (x + ((-c : ℝ) : EReal)) + (c : EReal) = x
    rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
  map_rel_iff' := (EReal.addLECancellable_coe c).add_le_add_iff_right

theorem pathWeight_reweight {V E : Type} (G : WGraph V E) (ϕ : V → ℝ)
    {P : List E} {s t : V} (hp : G.net.IsPathFrom s t P) :
    pathWeight (G.reweight ϕ).w P = pathWeight G.w P + (ϕ s - ϕ t) := by
  induction P generalizing s with
  | nil => change s = t at hp; simp [hp, pathWeight]
  | cons e P ih =>
    obtain ⟨rfl, hp⟩ := hp
    change (G.w e + ϕ (G.net.tail e) - ϕ (G.net.head e)) + pathWeight (G.reweight ϕ).w P =
      (G.w e + pathWeight G.w P) + _
    rw [ih hp]
    ring

theorem dH_reweight {V E : Type} (G : WGraph V E) (ϕ : V → ℝ) (h : ℕ) (s t : V) :
    (G.reweight ϕ).dH h s t = G.dH h s t + ((ϕ s - ϕ t : ℝ) : EReal) := by
  let f := shiftOrder (ϕ s - ϕ t)
  change (⨅ (P : List E) (_ : G.IsRealWalk s t P ∧ G.hops P ≤ h),
    ((pathWeight (G.reweight ϕ).w P : ℝ) : EReal)) =
    f (⨅ (P : List E) (_ : G.IsRealWalk s t P ∧ G.hops P ≤ h), ((pathWeight G.w P : ℝ) : EReal))
  rw [f.map_iInf]
  congr 1
  funext P
  rw [f.map_iInf]
  apply iInf_congr
  intro hp
  exact (congrArg (fun x : ℝ => (x : EReal)) (pathWeight_reweight G ϕ hp.1.1)).trans (EReal.coe_add _ _)

/-- Each bounded-hop walk has at most h terms that can be negative, even if it repeats arcs. -/
theorem dH_ne_bot_of_frozen {V E : Type} [Fintype E] (G : WGraph V E) (hf : G.Frozen)
    (h : ℕ) (s t : V) : G.dH h s t ≠ ⊥ := by
  classical
  let M := ∑ e, |G.w e|
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hedge (e : E) : -M ≤ G.w e := by
    have hle : |G.w e| ≤ M := Finset.single_le_sum (fun j _ => abs_nonneg (G.w j)) (Finset.mem_univ e)
    linarith [neg_abs_le (G.w e)]
  have walk_bound (P : List E) : -(G.hops P : ℝ) * M ≤ pathWeight G.w P := by
    induction P with
    | nil => simp [hops, pathWeight]
    | cons e P ih =>
      change _ ≤ G.w e + pathWeight G.w P
      cases he : G.neg e with
      | false =>
        have hw : 0 ≤ G.w e := le_of_not_gt (fun hneg => by simpa [he] using hf e hneg)
        simpa [hops, List.countP_cons, he] using (ih.trans (le_add_of_nonneg_left hw))
      | true =>
        simp only [hops, List.countP_cons, he, if_true, Nat.cast_add,
          Nat.cast_one] at *
        linarith [hedge e]
  have lower : (((-(h : ℝ) * M : ℝ)) : EReal) ≤ G.dH h s t := by
    apply le_iInf
    intro P
    apply le_iInf
    intro hp
    apply EReal.coe_le_coe_iff.mpr
    calc
      _ ≤ -(G.hops P : ℝ) * M := mul_le_mul_of_nonneg_right (neg_le_neg (by exact_mod_cast hp.2)) hM
      _ ≤ _ := walk_bound P
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) lower

theorem inX_affine_iff {V E : Type} (G : WGraph V E) (h₁ h₂ : ℕ)
    (ϕ : V → ℝ) (s r t : V) :
    G.InX h₁ h₂ ϕ s r t ↔
      G.dH h₁ s r + G.dH h₂ r t + ((ϕ s - ϕ t : ℝ) : EReal) < 0 := by
  unfold InX
  rw [dH_reweight, dH_reweight]
  have h : (ϕ s - ϕ t) = (ϕ s - ϕ r) + (ϕ r - ϕ t) := by ring
  rw [h, EReal.coe_add, add_add_add_comm]

end BFAlmostLinear.WGraph

namespace BFAlmostLinear.WGraph

open AtomicDynRouting.ResidenceTime

private theorem path_parts {V E : Type} (G : Network V E) (L R : List E) (u v : V) :
    G.IsPathFrom u v (L++R) ↔ ∃ x, G.IsPathFrom u x L ∧ G.IsPathFrom x v R := by
  induction L generalizing u with
  | nil => constructor
           · intro h; exact ⟨u,rfl,h⟩
           · rintro ⟨x,rfl,h⟩; exact h
  | cons e L ih =>
    change (G.tail e = u ∧ G.IsPathFrom (G.head e) v (L++R)) ↔ _
    rw [ih]
    constructor
    · rintro ⟨eq,x,first,last⟩; exact ⟨x,⟨eq,first⟩,last⟩
    · rintro ⟨x,⟨eq,first⟩,last⟩; exact ⟨eq,x,first,last⟩

private theorem drop_nonneg_cycles {V E : Type} [Fintype V] (G : WGraph V E) {P : List E} {u v : V}
    (path : G.net.IsPathFrom u v P) (nonneg : ∀ e ∈ P, 0 ≤ G.w e) :
    ∃ Q, Q.Sublist P ∧ G.net.IsPathFrom u v Q ∧ (Q.map G.net.tail).Nodup ∧
      pathWeight G.w Q ≤ pathWeight G.w P := by
  classical
  induction P generalizing u with
  | nil => exact ⟨[],List.Sublist.refl _,path,by simp,le_rfl⟩
  | cons e P ih =>
    obtain ⟨start,walk⟩ := path
    obtain ⟨Q,sub,route,nd,cheap⟩ := ih walk (fun a ha => nonneg a (List.mem_cons_of_mem _ ha))
    by_cases hit : G.net.tail e ∈ Q.map G.net.tail
    · obtain ⟨a,ha,he⟩ := List.mem_map.mp hit
      obtain ⟨A,B,rfl,_⟩ := List.eq_append_cons_of_mem ha
      have split := (path_parts _ A (a::B) _ _).mp route
      obtain ⟨x,_,endPath⟩ := split
      have keepPath : G.net.IsPathFrom u v (a::B) := ⟨he.trans start,endPath.2⟩
      have sub' : (a::B).Sublist (A++a::B) := List.sublist_append_right ..
      have nA : 0 ≤ pathWeight G.w A := by
        apply List.sum_nonneg
        intro y hy
        obtain ⟨a',hA,rfl⟩ := List.mem_map.mp hy
        exact nonneg _ (List.mem_cons_of_mem _ (sub.subset (List.mem_append_left _ hA)))
      refine ⟨a::B,(sub'.trans sub).cons _,keepPath,nd.sublist (sub'.map _),?_⟩
      simp only [pathWeight,List.map_append,List.sum_append] at cheap nA
      change pathWeight G.w (a::B) ≤ G.w e + pathWeight G.w P
      unfold pathWeight
      linarith [nonneg e (List.Mem.head _)]
    · exact ⟨e::Q,sub.cons_cons _,⟨start,route⟩,List.nodup_cons.mpr ⟨hit,nd⟩,add_le_add_right cheap _⟩

private theorem first_flag {E : Type} (f : E → Bool) (P : List E) :
    (∀ e ∈ P, f e = false) ∨ ∃ A e B, P = A++e::B ∧ f e = true ∧ ∀ a ∈ A, f a = false := by
  induction P with
  | nil => simp
  | cons e P ih =>
    cases he : f e with
    | true => exact Or.inr ⟨[],e,P,rfl,he,by simp⟩
    | false =>
      rcases ih with none | ⟨A,a,B,eq,pos,no⟩
      · exact Or.inl (by simpa [he] using none)
      · exact Or.inr ⟨e::A,a,B,by simp [eq],pos,by simpa [he] using no⟩

/-- Between consecutive flagged arcs a walk can be made simple. This bounds the finite
search space even if a negative mixed cycle exists. The retained list is a subwalk
formed exclusively from original occurrences. -/
theorem bounded_walk_shorten {V E : Type} [Fintype V] (G : WGraph V E) (frozen : G.Frozen)
    (h : ℕ) {P : List E} {u v : V} (path : G.net.IsPathFrom u v P) (budget : G.hops P ≤ h) :
    ∃ Q, Q.Sublist P ∧ G.net.IsPathFrom u v Q ∧ pathWeight G.w Q ≤ pathWeight G.w P ∧
      Q.length ≤ (h+1)*Fintype.card V+h := by
  classical
  have pure {A : List E} {x y : V} (walk : G.net.IsPathFrom x y A) (unflag : ∀ a ∈ A, G.neg a = false) :
      ∃ Q, Q.Sublist A ∧ G.net.IsPathFrom x y Q ∧ pathWeight G.w Q ≤ pathWeight G.w A ∧ Q.length ≤ Fintype.card V := by
    obtain ⟨Q,sub,route,nd,cheap⟩ := drop_nonneg_cycles G walk (fun a ha =>
      le_of_not_gt (fun neg => by have := frozen a neg; simp [unflag a ha] at this))
    have le := Finset.card_le_univ (Q.map G.net.tail).toFinset
    exact ⟨Q,sub,route,cheap,by simpa [List.toFinset_card_of_nodup nd] using le⟩
  induction h generalizing P u v with
  | zero =>
    simp only [zero_add,one_mul,add_zero]
    apply pure path
    intro e he
    have le : G.hops [e] ≤ G.hops P := (List.singleton_sublist.mpr he).countP_le
    cases hf : G.neg e <;> simp_all [hops]
  | succ h ih =>
    rcases first_flag G.neg P with unflag | ⟨A,e,B,rfl,flagged,unflag⟩
    · obtain ⟨Q,sub,route,cheap,len⟩ := pure path unflag
      exact ⟨Q,sub,route,cheap,by nlinarith⟩
    · obtain ⟨x,pre,start,suf⟩ := (path_parts _ A (e::B) _ _).mp path
      have hb : G.hops B ≤ h := by
        simp [hops,List.countP_append,List.countP_cons,flagged] at budget ⊢
        omega
      obtain ⟨L,subL,routeL,cL,lL⟩ := pure pre unflag
      obtain ⟨R,subR,routeR,cR,lR⟩ := ih suf hb
      refine ⟨L++e::R,subL.append (subR.cons_cons _),(path_parts ..).mpr ⟨x,routeL,start,routeR⟩,?_,?_⟩
      · simp only [pathWeight,List.map_append,List.map_cons,List.sum_append,List.sum_cons] at *
        linarith
      · simp only [List.length_append,List.length_cons]
        nlinarith

/-- Each bounded real-walk distance on a finite frozen graph is infinite or attained. -/
theorem dH_attained {V E : Type} [Fintype V] [Fintype E] (G : WGraph V E) (frozen : G.Frozen)
    (h : ℕ) (u v : V) : G.dH h u v = ⊤ ∨
      ∃ P, G.IsRealWalk u v P ∧ G.hops P ≤ h ∧ G.dH h u v = ((pathWeight G.w P : ℝ):EReal) := by
  classical
  let S := {P : List E | G.IsRealWalk u v P ∧ G.hops P ≤ h ∧ P.length ≤ (h+1)*Fintype.card V+h}
  have finite : S.Finite := (List.finite_length_le E _).subset (fun _ hh => hh.2.2)
  have short {P : List E} (walk : G.IsRealWalk u v P) (hp : G.hops P ≤ h) :
      ∃ Q ∈ S, pathWeight G.w Q ≤ pathWeight G.w P := by
    obtain ⟨Q,sub,pq,cheap,lq⟩ := bounded_walk_shorten G frozen h walk.1 hp
    exact ⟨Q,⟨⟨pq,fun e he => walk.2 e (sub.subset he)⟩,(sub.countP_le).trans hp,lq⟩,cheap⟩
  by_cases nonempty : S.Nonempty
  · obtain ⟨Q,hQ,least⟩ := Set.exists_min_image S (pathWeight G.w) finite nonempty
    refine Or.inr ⟨Q,hQ.1,hQ.2.1,le_antisymm (iInf_le_of_le Q (iInf_le_of_le ⟨hQ.1,hQ.2.1⟩ le_rfl)) ?_⟩
    apply le_iInf
    intro P
    apply le_iInf
    intro hp
    obtain ⟨Y,hY,cheap⟩ := short hp.1 hp.2
    exact EReal.coe_le_coe_iff.mpr ((least Y hY).trans cheap)
  · left
    apply top_unique
    apply le_iInf
    intro P
    apply le_iInf
    intro hp
    obtain ⟨Q,hQ,_⟩ := short hp.1 hp.2
    exact (nonempty ⟨Q,hQ⟩).elim

end BFAlmostLinear.WGraph

namespace BFAlmostLinear.WGraph

/-- The weighted sampling theorem applies on the graph visible to mixed bounded-hop searches.
The sampled center set still comes from the designated real negative bridges. -/
def allReal {V E : Type} (G : WGraph V E) : WGraph V E := {G with aux := fun _ => false}

theorem allReal_distance {V E : Type} (G : WGraph V E) (h : ℕ) (s t : V) :
    G.allReal.dH h s t = G.dHt h s t := by
  unfold dH dHt
  simp [IsRealWalk,allReal,hops]

/-- Convert a pairwise bound for actual mixed walks through each center to the canonical
extended-real distance fixing interface. In particular one missing side contributes +∞. -/
theorem fixes_mixed_of_walks {V E : Type} [Fintype V] [Fintype E] (G : WGraph V E) (U : Finset V)
    (ϕ : V → ℝ) (h i j : ℕ) (hi : i ≤ h) (hj : j ≤ h) (valid : G.IsValid ϕ)
    (through : ∀ r ∈ U, ∀ s t (P Q : List E), G.net.IsPathFrom s r P → G.net.IsPathFrom r t Q →
      G.hops P ≤ h → G.hops Q ≤ h → ϕ t ≤ ϕ s + pathWeight G.w P + pathWeight G.w Q) :
    G.allReal.Fixes i j U ϕ := by
  let A := G.allReal.reweight ϕ
  have fr : A.Frozen := by
    intro e neg
    cases hf : G.neg e with
    | true => exact hf
    | false => exact (not_lt_of_ge (valid e hf) neg).elim
  intro r hr s t
  change 0 ≤ A.dH i s r + A.dH j r t
  rcases A.dH_attained fr i s r with l | ⟨P,hP,ihP,l⟩
  · rw [l,EReal.top_add_of_ne_bot (A.dH_ne_bot_of_frozen fr _ _ _)]
    exact le_top
  rcases A.dH_attained fr j r t with rr | ⟨Q,hQ,ihQ,rr⟩
  · rw [rr,l,EReal.coe_add_top]; exact le_top
  have th := through r hr s t P Q hP.1 hQ.1 (ihP.trans hi) (ihQ.trans hj)
  rw [l,rr,← EReal.coe_add,← EReal.coe_zero,EReal.coe_le_coe_iff]
  change 0 ≤ pathWeight (G.reweight ϕ).w P + pathWeight (G.reweight ϕ).w Q
  rw [G.pathWeight_reweight ϕ hP.1,G.pathWeight_reweight ϕ hQ.1]
  linarith

end BFAlmostLinear.WGraph

namespace BFAlmostLinear
namespace PaperAux
open AtomicDynRouting.ResidenceTime

variable {V E : Type} {G : WGraph V E} {level : V → ℕ} {U : Finset V} {h : ℕ}

/-- Parent vertex used for the journal of a child call. -/
def parent : AuxVertex V U h → V
  | .copy _ v => v
  | .tl r | .hd r => r.val

def parentArc : AuxArc G level U h → Option E
  | .copy _ e => some e
  | .fwdStep _ e | .bwdStep _ e => some e.val
  | _ => none

def layerOffset : Layer h → ℤ
  | .base => 0
  | .fwd i => (i.val:ℤ)+1
  | .bwd i => -((i.val:ℤ)+1)

def offset : AuxVertex V U h → ℤ
  | .copy l _ => layerOffset l
  | .tl _ => h
  | .hd _ => -(h:ℤ)

private theorem fwd_offset (k : ℕ) (cap : k≤h) : layerOffset (fwdAt h k)=k := by
  cases k with
  | zero => simp [fwdAt,layerOffset]
  | succ k => simp [fwdAt,show k<h by omega,layerOffset]

private theorem bwd_offset (k : ℕ) (cap : k≤h) : layerOffset (bwdAt h k)=-(k:ℤ) := by
  cases k with
  | zero => simp [bwdAt,layerOffset]
  | succ k => simp [bwdAt,show k<h by omega,layerOffset]

theorem incidence (M : ℝ) (a : AuxArc G level U h) :
    let P := auxGraph G level U h M
    match parentArc a with
    | none => parent (P.net.head a)=parent (P.net.tail a)
    | some e => G.net.tail e=parent (P.net.tail a) ∧ G.net.head e=parent (P.net.head a) := by
  cases a <;> first | rfl | exact ⟨rfl,rfl⟩

theorem price (M : ℝ) (a : AuxArc G level U h) :
    let P := auxGraph G level U h M
    P.w a = (parentArc a).elim 0 G.w +
        M*((offset (P.net.head a):ℝ)-(offset (P.net.tail a):ℝ)) := by
  cases a <;> simp [auxGraph,parentArc,offset,fwd_offset,bwd_offset,
    Nat.le_of_lt,Fin.isLt, Nat.succ_le_of_lt] <;> push_cast <;> ring

/-- The same list of parent references gives incidence and telescoping tolls.
This applies to every runtime height and to every choice of parent weights. -/
theorem project_walk (M : ℝ) {x y : AuxVertex V U h} {P : List (AuxArc G level U h)}
    (walk : (auxGraph G level U h M).net.IsPathFrom x y P) :
    G.net.IsPathFrom (parent x) (parent y) (P.filterMap parentArc) ∧
    pathWeight (auxGraph G level U h M).w P = pathWeight G.w (P.filterMap parentArc) +
        M*((offset y:ℝ)-(offset x:ℝ)) := by
  let A := auxGraph G level U h M
  induction P generalizing x with
  | nil =>
    change x=y at walk
    subst y
    exact ⟨rfl,by simp [pathWeight]⟩
  | cons a P ih =>
    change A.net.tail a=x ∧ A.net.IsPathFrom (A.net.head a) y P at walk
    obtain ⟨rfl,rest⟩ := walk
    obtain ⟨route,cost⟩ := ih rest
    have row := price M a
    have ends := incidence M a
    cases ref : parentArc a with
    | none =>
      simp only [ref] at ends row
      simp only [List.filterMap_cons,ref]
      refine ⟨ends ▸ route,?_⟩
      change A.w a + pathWeight A.w P=_
      change A.w a=0+M*((offset (A.net.head a):ℝ)-(offset (A.net.tail a):ℝ)) at row
      rw [row,cost];ring
    | some e =>
      simp only [ref] at ends row
      simp only [List.filterMap_cons,ref]
      refine ⟨⟨ends.1,ends.2 ▸ route⟩,?_⟩
      change A.w a + pathWeight A.w P=(G.w e + pathWeight G.w (List.filterMap parentArc P))+_
      change A.w a=G.w e+M*((offset (A.net.head a):ℝ)-(offset (A.net.tail a):ℝ)) at row
      rw [row,cost];ring

theorem project_closed (M : ℝ) {x : AuxVertex V U h} {P : List (AuxArc G level U h)}
    (walk : (auxGraph G level U h M).net.IsPathFrom x x P) :
    G.net.IsPathFrom (parent x) (parent x) (P.filterMap parentArc) ∧
      pathWeight G.w (P.filterMap parentArc)=pathWeight (auxGraph G level U h M).w P := by
  obtain ⟨route,price⟩ := project_walk M walk
  exact ⟨route,by simpa using price.symm⟩

end PaperAux
end BFAlmostLinear

namespace BFAlmostLinear.PaperAux


def slot {h : ℕ} : Layer h → Fin (2*h+1)
  | .base => ⟨h,by omega⟩
  | .fwd i => ⟨h+i.val+1,by have := i.isLt;omega⟩
  | .bwd i => ⟨h-(i.val+1),by omega⟩

def readLayer {h : ℕ} (j : Fin (2*h+1)) : Layer h :=
  if low : j.val<h then .bwd ⟨h-1-j.val,by omega⟩
  else if high : h<j.val then .fwd ⟨j.val-h-1,by have := j.isLt;omega⟩
  else .base

def layerEquiv (h : ℕ) : Layer h ≃ Fin (2*h+1) where
  toFun := slot
  invFun := readLayer
  left_inv := by
    intro l
    cases l with
    | base => simp [slot,readLayer]
    | fwd i =>
      have room := i.isLt
      simp [slot,readLayer,show ¬h+i.val+1<h by omega,show h<h+i.val+1 by omega]
      apply Fin.ext
      dsimp;omega
    | bwd i =>
      have room := i.isLt
      change readLayer ⟨h-(i.val+1),_⟩=Layer.bwd i
      unfold readLayer
      rw [dif_pos (show h-(i.val+1)<h by omega)]
      apply congrArg Layer.bwd
      apply Fin.ext
      dsimp;omega
  right_inv := by
    intro j
    apply Fin.ext
    unfold readLayer
    split <;> rename_i low
    · dsimp [slot];omega
    · split <;> dsimp [slot] <;> omega
end BFAlmostLinear.PaperAux

namespace BFAlmostLinear.PaperAux

/-- The physical row ranges, in copy, forward/backward step, forward/backward
wait, and incoming/negative/outgoing gate order. The two filtered lists can
have different lengths and either may be empty. -/
def rows (h e f z k : ℕ) :=
  (2*h+1)*e + (h*f + (h*f + (h*z + (h*z + (k + (k+k))))))

private def prependRows {B : Type} {a b : ℕ} (tail : B ≃ Fin b) :
    (Fin a ⊕ B) ≃ Fin (a+b) :=
  (Equiv.sumCongr (Equiv.refl _) tail).trans finSumFinEquiv

private abbrev Parts (h e f z k : ℕ) :=
  Fin ((2*h+1)*e) ⊕ Fin (h*f) ⊕ Fin (h*f) ⊕ Fin (h*z) ⊕ Fin (h*z) ⊕ Fin k ⊕ Fin k ⊕ Fin k

private def combine (h e f z k : ℕ) : Parts h e f z k ≃ Fin (rows h e f z k) :=
  prependRows (prependRows (prependRows (prependRows (prependRows (prependRows finSumFinEquiv)))))

section
variable {V E : Type} {e h f z k : ℕ} {G : WGraph V E} {level : V → ℕ} {U : Finset V}
variable (flag : Fin f ≃ {i // G.neg i = true}) (zero : Fin z ≃ {v // level v = 0}) (gate : Fin k ≃ U)

private def pieces (edge : E ≃ Fin e) : AuxArc G level U h ≃ Parts h e f z k where
  toFun
    | .copy l j => .inl (finProdFinEquiv (slot l,edge j))
    | .fwdStep i j => .inr (.inl (finProdFinEquiv (i,flag.symm j)))
    | .bwdStep i j => .inr (.inr (.inl (finProdFinEquiv (i,flag.symm j))))
    | .fwdSelf i v => .inr (.inr (.inr (.inl (finProdFinEquiv (i,zero.symm v)))))
    | .bwdSelf i v => .inr (.inr (.inr (.inr (.inl (finProdFinEquiv (i,zero.symm v))))))
    | .gIn r => .inr (.inr (.inr (.inr (.inr (.inl (gate.symm r))))))
    | .gNeg r => .inr (.inr (.inr (.inr (.inr (.inr (.inl (gate.symm r)))))))
    | .gOut r => .inr (.inr (.inr (.inr (.inr (.inr (.inr (gate.symm r)))))))
  invFun
    | .inl r => .copy ((layerEquiv h).symm (finProdFinEquiv.symm r).1) (edge.symm (finProdFinEquiv.symm r).2)
    | .inr (.inl r) => .fwdStep (finProdFinEquiv.symm r).1 (flag (finProdFinEquiv.symm r).2)
    | .inr (.inr (.inl r)) => .bwdStep (finProdFinEquiv.symm r).1 (flag (finProdFinEquiv.symm r).2)
    | .inr (.inr (.inr (.inl r))) => .fwdSelf (finProdFinEquiv.symm r).1 (zero (finProdFinEquiv.symm r).2)
    | .inr (.inr (.inr (.inr (.inl r)))) => .bwdSelf (finProdFinEquiv.symm r).1 (zero (finProdFinEquiv.symm r).2)
    | .inr (.inr (.inr (.inr (.inr (.inl r))))) => .gIn (gate r)
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl r)))))) => .gNeg (gate r)
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr r)))))) => .gOut (gate r)
  left_inv := by
    intro a
    cases a <;> simp [show slot (h:=h)=(layerEquiv h) from rfl]
  right_inv := by
    rintro (r|r|r|r|r|r|r|r) <;> simp [show slot (h:=h)=(layerEquiv h) from rfl] <;> exact finProdFinEquiv.apply_symm_apply r

def packRows (edge : E ≃ Fin e) : AuxArc G level U h ≃ Fin (rows h e f z k) :=
  (pieces flag zero gate edge).trans (combine h e f z k)

end
end BFAlmostLinear.PaperAux

namespace BFAlmostLinear.PaperAux
open AtomicDynRouting.ResidenceTime
noncomputable section
variable {V E : Type} {G : WGraph V E} {level : V → ℕ} {U : Finset V} {h : ℕ}
variable (M : ℝ) (p : AuxVertex V U h → ℝ)

/-- The child solver enforces feasibility on precisely the arcs allowed by
the recursive problem in Lemma 4.2, including unflagged auxiliary arcs. -/
def Feasible (G : WGraph V E) (level : V → ℕ) (U : Finset V) (h : ℕ) (M : ℝ)
    (p : AuxVertex V U h → ℝ) : Prop :=
  let A := auxGraph G level U h M
  ∀ a,¬(A.aux a=true ∧ A.neg a=true) → p (A.net.head a) ≤ p (A.net.tail a)+A.w a

private def forward (k : ℕ) (v : V) := p (.copy (fwdAt h k) v)-(k:ℝ)*M
private def backward (k : ℕ) (v : V) := p (.copy (bwdAt h k) v)+(k:ℝ)*M

variable (ok : Feasible G level U h M p)
include ok

private theorem copied (l : Layer h) (e : E) (clear : G.neg e=false) :
    p (.copy l (G.net.head e))≤p (.copy l (G.net.tail e))+G.w e := by
  exact ok (.copy l e) (by simp [auxGraph,clear])

private theorem forward_step (i : Fin h) (e : E) (flag : G.neg e=true) :
    forward M p (i.val+1) (G.net.head e)≤forward M p i.val (G.net.tail e)+G.w e := by
  have bound := ok (.fwdStep i ⟨e,flag⟩) (by simp [auxGraph])
  change p (.copy (fwdAt h (i.val+1)) (G.net.head e)) ≤
    p (.copy (fwdAt h i.val) (G.net.tail e))+(M+G.w e) at bound
  simp only [forward,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
  linarith

private theorem backward_step (i : Fin h) (e : E) (flag : G.neg e=true) :
    backward M p i.val (G.net.head e)≤backward M p (i.val+1) (G.net.tail e)+G.w e := by
  have bound := ok (.bwdStep i ⟨e,flag⟩) (by simp [auxGraph])
  change p (.copy (bwdAt h i.val) (G.net.head e)) ≤
    p (.copy (bwdAt h (i.val+1)) (G.net.tail e))+(M+G.w e) at bound
  simp only [backward,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
  linarith

private theorem forward_walk {s t : V} {P : List E} (route : G.net.IsPathFrom s t P)
    (j : ℕ) (fits : j+G.hops P≤h) :
    forward M p (j+G.hops P) t ≤ forward M p j s+pathWeight G.w P := by
  induction P generalizing s j with
  | nil =>
    change s=t at route
    subst s
    simp [WGraph.hops,pathWeight]
  | cons e P ih =>
    obtain ⟨sEq,rest⟩ := route
    subst s
    cases flag : G.neg e with
    | false =>
      have hops : G.hops (e::P)=G.hops P := by simp [WGraph.hops,flag]
      rw [hops] at fits ⊢
      have next := ih rest j fits
      have first := copied M p ok (fwdAt h j) e flag
      unfold forward at next ⊢
      change _ ≤ _+(G.w e+pathWeight G.w P)
      linarith
    | true =>
      have hops : G.hops (e::P)=G.hops P+1 := by simp [WGraph.hops,flag]
      rw [hops] at fits ⊢
      have next := ih rest (j+1) (by omega)
      have first := forward_step M p ok ⟨j,by omega⟩ e flag
      change forward M p (j+1) (G.net.head e)≤forward M p j (G.net.tail e)+G.w e at first
      rw [show j+(G.hops P+1)=j+1+G.hops P by omega]
      change _ ≤ _+(G.w e+pathWeight G.w P)
      linarith

private theorem backward_walk {s t : V} {P : List E} (route : G.net.IsPathFrom s t P)
    (j : ℕ) (fits : j+G.hops P≤h) :
    backward M p j t ≤ backward M p (j+G.hops P) s+pathWeight G.w P := by
  induction P generalizing s with
  | nil =>
    change s=t at route
    subst s
    simp [WGraph.hops,pathWeight]
  | cons e P ih =>
    obtain ⟨sEq,rest⟩ := route
    subst s
    cases flag : G.neg e with
    | false =>
      have hops : G.hops (e::P)=G.hops P := by simp [WGraph.hops,flag]
      rw [hops] at fits ⊢
      have next := ih rest fits
      have first := copied M p ok (bwdAt h (j+G.hops P)) e flag
      unfold backward at next ⊢
      change _ ≤ _+(G.w e+pathWeight G.w P)
      linarith
    | true =>
      have hops : G.hops (e::P)=G.hops P+1 := by simp [WGraph.hops,flag]
      rw [hops] at fits ⊢
      have next := ih rest (by omega)
      have first := backward_step M p ok ⟨j+G.hops P,by omega⟩ e flag
      change backward M p (j+G.hops P) (G.net.head e) ≤ backward M p ((j+G.hops P)+1) (G.net.tail e)+G.w e at first
      rw [← Nat.add_assoc]
      change _ ≤ _+(G.w e+pathWeight G.w P)
      linarith

private theorem pad {r : V} (original : level r=0) {i j : ℕ} (ij : i≤j) (fits : j≤h) :
    forward M p j r ≤ forward M p i r ∧ backward M p i r ≤ backward M p j r := by
  induction ij with
  | refl => exact ⟨le_rfl,le_rfl⟩
  | @step j _ ih =>
    obtain ⟨f,b⟩ := ih (by omega)
    let idx : Fin h := ⟨j,by omega⟩
    have a := ok (.fwdSelf idx ⟨r,original⟩) (by simp [auxGraph])
    have c := ok (.bwdSelf idx ⟨r,original⟩) (by simp [auxGraph])
    change p (.copy (fwdAt h (j+1)) r) ≤ p (.copy (fwdAt h j) r)+M at a
    change p (.copy (bwdAt h j) r) ≤ p (.copy (bwdAt h (j+1)) r)+M at c
    simp only [forward,backward,Nat.cast_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] at *
    constructor <;> linarith

private theorem gate_bridge (r : U) : backward M p h r≤forward M p h r := by
  have a := ok (.gIn r) (by simp [auxGraph])
  have b := ok (.gNeg r) (by simp [auxGraph])
  have c := ok (.gOut r) (by simp [auxGraph])
  change p (.tl r)≤p (.copy (fwdAt h h) r)+0 at a
  change p (.hd r)≤p (.tl r)+ -(2*(h:ℝ)*M) at b
  change p (.copy (bwdAt h h) r)≤p (.hd r)+0 at c
  unfold backward forward
  linarith

theorem through_walks (original : ∀ r∈U,level r=0) :
    let ψ : V → ℝ := fun v => p (.copy .base v)
    ∀ r∈U,∀ s t (P Q : List E),G.net.IsPathFrom s r P → G.net.IsPathFrom r t Q →
      G.hops P≤h → G.hops Q≤h → ψ t≤ψ s+pathWeight G.w P+pathWeight G.w Q := by
  let ψ : V → ℝ := fun v => p (.copy .base v)
  change ∀ r∈U,∀ s t (P Q : List E),G.net.IsPathFrom s r P → G.net.IsPathFrom r t Q →
    G.hops P≤h → G.hops Q≤h → ψ t≤ψ s+pathWeight G.w P+pathWeight G.w Q
  intro r mem s t P Q inPath outPath inH outH
  obtain ⟨a,_⟩ := pad M p ok (original r mem) inH le_rfl
  obtain ⟨_,b⟩ := pad M p ok (original r mem) outH le_rfl
  have inBound := forward_walk M p ok inPath 0 (by omega)
  have outBound := backward_walk M p ok outPath 0 (by omega)
  have gate := gate_bridge M p ok ⟨r,mem⟩
  change backward M p h r ≤ forward M p h r at gate
  simp only [Nat.zero_add] at inBound outBound
  have f0 (x : V) : forward M p 0 x=ψ x := by simp [forward,ψ,fwdAt]
  have b0 (x : V) : backward M p 0 x=ψ x := by simp [backward,ψ,bwdAt]
  rw [f0] at inBound
  rw [b0] at outBound
  linarith


/-- Restrict a feasible recursive answer to the central layer. The two hop
bounds may be chosen separately, as required for the forward and backward
searches in section 4.3. -/
theorem fixes_from_return [Fintype V] [Fintype E] (original : ∀ r∈U,level r=0)
    (i j : ℕ) (hi : i≤h) (hj : j≤h) :
    let ψ : V → ℝ := fun v => p (.copy .base v)
    G.IsValid ψ ∧ G.allReal.Fixes i j U ψ := by
  let ψ : V → ℝ := fun v => p (.copy .base v)
  have valid : G.IsValid ψ := by
    intro e flag
    have first := copied M p ok .base e flag
    change 0≤G.w e + p (.copy .base (G.net.tail e)) - p (.copy .base (G.net.head e))
    linarith
  exact ⟨valid,G.fixes_mixed_of_walks U ψ h i j hi hj valid (through_walks M p ok original)⟩

end
end BFAlmostLinear.PaperAux

namespace BFAlmostLinear.PaperAux
open AtomicDynRouting.ResidenceTime
noncomputable section
variable {V E : Type} {G : WGraph V E} {level : V → ℕ} {U : Finset V} {h : ℕ}
variable (M : ℝ)
local notation "A" => auxGraph G level U h M
local notation "L" => auxLevel (U:=U) (h:=h) level

theorem new_row_level (parents : G.I4 level) (centers : ∀ r∈U,level r=0)
    (a : AuxArc G level U h) (newRow : ∀ l e,a≠.copy l e) :
    L ((A).net.tail a)=0 ∧ L ((A).net.head a)=0 := by
  cases a with
  | copy l e => exact (newRow l e rfl).elim
  | fwdStep _ e | bwdStep _ e => exact parents e e.property
  | fwdSelf _ v | bwdSelf _ v => exact ⟨v.property,v.property⟩
  | gIn r => exact ⟨centers r r.property,rfl⟩
  | gNeg r => exact ⟨rfl,rfl⟩
  | gOut r => exact ⟨rfl,centers r r.property⟩

theorem flag_real (a : AuxArc G level U h) :
    ((A).neg a=true ∧ (A).aux a=false) ↔ ∃ r : U,a=.gNeg r := by
  cases a <;> simp [auxGraph]
  exact fun flag _ => flag

theorem invariant_one (parentInv : G.I1) : (A).I1 := by
  constructor
  · intro a b flagA flagB touch
    cases a <;> cases b <;> simp [auxGraph] at flagA flagB touch ⊢
    · rcases touch with ⟨l,eq⟩|⟨l,eq⟩|⟨l,eq⟩|⟨l,eq⟩
      · exact ⟨l,parentInv.1 _ _ flagA flagB (.inl eq)⟩
      · exact ⟨l,parentInv.1 _ _ flagA flagB (.inr (.inl eq))⟩
      · exact ⟨l,parentInv.1 _ _ flagA flagB (.inr (.inr (.inl eq)))⟩
      · exact ⟨l,parentInv.1 _ _ flagA flagB (.inr (.inr (.inr eq)))⟩
    · exact touch
  · intro a flag real
    obtain ⟨r,rfl⟩ := (flag_real M a).mp ⟨flag,real⟩
    constructor <;> intro b allowed touch <;> cases b <;> simp_all [auxGraph]

theorem invariant_two (parentInv : G.I2 level) (negLevel : G.I4 level) (centers : ∀ r∈U,level r=0) :
    (A).I2 L := by
  intro a same
  by_cases copied : ∃ l e,a=.copy l e
  · obtain ⟨l,e,rfl⟩ := copied
    exact parentInv e same
  · exact (new_row_level M negLevel centers a (fun l e eq => copied ⟨l,e,eq⟩)).1

theorem invariant_four (parentInv : G.I4 level) : (A).I4 L := by
  intro a flag
  cases a <;> simp [auxGraph,auxLevel] at flag ⊢
  exact parentInv _ flag

private theorem lift_copy_path (l : Layer h) {s t : V} (P : List E) (walk : G.net.IsPathFrom s t P) :
    (A).net.IsPathFrom (.copy l s) (.copy l t) (P.map (AuxArc.copy l)) := by
  induction P generalizing s with
  | nil => exact congrArg (AuxVertex.copy l) walk
  | cons a P ih =>
    exact ⟨congrArg (AuxVertex.copy l) walk.1,ih walk.2⟩

theorem invariant_three (parentInv : G.I3 level) (negLevel : G.I4 level) (centers : ∀ r∈U,level r=0) :
    (A).I3 L := by
  intro a b clearA clearB join positive incoming outgoing
  have positive' : 0<L ((A).net.tail b) := join ▸ positive
  have takeCopy (x : AuxArc G level U h) (pos : 0<L ((A).net.head x) ∨ 0<L ((A).net.tail x)) :
      ∃ l e,x=.copy l e := by
    by_contra no
    obtain ⟨left,right⟩ := new_row_level M negLevel centers x (fun l e eq => no ⟨l,e,eq⟩)
    omega
  obtain ⟨l,e,rfl⟩ := takeCopy a (.inl positive)
  obtain ⟨l',f,rfl⟩ := takeCopy b (.inr positive')
  change AuxVertex.copy (U:=U) l (G.net.head e)=.copy l' (G.net.tail f) at join
  obtain ⟨rfl,ef⟩ := AuxVertex.copy.inj join
  change (G.aux e || G.neg e)=false at clearA
  change (G.aux f || G.neg f)=false at clearB
  obtain ⟨P,walk,usable,hops,price,below,last,first⟩ :=
    parentInv e f (Bool.or_eq_false_iff.mp clearA).1 (Bool.or_eq_false_iff.mp clearB).1 ef positive incoming outgoing
  refine ⟨P.map (AuxArc.copy l),lift_copy_path M l P walk,?_,?_,?_,?_,?_,?_⟩
  · intro a mem
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    change (G.aux x || G.neg x)=false ∨ G.neg x=true
    rcases usable x hx with allow|flag
    · cases G.neg x <;> simp [allow]
    · exact .inr flag
  · simpa [WGraph.hops,auxGraph,Function.comp_def] using hops
  · simpa [pathWeight,auxGraph,Function.comp_def] using price
  · intro a mem
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    exact below x hx
  · intro a atEnd
    rw [List.getLast?_map,Option.map_eq_some_iff] at atEnd
    obtain ⟨x,atX,rfl⟩ := atEnd
    exact last x atX
  · intro a atHead
    rw [List.head?_map,Option.map_eq_some_iff] at atHead
    obtain ⟨x,atX,rfl⟩ := atHead
    exact first x atX

end
end BFAlmostLinear.PaperAux

namespace BFAlmostLinear.PaperAux
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : WGraph V E) (level : V → ℕ) (U : Finset V) (h : ℕ)

theorem card_vertices :
    Nat.card (AuxVertex V U h)=(2*h+1)*Fintype.card V+2*U.card := by
  classical
  let types : AuxVertex V U h ≃ (Fin (2*h+1) × V) ⊕ (U ⊕ U) :=
    { toFun := fun | .copy l v => .inl (layerEquiv h l,v) | .tl r => .inr (.inl r) | .hd r => .inr (.inr r)
      invFun := fun | .inl (j,v) => .copy ((layerEquiv h).symm j) v | .inr (.inl r) => .tl r | .inr (.inr r) => .hd r
      left_inv := by intro a;cases a <;> simp
      right_inv := by rintro (⟨j,v⟩|r|r) <;> simp }
  rw [Nat.card_congr types,Nat.card_eq_fintype_card]
  simp [two_mul]

theorem card_arcs :
    Nat.card (AuxArc G level U h)=(2*h+1)*Fintype.card E+
      2*h*(Finset.univ.filter fun i => G.neg i=true).card+
      2*h*(Finset.univ.filter fun v => level v=0).card+3*U.card := by
  classical
  let ids := packRows (G:=G) (level:=level) (U:=U) (h:=h)
    ((Fintype.equivFin {i // G.neg i=true}).symm)
    ((Fintype.equivFin {v // level v=0}).symm)
    ((Fintype.equivFin U).symm) (Fintype.equivFin E)
  rw [Nat.card_congr ids,Nat.card_eq_fintype_card,Fintype.card_fin]
  have cut : (Finset.univ.filter fun v : V => v∈U)=U := by ext v;simp
  simp only [rows,Fintype.card_coe,Fintype.card_subtype,cut]
  ring

end
end BFAlmostLinear.PaperAux

open BFAlmostLinear

open Classical in
/-- **Lemma 4.2**, p.13, with Subclaims 4.3–4.5, pp.15–16. "There is an algorithm that, given a graph G with vertex
partition S_0 ⊔ S_1 ⊔ · · · ⊔ S_t that satisfies invariants (I1)–(I4), a subset U ⊂ N of its negative vertices, and a hop
bound h, either reports a negative cycle in G or finds a valid reweighting ϕ such that after reweighting,
d̃^h(s, r) + d̃^h(r, t) ≥ 0 ∀r ∈ U, ∀s, t ∈ V. The algorithm computes this reweighting by solving the single-source
shortest path problem on an auxiliary graph G′ …"

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Lemma 4.2, p.13, Subclaims 4.3, 4.4, 4.5, pp.15–16.

**Formalization Note.** The algorithm is "solve SSSP on `auxGraph`". The statement has no machine; it states the two
outcomes on the explicit `G′` of pp.13–14, for every hop bound `h` (at `h = 0` the construction is one copy and
the gadget) and `M ≥ 0` above the absolute weight of each flagged arc:
* (a) If `ϕ` on `V(G′)` is nonnegative on every arc other than the auxiliary negatives, then `v ↦ ϕ(v₀)` is valid on
  `G`, Subclaim 4.3 holds, and `d̃^h + d̃^h ≥ 0` after the reweighting.
* (b) Subclaim 4.4: a closed walk of negative weight on the other arcs of `G′` gives a closed walk in `G` of the same
  weight, where auxiliary arcs may occur.
* (c) `G′` satisfies (I1)–(I4), with the levels of the copies and level `0` at each new vertex. Also Subclaim 4.5.
* (d) Exact counts. Printed: "O(h) copies", "O(|V(G)|) extra vertices, O(h|E(G)|) extra edges, and |U| real negative
  edges". The self edges are `2h |S₀|`, which the printed `O(h|E(G)|)` misses when `|S₀| > |E|` while the proof
  says `O(nh)`; the exact count avoids it. The data structure of Lemma 3.1 is not modeled. -/
theorem solution {V E : Type} [Fintype V] [Fintype E] (G : WGraph V E) (level : V → ℕ)
    (U : Finset V) (h : ℕ) (M : ℝ) (hU : U ⊆ G.negVertices) (hF : G.Frozen)
    (hM0 : 0 ≤ M) (hM : ∀ e, G.neg e = true → |G.w e| < M)
    (hI1 : G.I1) (hI2 : G.I2 level) (hI3 : G.I3 level) (hI4 : G.I4 level) :
    let G' := auxGraph G level U h M
    -- (a) a potential on `G′` gives a valid reweighting of `G`, with Subclaim 4.3
    (∀ ϕ' : AuxVertex V U h → ℝ,
      (∀ a, ¬ (G'.aux a = true ∧ G'.neg a = true) → 0 ≤ (G'.reweight ϕ').w a) →
      let ψ : V → ℝ := fun v => ϕ' (.copy .base v)
      G.IsValid ψ ∧
      (∀ r ∈ U, ∀ s t, ((ψ t - ψ s : ℝ) : EReal) ≤ G.dHt h s r + G.dHt h r t) ∧
      (∀ r ∈ U, ∀ s t, 0 ≤ (G.reweight ψ).dHt h s r + (G.reweight ψ).dHt h r t)) ∧
    -- (b) Subclaim 4.4
    (∀ (v' : AuxVertex V U h) (P' : List (AuxArc G level U h)),
      G'.net.IsPathFrom v' v' P' → (∀ a ∈ P', ¬ (G'.aux a = true ∧ G'.neg a = true)) →
      pathWeight G'.w P' < 0 →
      ∃ (v : V) (P : List E), G.net.IsPathFrom v v P ∧ pathWeight G.w P = pathWeight G'.w P') ∧
    -- (c) the invariants of `G′`, and Subclaim 4.5
    (G'.I1 ∧ G'.I2 (auxLevel level) ∧ G'.I3 (auxLevel level) ∧ G'.I4 (auxLevel level)) ∧
    (∀ a, (∀ l e, a ≠ AuxArc.copy l e) →
      auxLevel level (G'.net.tail a) = 0 ∧ auxLevel level (G'.net.head a) = 0) ∧
    -- (d) sizes, and the real negative arcs
    Nat.card (AuxVertex V U h) = (2 * h + 1) * Fintype.card V + 2 * U.card ∧
    Nat.card (AuxArc G level U h) =
      (2 * h + 1) * Fintype.card E +
        2 * h * (Finset.univ.filter fun e => G.neg e = true).card +
        2 * h * (Finset.univ.filter fun v => level v = 0).card + 3 * U.card ∧
    (∀ a, (G'.neg a = true ∧ G'.aux a = false) ↔ ∃ r : U, a = AuxArc.gNeg r) := by
  classical
  dsimp only
  have centers (r : V) (hr : r∈U) : level r=0 := by
    have mem := hU hr
    obtain ⟨e,eq,flag,_⟩ := (Finset.mem_filter.mp mem).2
    exact eq ▸ (hI4 e flag).1
  refine ⟨?_,?_,⟨PaperAux.invariant_one M hI1,PaperAux.invariant_two M hI2 hI4 centers,
    PaperAux.invariant_three M hI3 hI4 centers,PaperAux.invariant_four M hI4⟩,
    PaperAux.new_row_level M hI4 centers,PaperAux.card_vertices U h,
    PaperAux.card_arcs G level U h,PaperAux.flag_real M⟩
  · intro p admissible
    let ψ : V → ℝ := fun v => p (.copy .base v)
    have ok : PaperAux.Feasible G level U h M p := by
      intro a allowed
      have bound := admissible a allowed
      change 0≤(auxGraph G level U h M).w a+p ((auxGraph G level U h M).net.tail a)-p ((auxGraph G level U h M).net.head a) at bound
      linarith
    obtain ⟨valid,mixed⟩ := PaperAux.fixes_from_return M p ok centers h h le_rfl le_rfl
    refine ⟨valid,?_,?_⟩
    · intro r hr s t
      let B := G.allReal
      have stable : B.Frozen := hF
      rw [← G.allReal_distance h s r,← G.allReal_distance h r t]
      change ((ψ t-ψ s:ℝ):EReal)≤B.dH h s r+B.dH h r t
      rcases B.dH_attained stable h s r with miss | ⟨P,pathP,hopP,lp⟩
      · rw [miss,EReal.top_add_of_ne_bot (B.dH_ne_bot_of_frozen stable _ _ _)]
        exact le_top
      rcases B.dH_attained stable h r t with miss | ⟨Q,pathQ,hopQ,lq⟩
      · rw [lp,miss,EReal.coe_add_top]
        exact le_top
      have walks := PaperAux.through_walks M p ok centers r hr s t P Q pathP.1 pathQ.1 hopP hopQ
      rw [lp,lq,←EReal.coe_add,EReal.coe_le_coe_iff]
      change ψ t-ψ s≤pathWeight G.w P+pathWeight G.w Q
      change ψ t≤ψ s+pathWeight G.w P+pathWeight G.w Q at walks
      linarith
    · intro r hr s t
      rw [← (G.reweight ψ).allReal_distance h s r,← (G.reweight ψ).allReal_distance h r t]
      exact mixed r hr s t
  · intro start walk route _ _
    exact ⟨PaperAux.parent start,walk.filterMap PaperAux.parentArc,PaperAux.project_closed M route⟩
