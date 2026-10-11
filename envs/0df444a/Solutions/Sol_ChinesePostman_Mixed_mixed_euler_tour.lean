-- Prove2me | solution 1 for ChinesePostman.Mixed.mixed_euler_tour
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T04:20:46.009329+00:00
-- url     : https://prove2.me/submissions/53840503-e51a-41f0-aa3c-123b47ab97b8

import Mathlib
import Definitions.Def_ChinesePostman_Mixed_Setting

-- BEGIN COMPLETE MODULE OrientationBasic
section

open Finset
namespace ChinesePostman.Mixed.Proof
variable {V E : Type*}

def orientedTail (a b : E → V) (flip : E → Bool) (e : E) : V :=
  if flip e then b e else a e

def orientedHead (a b : E → V) (flip : E → Bool) (e : E) : V :=
  if flip e then a e else b e

lemma oriented_endpoints (a b : E → V) (flip : E → Bool) (e : E) :
    (orientedTail a b flip e=a e ∧ orientedHead a b flip e=b e) ∨
    (orientedTail a b flip e=b e ∧ orientedHead a b flip e=a e) := by
  cases h : flip e <;> simp [orientedTail,orientedHead,h]

lemma oriented_loopless (a b : E → V) (hab : ∀e,a e≠b e) (flip : E → Bool) (e : E) :
    orientedTail a b flip e≠orientedHead a b flip e := by
  cases h : flip e <;> simp [orientedTail,orientedHead,h,hab e,(hab e).symm]

variable [DecidableEq V] [DecidableEq E]

def incidentDegree (a b : E → V) (S : Finset E) (v : V) : ℕ :=
  (S.filter (fun e => a e=v ∨ b e=v)).card

def outDegree (a : E → V) (S : Finset E) (v : V) : ℕ :=
  (S.filter (fun e => a e=v)).card

lemma incidentDegree_sdiff (a b : E → V) {S C : Finset E} (hCS : C ⊆ S) (v : V) :
    incidentDegree a b S v = incidentDegree a b C v + incidentDegree a b (S \ C) v := by
  unfold incidentDegree
  have he : S.filter (fun e => a e=v ∨ b e=v) =
      C.filter (fun e => a e=v ∨ b e=v) ∪ (S \ C).filter (fun e => a e=v ∨ b e=v) := by
    ext e
    simp only [mem_filter,mem_union,mem_sdiff]
    constructor
    · rintro ⟨hs,h⟩
      by_cases hc : e∈C
      · exact Or.inl ⟨hc,h⟩
      · exact Or.inr ⟨⟨hs,hc⟩,h⟩
    · rintro (⟨hc,h⟩|⟨⟨hs,_⟩,h⟩)
      · exact ⟨hCS hc,h⟩
      · exact ⟨hs,h⟩
  rw [he,card_union_of_disjoint]
  exact disjoint_left.mpr fun e hc hs => (mem_sdiff.mp (mem_filter.mp hs).1).2 (mem_filter.mp hc).1

lemma incidentDegree_insert (a b : E → V) {S : Finset E} {e : E} (he : e∉S)
    (hab : a e≠b e) (v : V) :
    incidentDegree a b (insert e S) v = incidentDegree a b S v +
      (if a e=v then 1 else 0) + (if b e=v then 1 else 0) := by
  unfold incidentDegree
  by_cases ha : a e=v <;> by_cases hb : b e=v
  · exact (hab (ha.trans hb.symm)).elim
  · simp [filter_insert,ha,hb,he,mem_filter,Nat.add_comm]
  · simp [filter_insert,ha,hb,he,mem_filter,Nat.add_comm]
  · simp [filter_insert,ha,hb]

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE OrientationBasic

-- BEGIN COMPLETE MODULE LabelWalk
section

namespace ChinesePostman.Mixed.Proof

variable {V E : Type}

inductive LabelWalk (step : E → V → V → Prop) : V → V → Type
  | nil (v : V) : LabelWalk step v v
  | cons {u v w : V} (e : E) (h : step e u v) (p : LabelWalk step v w) : LabelWalk step u w

namespace LabelWalk
variable {step : E → V → V → Prop} {u v w z : V}

def edges : {u v : V} → LabelWalk step u v → List E
  | _, _, .nil _ => []
  | _, _, .cons e _ p => e :: p.edges

def nodes : {u v : V} → LabelWalk step u v → List V
  | _, _, .nil x => [x]
  | x, _, .cons _ _ p => x :: p.nodes

def append : {u v w : V} → LabelWalk step u v → LabelWalk step v w → LabelWalk step u w
  | _, _, _, .nil _, q => q
  | _, _, _, .cons e h p, q => .cons e h (p.append q)

@[simp] lemma edges_nil (v : V) : (nil (step:=step) v).edges=[] := rfl
@[simp] lemma edges_cons (e : E) (h : step e u v) (p : LabelWalk step v w) :
    (cons e h p).edges=e::p.edges := rfl
@[simp] lemma nodes_nil (v : V) : (nil (step:=step) v).nodes=[v] := rfl
@[simp] lemma nodes_cons (e : E) (h : step e u v) (p : LabelWalk step v w) :
    (cons e h p).nodes=u::p.nodes := rfl

@[simp] lemma edges_append (p : LabelWalk step u v) (q : LabelWalk step v w) :
    (p.append q).edges=p.edges++q.edges := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [append,ih]

@[simp] lemma nodes_length (p : LabelWalk step u v) : p.nodes.length=p.edges.length+1 := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih]

@[simp] lemma nodes_head (p : LabelWalk step u v) : p.nodes.head?=some u := by cases p <;> rfl
@[simp] lemma nodes_last (p : LabelWalk step u v) : p.nodes.getLast?=some v := by
  induction p with
  | nil => rfl
  | cons e h p ih =>
    simp only [nodes_cons,List.getLast?_cons,ih,Option.getD_some]

lemma start_mem (p : LabelWalk step u v) : u∈p.nodes := by cases p <;> simp
lemma end_mem (p : LabelWalk step u v) : v∈p.nodes := by
  induction p with
  | nil => simp
  | cons e h p ih => exact List.mem_cons_of_mem _ ih

@[simp] lemma nodes_zero (p : LabelWalk step u v) :
    p.nodes[0]'(by rw [p.nodes_length]; omega)=u := by cases p <;> rfl

lemma step_at (p : LabelWalk step u v) (i : ℕ) (hi : i<p.edges.length) :
    step p.edges[i] (p.nodes[i]'(by rw [p.nodes_length]; omega))
      (p.nodes[i+1]'(by rw [p.nodes_length]; omega)) := by
  induction p generalizing i with
  | nil => simp at hi
  | cons e h p ih =>
    cases i with
    | zero => simpa using h
    | succ i => simpa using ih i (by simpa using hi)

lemma split_at_node (p : LabelWalk step u v) {x : V} (hx : x∈p.nodes) :
    ∃ a : LabelWalk step u x, ∃ b : LabelWalk step x v,
      p.edges=a.edges++b.edges := by
  induction p with
  | nil y =>
    simp only [nodes_nil,List.mem_singleton] at hx
    subst x
    exact ⟨nil y,nil y,rfl⟩
  | @cons u y v e h p ih =>
    rcases List.mem_cons.mp hx with he | hx
    · subst x
      exact ⟨nil u,cons e h p,rfl⟩
    · obtain ⟨a,b,hab⟩ := ih hx
      exact ⟨cons e h a,b,by simp [hab]⟩

lemma nodup_length_le [Fintype E] (p : LabelWalk step u v) (hp : p.edges.Nodup) :
    p.edges.length≤Fintype.card E := List.Nodup.length_le_card hp

end LabelWalk
end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE LabelWalk

-- BEGIN COMPLETE MODULE UndirectedTrail
section

open Finset
namespace ChinesePostman.Mixed.Proof
variable {V E : Type} [DecidableEq V] [DecidableEq E]

def undirStep (a b : E → V) (e : E) (u v : V) : Prop :=
  (a e=u ∧ b e=v) ∨ (a e=v ∧ b e=u)

abbrev UndirWalk (a b : E → V) (S : Finset E) (u v : V) :=
  LabelWalk (fun e u v => e∈S ∧ undirStep a b e u v) u v

omit [DecidableEq V] in
lemma undirWalk_edges_subset {a b : E → V} {S : Finset E} {u v : V}
    (p : UndirWalk a b S u v) : p.edges.toFinset ⊆ S := by
  intro e he
  have he' : e∈p.edges := List.mem_toFinset.mp he
  induction p with
  | nil => simp at he'
  | cons d h p ih =>
    rcases List.mem_cons.mp he' with rfl | he'
    · exact h.1
    · exact ih (List.mem_toFinset.mpr he') he'

lemma undirWalk_incidence {a b : E → V} (hab : ∀e,a e≠b e) {S : Finset E} {u v : V}
    (p : UndirWalk a b S u v) (hp : p.edges.Nodup) (x : V) :
    incidentDegree a b p.edges.toFinset x + (if u=x then 1 else 0) + (if v=x then 1 else 0) =
      2*p.nodes.count x := by
  induction p with
  | nil u =>
    by_cases hu : u=x <;> simp [incidentDegree,hu,eq_comm]
  | @cons u y v e he p ih =>
    have hn := List.nodup_cons.mp hp
    have hh := ih hn.2
    rw [LabelWalk.edges_cons,List.toFinset_cons,incidentDegree_insert a b (by simpa using hn.1) (hab e)]
    rcases he.2 with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simp only [ha,hb]
      by_cases hu : u=x <;> by_cases hy : y=x <;> by_cases hv : v=x <;>
        simp [hu,hy,hv] at hh ⊢ <;> omega
    · simp only [ha,hb]
      by_cases hu : u=x <;> by_cases hy : y=x <;> by_cases hv : v=x <;>
        simp [hu,hy,hv] at hh ⊢ <;> omega

lemma undirWalk_closed_even {a b : E → V} (hab : ∀e,a e≠b e) {S : Finset E} {u : V}
    (p : UndirWalk a b S u u) (hp : p.edges.Nodup) (x : V) :
    Even (incidentDegree a b p.edges.toFinset x) := by
  have hh := undirWalk_incidence hab p hp x
  by_cases hu : u=x
  · simp only [if_pos hu] at hh
    refine ⟨p.nodes.count x-1,?_⟩
    omega
  · simp only [if_neg hu] at hh
    exact ⟨p.nodes.count x,by omega⟩

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE UndirectedTrail

-- BEGIN COMPLETE MODULE LabelWalkMax
section

namespace ChinesePostman.Mixed.Proof
namespace LabelWalk
variable {V E : Type} {step : E → V → V → Prop} {u v w : V}

lemma length_le_card [DecidableEq E] (p : LabelWalk step u v) (F : Finset E)
    (hp : p.edges.Nodup) (hF : ∀e∈p.edges,e∈F) : p.edges.length≤F.card := by
  rw [←List.toFinset_card_of_nodup hp]
  exact Finset.card_le_card (fun e he=>hF e (List.mem_toFinset.mp he))

lemma exists_longest [DecidableEq E] (step : E → V → V → Prop) (F : Finset E) (u : V) :
    ∃v,∃p : LabelWalk step u v,p.edges.Nodup ∧ (∀e∈p.edges,e∈F) ∧
      ∀w (q : LabelWalk step u w), q.edges.Nodup → (∀e∈q.edges,e∈F) →
        q.edges.length≤p.edges.length := by
  classical
  let P : ℕ → Prop := fun n=>∃v,∃p : LabelWalk step u v,
    p.edges.Nodup ∧ (∀e∈p.edges,e∈F) ∧ p.edges.length=n
  have h0 : P 0 := ⟨u,nil u,by simp,by simp,rfl⟩
  obtain ⟨v,p,hp,hF,hlen⟩ := Nat.findGreatest_spec (P:=P) (Nat.zero_le F.card) h0
  refine ⟨v,p,hp,hF,?_⟩
  intro w q hq hqF
  rw [hlen]
  exact Nat.le_findGreatest (q.length_le_card F hq hqF) ⟨w,q,hq,hqF,rfl⟩

lemma longest_no_extension [DecidableEq E] {F : Finset E} (p : LabelWalk step u v)
    (hp : p.edges.Nodup) (hF : ∀e∈p.edges,e∈F)
    (hmax : ∀w (q : LabelWalk step u w), q.edges.Nodup → (∀e∈q.edges,e∈F) →
      q.edges.length≤p.edges.length) {e : E} {w : V} (he : e∈F) (hs : step e v w) :
    e∈p.edges := by
  classical
  by_contra hn
  let q := p.append (cons e hs (nil w))
  have hq : q.edges.Nodup := by
    have hd : ∀a∈p.edges,a≠e := fun a ha h=>hn (h ▸ ha)
    simpa [q,List.nodup_append] using And.intro hp hd
  have hqF : ∀a∈q.edges,a∈F := by
    intro a ha
    simp only [q,edges_append,edges_cons,edges_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with ha|rfl
    · exact hF a ha
    · exact he
  have hh := hmax w q hq hqF
  simp [q] at hh

end LabelWalk
end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE LabelWalkMax

-- BEGIN COMPLETE MODULE UndirectedCycle
section

open Finset
namespace ChinesePostman.Mixed.Proof
variable {V E : Type} [DecidableEq V] [DecidableEq E]

lemma exists_undirected_cycle (a b : E → V) (hab : ∀e,a e≠b e) (S : Finset E)
    (hS : S.Nonempty) (heven : ∀v,Even (incidentDegree a b S v)) :
    ∃u,∃p : UndirWalk a b S u u,p.edges.Nodup ∧ p.edges≠[] := by
  obtain ⟨e,he⟩ := hS
  obtain ⟨v,p,hp,hF,hmax⟩ := LabelWalk.exists_longest
    (fun d u v => d∈S ∧ undirStep a b d u v) S (a e)
  have hused : ∀d∈S,a d=v ∨ b d=v → d∈p.edges := by
    intro d hd hv
    rcases hv with ha | hb
    · exact p.longest_no_extension hp hF hmax hd ⟨hd,Or.inl ⟨ha,rfl⟩⟩
    · exact p.longest_no_extension hp hF hmax hd ⟨hd,Or.inr ⟨rfl,hb⟩⟩
  have hdeg : incidentDegree a b p.edges.toFinset v=incidentDegree a b S v := by
    unfold incidentDegree
    congr 1
    ext d
    simp only [mem_filter,List.mem_toFinset]
    exact ⟨fun h => ⟨hF d h.1,h.2⟩,fun h => ⟨hused d h.1 h.2,h.2⟩⟩
  have hv : a e=v := by
    by_contra hv
    have hh := undirWalk_incidence hab p hp v
    simp only [if_neg hv,ite_true,add_zero,hdeg] at hh
    obtain ⟨k,hk⟩ := heven v
    omega
  subst v
  refine ⟨a e,p,hp,?_⟩
  intro hz
  let q : UndirWalk a b S (a e) (b e) := .cons e ⟨he,Or.inl ⟨rfl,rfl⟩⟩ (.nil (b e))
  have hq : q.edges.Nodup := by simp [q]
  have hqF : ∀d∈q.edges,d∈S := by simpa [q] using he
  have hh := hmax (b e) q hq hqF
  simp [q,hz] at hh

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE UndirectedCycle

-- BEGIN COMPLETE MODULE TrailOrientation
section

open Finset
namespace ChinesePostman.Mixed.Proof
variable {V E : Type} [DecidableEq V] [DecidableEq E]

noncomputable def walkFlip (a : E → V) {step : E → V → V → Prop} :
    {u v : V} → LabelWalk step u v → E → Bool
  | _, _, .nil _ => fun _ => false
  | u, _, .cons e _ p => fun d => if d=e then decide (a e≠u) else walkFlip a p d

lemma walkFlip_cons_other (a : E → V) {step : E → V → V → Prop} {u v w : V}
    (e : E) (h : step e u v) (p : LabelWalk step v w) {d : E} (hd : d≠e) :
    walkFlip a (.cons e h p) d=walkFlip a p d := by simp [walkFlip,hd]

lemma walkFlip_first {a b : E → V} (hab : ∀e,a e≠b e) {S : Finset E} {u v w : V}
    (e : E) (he : e∈S ∧ undirStep a b e u v) (p : UndirWalk a b S v w) :
    orientedTail a b (walkFlip a (.cons e he p)) e=u ∧
      orientedHead a b (walkFlip a (.cons e he p)) e=v := by
  rcases he.2 with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simp [walkFlip,orientedTail,orientedHead,ha,hb]
  · have hvu : v≠u := by intro h; exact hab e (ha.trans (h.trans hb.symm))
    simp [walkFlip,orientedTail,orientedHead,ha,hb,hvu]

lemma outDegree_walkFlip_cons {a b : E → V} (hab : ∀e,a e≠b e) {S : Finset E} {u v w : V}
    (e : E) (he : e∈S ∧ undirStep a b e u v) (p : UndirWalk a b S v w)
    (hn : e∉p.edges) (x : V) :
    outDegree (orientedTail a b (walkFlip a (.cons e he p))) (e::p.edges).toFinset x =
      outDegree (orientedTail a b (walkFlip a p)) p.edges.toFinset x + (if u=x then 1 else 0) := by
  classical
  have hfirst := (walkFlip_first hab e he p).1
  have hc : p.edges.toFinset.filter (fun d => orientedTail a b (walkFlip a (.cons e he p)) d=x) =
      p.edges.toFinset.filter (fun d => orientedTail a b (walkFlip a p) d=x) := by
    apply Finset.filter_congr
    intro d hd
    have hde : d≠e := by rintro rfl; exact hn (List.mem_toFinset.mp hd)
    simp only [orientedTail,walkFlip_cons_other a e he p hde]
  unfold outDegree
  rw [List.toFinset_cons,filter_insert,hc,hfirst]
  by_cases hx : u=x
  · simp [hx,mem_filter,hn,Nat.add_comm]
  · simp [hx]

lemma inDegree_walkFlip_cons {a b : E → V} (hab : ∀e,a e≠b e) {S : Finset E} {u v w : V}
    (e : E) (he : e∈S ∧ undirStep a b e u v) (p : UndirWalk a b S v w)
    (hn : e∉p.edges) (x : V) :
    outDegree (orientedHead a b (walkFlip a (.cons e he p))) (e::p.edges).toFinset x =
      outDegree (orientedHead a b (walkFlip a p)) p.edges.toFinset x + (if v=x then 1 else 0) := by
  classical
  have hfirst := (walkFlip_first hab e he p).2
  have hc : p.edges.toFinset.filter (fun d => orientedHead a b (walkFlip a (.cons e he p)) d=x) =
      p.edges.toFinset.filter (fun d => orientedHead a b (walkFlip a p) d=x) := by
    apply Finset.filter_congr
    intro d hd
    have hde : d≠e := by rintro rfl; exact hn (List.mem_toFinset.mp hd)
    simp only [orientedHead,walkFlip_cons_other a e he p hde]
  unfold outDegree
  rw [List.toFinset_cons,filter_insert,hc,hfirst]
  by_cases hx : v=x
  · simp [hx,mem_filter,hn,Nat.add_comm]
  · simp [hx]

lemma walkFlip_balance {a b : E → V} (hab : ∀e,a e≠b e) {S : Finset E} {u v : V}
    (p : UndirWalk a b S u v) (hp : p.edges.Nodup) (x : V) :
    outDegree (orientedTail a b (walkFlip a p)) p.edges.toFinset x + (if v=x then 1 else 0) =
      outDegree (orientedHead a b (walkFlip a p)) p.edges.toFinset x + (if u=x then 1 else 0) := by
  induction p with
  | nil u => simp [outDegree]
  | cons e he p ih =>
    have hn := List.nodup_cons.mp hp
    have hh := ih hn.2
    rw [LabelWalk.edges_cons,outDegree_walkFlip_cons hab e he p hn.1,
      inDegree_walkFlip_cons hab e he p hn.1]
    omega

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE TrailOrientation

-- BEGIN COMPLETE MODULE OrientationCombine
section

open Finset
namespace ChinesePostman.Mixed.Proof
variable {V E : Type} [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
lemma outDegree_congr {a b : E → V} {S : Finset E} (h : ∀e∈S,a e=b e) (v : V) :
    outDegree a S v=outDegree b S v := by
  unfold outDegree
  congr 1
  exact Finset.filter_congr fun e he => by rw [h e he]

lemma outDegree_sdiff (a : E → V) {S C : Finset E} (hCS : C ⊆ S) (v : V) :
    outDegree a S v=outDegree a C v+outDegree a (S \ C) v := by
  simpa only [incidentDegree,outDegree,or_self] using incidentDegree_sdiff a a hCS v

lemma combine_balanced (a b : E → V) {S C : Finset E} (hCS : C ⊆ S)
    (f g : E → Bool)
    (hf : ∀v,outDegree (orientedTail a b f) C v=outDegree (orientedHead a b f) C v)
    (hg : ∀v,outDegree (orientedTail a b g) (S \ C) v=outDegree (orientedHead a b g) (S \ C) v) :
    ∀v,outDegree (orientedTail a b (fun e => if e∈C then f e else g e)) S v =
      outDegree (orientedHead a b (fun e => if e∈C then f e else g e)) S v := by
  classical
  intro v
  rw [outDegree_sdiff _ hCS,outDegree_sdiff _ hCS]
  have h1 : outDegree (orientedTail a b (fun e => if e∈C then f e else g e)) C v = outDegree (orientedTail a b f) C v :=
    outDegree_congr (fun e he => by simp [orientedTail,he]) v
  have h2 : outDegree (orientedHead a b (fun e => if e∈C then f e else g e)) C v = outDegree (orientedHead a b f) C v :=
    outDegree_congr (fun e he => by simp [orientedHead,he]) v
  have h3 : outDegree (orientedTail a b (fun e => if e∈C then f e else g e)) (S \ C) v = outDegree (orientedTail a b g) (S \ C) v :=
    outDegree_congr (fun e he => by simp [orientedTail,(mem_sdiff.mp he).2]) v
  have h4 : outDegree (orientedHead a b (fun e => if e∈C then f e else g e)) (S \ C) v = outDegree (orientedHead a b g) (S \ C) v :=
    outDegree_congr (fun e he => by simp [orientedHead,(mem_sdiff.mp he).2]) v
  rw [h1,h2,h3,h4,hf v,hg v]

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE OrientationCombine

-- BEGIN COMPLETE MODULE EvenOrientation
section

open Finset
namespace ChinesePostman.Mixed.Proof
variable {V E : Type} [DecidableEq V] [DecidableEq E]

lemma even_orientation (a b : E → V) (hab : ∀e,a e≠b e) (S : Finset E)
    (heven : ∀v,Even (incidentDegree a b S v)) :
    ∃flip : E → Bool,∀v,outDegree (orientedTail a b flip) S v=outDegree (orientedHead a b flip) S v := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S=∅
    · subst S
      exact ⟨fun _ => false,fun _ => by simp [outDegree]⟩
    obtain ⟨u,p,hp,hpn⟩ := exists_undirected_cycle a b hab S (Finset.nonempty_iff_ne_empty.mpr hS) heven
    let C := p.edges.toFinset
    have hCS : C ⊆ S := undirWalk_edges_subset p
    have hC : C.Nonempty := by simpa [C] using hpn
    have hcEven (v : V) : Even (incidentDegree a b C v) := undirWalk_closed_even hab p hp v
    have hrest (v : V) : Even (incidentDegree a b (S \ C) v) := by
      have hd := incidentDegree_sdiff a b hCS v
      obtain ⟨k,hk⟩ := heven v
      obtain ⟨j,hj⟩ := hcEven v
      exact ⟨k-j,by omega⟩
    obtain ⟨g,hg⟩ := ih (S \ C) (Finset.sdiff_ssubset hCS hC) hrest
    have hf (v : V) : outDegree (orientedTail a b (walkFlip a p)) C v=outDegree (orientedHead a b (walkFlip a p)) C v := by
      exact Nat.add_right_cancel (walkFlip_balance hab p hp v)
    exact ⟨fun e => if e∈C then walkFlip a p e else g e,combine_balanced a b hCS (walkFlip a p) g hf hg⟩

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE EvenOrientation

-- BEGIN COMPLETE MODULE MixedDegreeParity
section

open Finset
namespace ChinesePostman.Mixed.Proof
variable {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
lemma degree_decomposition (G : MixedGraph V E) (v : V) :
    G.degree v = G.undirDeg v + G.outDeg v + G.inDeg v := by
  unfold MixedGraph.degree MixedGraph.undirDeg MixedGraph.outDeg MixedGraph.inDeg
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  cases hd : G.directed e <;> by_cases ht : G.tail e=v <;> by_cases hh : G.head e=v
  all_goals try exact (G.loopless e (ht.trans hh.symm)).elim
  all_goals simp [ht,hh]

omit [DecidableEq E] in
lemma even_undirected_degree (G : MixedGraph V E) (he : G.IsEven) (hs : G.IsSymmetric) (v : V) :
    Even (G.undirDeg v) := by
  obtain ⟨k,hk⟩ := he v
  have hd := degree_decomposition G v
  rw [hs v] at hd
  refine ⟨k-G.inDeg v,?_⟩
  omega

omit [DecidableEq E] in
lemma even_undirected_incidence (G : MixedGraph V E) (he : G.IsEven) (hs : G.IsSymmetric) (v : V) :
    Even (incidentDegree G.tail G.head (univ.filter (fun e => G.directed e=false)) v) := by
  have hh := even_undirected_degree G he hs v
  simpa only [incidentDegree,MixedGraph.undirDeg,filter_filter] using hh

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE MixedDegreeParity

-- BEGIN COMPLETE MODULE MixedOrientation
section

open Finset
namespace ChinesePostman.Mixed.Proof
variable {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]

lemma exists_balanced_orientation (G : MixedGraph V E) (heven : G.IsEven) (hsym : G.IsSymmetric) :
    ∃flip : E → Bool, (∀e,G.directed e=true → flip e=false) ∧
      ∀v,outDegree (orientedTail G.tail G.head flip) univ v =
        outDegree (orientedHead G.tail G.head flip) univ v := by
  classical
  let S : Finset E := univ.filter (fun e => G.directed e=false)
  obtain ⟨f,hf⟩ := even_orientation G.tail G.head G.loopless S (even_undirected_incidence G heven hsym)
  let g : E → Bool := fun e => if G.directed e=false then f e else false
  refine ⟨g,?_,?_⟩
  · intro e he
    simp [g,he]
  · intro v
    have hsub : S ⊆ univ := subset_univ _
    have hT : outDegree (orientedTail G.tail G.head g) S v = outDegree (orientedTail G.tail G.head f) S v := by
      apply outDegree_congr
      intro e he
      have hd : G.directed e=false := (mem_filter.mp he).2
      simp [orientedTail,g,hd]
    have hH : outDegree (orientedHead G.tail G.head g) S v = outDegree (orientedHead G.tail G.head f) S v := by
      apply outDegree_congr
      intro e he
      have hd : G.directed e=false := (mem_filter.mp he).2
      simp [orientedHead,g,hd]
    have hTD : outDegree (orientedTail G.tail G.head g) (univ \ S) v=G.outDeg v := by
      unfold outDegree MixedGraph.outDeg
      congr 1
      ext e
      cases hd : G.directed e <;> simp [S,g,hd,orientedTail]
    have hHD : outDegree (orientedHead G.tail G.head g) (univ \ S) v=G.inDeg v := by
      unfold outDegree MixedGraph.inDeg
      congr 1
      ext e
      cases hd : G.directed e <;> simp [S,g,hd,orientedHead]
    rw [outDegree_sdiff _ hsub,outDegree_sdiff _ hsub,hT,hH,hTD,hHD,hf v,hsym v]

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE MixedOrientation

-- BEGIN COMPLETE MODULE DirectedCounts
section

namespace ChinesePostman.Mixed.Proof
variable {V E : Type} [DecidableEq V]

def directedStep (tail head : E → V) (e : E) (u v : V) : Prop := tail e=u ∧ head e=v

def edgeCount (f : E → V) (es : List E) (v : V) : ℕ :=
  (es.filter (fun e=>decide (f e=v))).length

def setCount [DecidableEq E] (f : E → V) (F : Finset E) (v : V) : ℕ :=
  (F.filter (fun e=>f e=v)).card

@[simp] lemma edgeCount_nil (f : E → V) (v : V) : edgeCount f [] v=0 := rfl
@[simp] lemma edgeCount_cons (f : E → V) (e : E) (es : List E) (v : V) :
    edgeCount f (e::es) v=(if f e=v then 1 else 0)+edgeCount f es v := by
  by_cases h : f e=v <;> simp [edgeCount,h,Nat.add_comm]

lemma walk_flow (tail head : E → V) {u v : V}
    (p : LabelWalk (directedStep tail head) u v) (x : V) :
    edgeCount tail p.edges x+(if v=x then 1 else 0)=
      edgeCount head p.edges x+(if u=x then 1 else 0) := by
  induction p with
  | nil => simp
  | @cons u v w e h p ih =>
    have ht := h.1
    have hh := h.2
    simp only [LabelWalk.edges_cons,edgeCount_cons,ht,hh]
    omega

lemma edgeCount_le_setCount [DecidableEq E] (f : E → V) (es : List E) (F : Finset E)
    (hn : es.Nodup) (hs : ∀e∈es,e∈F) (x : V) : edgeCount f es x≤ setCount f F x := by
  unfold edgeCount setCount
  rw [←List.toFinset_card_of_nodup (hn.filter _)]
  apply Finset.card_le_card
  intro e he
  have hh := List.mem_filter.mp (List.mem_toFinset.mp he)
  exact Finset.mem_filter.mpr ⟨hs e hh.1,of_decide_eq_true hh.2⟩

lemma edgeCount_eq_setCount [DecidableEq E] (f : E → V) (es : List E) (F : Finset E)
    (hn : es.Nodup) (hs : ∀e∈es,e∈F) (x : V) (hx : ∀e∈F,f e=x→e∈es) :
    edgeCount f es x=setCount f F x := by
  unfold edgeCount setCount
  rw [←List.toFinset_card_of_nodup (hn.filter _)]
  congr 1
  ext e
  simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,Finset.mem_filter]
  exact ⟨fun h=>⟨hs e h.1,h.2⟩,fun h=>⟨hx e h.1 h.2,h.2⟩⟩

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE DirectedCounts

-- BEGIN COMPLETE MODULE DirectedClosedTrail
section

namespace ChinesePostman.Mixed.Proof
variable {V E : Type} [DecidableEq V] [DecidableEq E]

lemma maximal_directed_closed (tail head : E → V) (F : Finset E)
    (hbal : ∀x,setCount tail F x=setCount head F x) {u v : V}
    (p : LabelWalk (directedStep tail head) u v) (hp : p.edges.Nodup)
    (hF : ∀e∈p.edges,e∈F)
    (hmax : ∀w (q : LabelWalk (directedStep tail head) u w),q.edges.Nodup →
      (∀e∈q.edges,e∈F) → q.edges.length≤p.edges.length) : v=u := by
  by_contra hne
  have hout : ∀e∈F,tail e=v→e∈p.edges := by
    intro e he ht
    exact p.longest_no_extension hp hF hmax he ⟨ht,rfl⟩
  have hcout := edgeCount_eq_setCount tail p.edges F hp hF v hout
  have hcin := edgeCount_le_setCount head p.edges F hp hF v
  have hflow : edgeCount tail p.edges v+1=edgeCount head p.edges v := by
    simpa [hne,Ne.symm hne] using walk_flow tail head p v
  rw [hcout,hbal v] at hflow
  omega

lemma exists_closed_directed_trail (tail head : E → V) (F : Finset E)
    (hbal : ∀x,setCount tail F x=setCount head F x) (u : V) :
    ∃p : LabelWalk (directedStep tail head) u u,p.edges.Nodup ∧
      (∀e∈p.edges,e∈F) ∧
      ∀w (q : LabelWalk (directedStep tail head) u w),q.edges.Nodup →
        (∀e∈q.edges,e∈F) → q.edges.length≤p.edges.length := by
  obtain ⟨v,p,hp,hF,hmax⟩ := LabelWalk.exists_longest (directedStep tail head) F u
  have hv := maximal_directed_closed tail head F hbal p hp hF hmax
  subst v
  exact ⟨p,hp,hF,hmax⟩

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE DirectedClosedTrail

-- BEGIN COMPLETE MODULE DirectedResidual
section

namespace ChinesePostman.Mixed.Proof
variable {V E : Type} [DecidableEq V] [DecidableEq E]

lemma setCount_sdiff (f : E → V) (F U : Finset E) (hU : U⊆F) (x : V) :
    setCount f (F\U) x+setCount f U x=setCount f F x := by
  unfold setCount
  have he : (F\U).filter (fun e=>f e=x)=F.filter (fun e=>f e=x)\U.filter (fun e=>f e=x) := by
    ext e; simp; tauto
  rw [he]
  exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter _ hU)

lemma setCount_edges (f : E → V) (es : List E) (hn : es.Nodup) (x : V) :
    setCount f es.toFinset x=edgeCount f es x := by
  apply Eq.symm
  exact edgeCount_eq_setCount f es es.toFinset hn
    (fun _ he=>List.mem_toFinset.mpr he) x (fun _ he _=>List.mem_toFinset.mp he)

lemma closed_residual_balanced (tail head : E → V) (F : Finset E)
    (hb : ∀x,setCount tail F x=setCount head F x) {u : V}
    (p : LabelWalk (directedStep tail head) u u) (hp : p.edges.Nodup)
    (hF : ∀e∈p.edges,e∈F) :
    ∀x,setCount tail (F\p.edges.toFinset) x=setCount head (F\p.edges.toFinset) x := by
  intro x
  have hsub : p.edges.toFinset⊆F := fun e he=>hF e (List.mem_toFinset.mp he)
  have ht := setCount_sdiff tail F p.edges.toFinset hsub x
  have hh := setCount_sdiff head F p.edges.toFinset hsub x
  rw [setCount_edges tail _ hp] at ht
  rw [setCount_edges head _ hp] at hh
  have hf := walk_flow tail head p x
  have hbal := hb x
  omega

lemma residual_outgoing_of_incident (tail head : E → V) (F : Finset E)
    (hb : ∀x,setCount tail F x=setCount head F x) {x : V}
    (hi : ∃e∈F,tail e=x ∨ head e=x) : ∃e∈F,tail e=x := by
  classical
  obtain ⟨e,he,ht|hh⟩ := hi
  · exact ⟨e,he,ht⟩
  · have hp : 0<setCount head F x := Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hh⟩⟩
    rw [←hb x] at hp
    obtain ⟨a,ha⟩ := Finset.card_pos.mp hp
    exact ⟨a,(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp ha).2⟩

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE DirectedResidual

-- BEGIN COMPLETE MODULE LabelWalkMap
section

namespace ChinesePostman.Mixed.Proof.LabelWalk
variable {V E : Type} {step step' : E → V → V → Prop}

def mapStep (h : ∀e u v,step e u v→step' e u v) :
    {u v : V} → LabelWalk step u v → LabelWalk step' u v
  | _, _, .nil x => .nil x
  | _, _, .cons e he p => .cons e (h _ _ _ he) (p.mapStep h)

@[simp] lemma edges_mapStep (h : ∀e u v,step e u v→step' e u v) {u v : V}
    (p : LabelWalk step u v) : (p.mapStep h).edges=p.edges := by
  induction p with
  | nil => rfl
  | cons e he p ih => simp [mapStep,ih]

@[simp] lemma nodes_mapStep (h : ∀e u v,step e u v→step' e u v) {u v : V}
    (p : LabelWalk step u v) : (p.mapStep h).nodes=p.nodes := by
  induction p with
  | nil => rfl
  | cons e he p ih => simp [mapStep,ih]

lemma end_mem_of_closed_set {u v : V} (p : LabelWalk step u v) (S : Set V)
    (hu : u∈S) (hS : ∀e x y,step e x y→x∈S→y∈S) : v∈S := by
  induction p with
  | nil => exact hu
  | cons e he p ih => exact ih (hS _ _ _ he hu)

end ChinesePostman.Mixed.Proof.LabelWalk
end
-- END COMPLETE MODULE LabelWalkMap

-- BEGIN COMPLETE MODULE DirectedConnection
section

namespace ChinesePostman.Mixed.Proof
variable {V E : Type}

def weakStep (tail head : E → V) (e : E) (u v : V) : Prop :=
  (tail e=u ∧ head e=v) ∨ (tail e=v ∧ head e=u)

lemma directed_edge_nodes (tail head : E → V) {u v : V}
    (p : LabelWalk (directedStep tail head) u v) {e : E} (he : e∈p.edges) :
    tail e∈p.nodes ∧ head e∈p.nodes := by
  induction p with
  | nil => simp at he
  | @cons u y v a ha p ih =>
    rcases List.mem_cons.mp he with rfl|he
    · have ht := ha.1
      have hh := ha.2
      rw [LabelWalk.nodes_cons,ht,hh]
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ p.start_mem⟩
    · have hh := ih he
      exact ⟨List.mem_cons_of_mem _ hh.1,List.mem_cons_of_mem _ hh.2⟩

lemma exists_unused_incident (tail head : E → V)
    (hconn : ∀u v,Nonempty (LabelWalk (weakStep tail head) u v)) {r : V}
    (p : LabelWalk (directedStep tail head) r r) (hmiss : ∃e,e∉p.edges) :
    ∃x∈p.nodes,∃e,e∉p.edges ∧ (tail e=x ∨ head e=x) := by
  classical
  by_contra hn
  push Not at hn
  have hc : ∀e x y,weakStep tail head e x y→x∈p.nodes→y∈p.nodes := by
    intro e x y he hx
    have hu : e∈p.edges := by
      by_contra hm
      exact he.elim (fun h=>(hn x hx e hm).1 h.1) (fun h=>(hn x hx e hm).2 h.2)
    have hh := directed_edge_nodes tail head p hu
    rcases he with ⟨ht,hh'⟩|⟨ht,hh'⟩
    · exact hh' ▸ hh.2
    · exact ht ▸ hh.1
  obtain ⟨e,he⟩ := hmiss
  obtain ⟨q⟩ := hconn r (tail e)
  have ht : tail e∈p.nodes := q.end_mem_of_closed_set {x|x∈p.nodes} p.start_mem hc
  exact (hn (tail e) ht e he).1 rfl

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE DirectedConnection

-- BEGIN COMPLETE MODULE SpliceNodup
section

namespace ChinesePostman.Mixed.Proof
variable {E : Type}
lemma splice_nodup {a b q : List E} (hab : (a++b).Nodup) (hq : q.Nodup)
    (hd : ∀e∈q,e∉a++b) : (a++q++b).Nodup := by
  obtain ⟨ha,hb,hab⟩ := List.nodup_append.mp hab
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨ha,hq,?_⟩,hb,?_⟩
  · intro e he f hf h
    exact hd f hf (List.mem_append_left _ (h ▸ he))
  · intro e he f hf h
    rcases List.mem_append.mp he with he|he
    · exact hab e he f hf h
    · exact hd e he (List.mem_append_right _ (h.symm ▸ hf))
end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE SpliceNodup

-- BEGIN COMPLETE MODULE DirectedEuler
section

namespace ChinesePostman.Mixed.Proof
variable {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E]

lemma directed_euler_exists (tail head : E → V)
    (hbal : ∀x,setCount tail Finset.univ x=setCount head Finset.univ x)
    (hconn : ∀u v,Nonempty (LabelWalk (weakStep tail head) u v)) (r : V) :
    ∃p : LabelWalk (directedStep tail head) r r,p.edges.Nodup ∧ ∀e,e∈p.edges := by
  classical
  obtain ⟨p,hp,hF,hmax⟩ := exists_closed_directed_trail tail head Finset.univ hbal r
  refine ⟨p,hp,?_⟩
  by_contra hn
  push Not at hn
  obtain ⟨x,hx,e,he,hinc⟩ := exists_unused_incident tail head hconn p hn
  let R := Finset.univ\p.edges.toFinset
  have hR : ∀x,setCount tail R x=setCount head R x := closed_residual_balanced tail head _ hbal p hp hF
  have heR : e∈R := by simpa [R] using he
  obtain ⟨d,hdR,hdt⟩ := residual_outgoing_of_incident tail head R hR ⟨e,heR,hinc⟩
  obtain ⟨q,hq,hqR,hqmax⟩ := exists_closed_directed_trail tail head R hR x
  let one : LabelWalk (directedStep tail head) x (head d) := .cons d ⟨hdt,rfl⟩ (.nil _)
  have hqpos : 0<q.edges.length := by
    have hh := hqmax (head d) one (by change [d].Nodup; simp) (by
      intro a ha
      change a∈[d] at ha
      have had := List.mem_singleton.mp ha
      simpa only [had] using hdR)
    change 1≤q.edges.length at hh
    omega
  obtain ⟨a,b,hab⟩ := p.split_at_node hx
  let c := (a.append q).append b
  have hc : c.edges.Nodup := by
    simp only [c,LabelWalk.edges_append]
    apply splice_nodup (hab ▸ hp) hq
    intro f hf
    have hh := hqR f hf
    have hnot : f∉p.edges := by simpa [R] using hh
    simpa only [hab] using hnot
  have hbound := hmax r c hc (by simp)
  simp only [c,LabelWalk.edges_append,List.length_append] at hbound
  have hlen := congrArg List.length hab
  simp only [List.length_append] at hlen
  omega

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE DirectedEuler

-- BEGIN COMPLETE MODULE LabelWalkLists
section

namespace ChinesePostman.Mixed.Proof
namespace LabelWalk
variable {V E : Type} {step : E → V → V → Prop}

lemma exists_of_lists (ns : List V) (es : List E)
    (hlen : ns.length=es.length+1)
    (hs : ∀i (hi : i<es.length),step es[i] (ns[i]'(by omega)) (ns[i+1]'(by omega))) :
    ∃u v,∃p : LabelWalk step u v,p.edges=es ∧ p.nodes=ns := by
  induction es generalizing ns with
  | nil =>
    cases ns with
    | nil => simp at hlen
    | cons u ns =>
      have hn : ns=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst ns
      exact ⟨u,u,nil u,rfl,rfl⟩
  | cons e es ih =>
    cases ns with
    | nil => simp at hlen
    | cons u ns =>
      cases ns with
      | nil => simp at hlen
      | cons v ns =>
        have htail : (v::ns).length=es.length+1 := by simpa using hlen
        have hstail : ∀i (hi : i<es.length),step es[i]
            ((v::ns)[i]'(by omega)) ((v::ns)[i+1]'(by omega)) := by
          intro i hi
          exact hs (i+1) (by simp; omega)
        obtain ⟨a,b,p,he,hn⟩ := ih (v::ns) htail hstail
        have hav : a=v := by have hh:=p.nodes_head; rw [hn] at hh; simpa using hh.symm
        subst a
        exact ⟨u,b,cons e (hs 0 (by simp)) p,by simp [he],by simp [hn]⟩

lemma exists_of_lists_endpoints (ns : List V) (es : List E)
    (hlen : ns.length=es.length+1)
    (hs : ∀i (hi : i<es.length),step es[i] (ns[i]'(by omega)) (ns[i+1]'(by omega)))
    {u v : V} (hfirst : ns.head?=some u) (hlast : ns.getLast?=some v) :
    ∃p : LabelWalk step u v,p.edges=es ∧ p.nodes=ns := by
  obtain ⟨a,b,p,he,hn⟩ := exists_of_lists ns es hlen hs
  have hau : a=u := by have h:=p.nodes_head; rw [hn,hfirst] at h; exact Option.some.inj h.symm
  have hbv : b=v := by have h:=p.nodes_last; rw [hn,hlast] at h; exact Option.some.inj h.symm
  subst a; subst b
  exact ⟨p,he,hn⟩

end LabelWalk
end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE LabelWalkLists

-- BEGIN COMPLETE MODULE NativeWalkAdapters
section

namespace ChinesePostman.Mixed.Proof
variable {V E : Type}

lemma weakStep_oriented_iff (a b : E → V) (flip : E → Bool) (e : E) (u v : V) :
    weakStep (orientedTail a b flip) (orientedHead a b flip) e u v ↔ weakStep a b e u v := by
  cases h : flip e <;> simp only [weakStep,orientedTail,orientedHead,h,Bool.false_eq_true,
    if_false,if_true]; tauto

lemma native_connected_oriented (G : MixedGraph V E) (hconn : G.Connected) (flip : E → Bool) :
    ∀u v,Nonempty (LabelWalk (weakStep (orientedTail G.tail G.head flip)
      (orientedHead G.tail G.head flip)) u v) := by
  intro u v
  obtain ⟨ns,es,⟨hlen,hs⟩,hfirst,hlast⟩ := hconn u v
  obtain ⟨p,_,_⟩ := LabelWalk.exists_of_lists_endpoints ns es hlen
    (fun i hi=>(weakStep_oriented_iff G.tail G.head flip _ _ _).mpr (hs i hi).2) hfirst hlast
  exact ⟨p⟩

lemma oriented_step_mixed (G : MixedGraph V E) (flip : E → Bool)
    (hfix : ∀e,G.directed e=true→flip e=false) {e : E} {u v : V}
    (hs : directedStep (orientedTail G.tail G.head flip) (orientedHead G.tail G.head flip) e u v) :
    (G.tail e=u ∧ G.head e=v) ∨ (G.directed e=false ∧ G.tail e=v ∧ G.head e=u) := by
  cases hf : flip e with
  | false => exact Or.inl (by simpa [directedStep,orientedTail,orientedHead,hf] using hs)
  | true =>
    have hd : G.directed e=false := by
      cases h : G.directed e
      · rfl
      · have hh := hfix e h
        simp [hf] at hh
    exact Or.inr ⟨hd,by simpa [directedStep,orientedTail,orientedHead,hf] using And.intro hs.2 hs.1⟩

lemma native_mixed_walk (G : MixedGraph V E) (flip : E → Bool)
    (hfix : ∀e,G.directed e=true→flip e=false) {u v : V}
    (p : LabelWalk (directedStep (orientedTail G.tail G.head flip)
      (orientedHead G.tail G.head flip)) u v) : G.IsMixedWalk p.nodes p.edges := by
  refine ⟨p.nodes_length,?_⟩
  intro i hi
  exact oriented_step_mixed G flip hfix (p.step_at i hi)

end ChinesePostman.Mixed.Proof
end
-- END COMPLETE MODULE NativeWalkAdapters

-- BEGIN COMPLETE MODULE MixedEulerRoot
section

namespace ChinesePostman.Mixed


theorem mixed_euler_tour {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hconn : G.Connected) (heven : G.IsEven)
    (hsym : G.IsSymmetric) (r : V) :
    ∃ ns es, G.IsMixedEulerTour ns es ∧ ns.head? = some r := by
  obtain ⟨flip,hfix,hbal⟩ := Proof.exists_balanced_orientation G heven hsym
  obtain ⟨p,hp,hall⟩ := Proof.directed_euler_exists
    (Proof.orientedTail G.tail G.head flip) (Proof.orientedHead G.tail G.head flip)
    hbal (Proof.native_connected_oriented G hconn flip) r
  refine ⟨p.nodes,p.edges,⟨⟨Proof.native_mixed_walk G flip hfix p,?_⟩,?_⟩,p.nodes_head⟩
  · rw [p.nodes_head,p.nodes_last]
  · intro e
    exact List.count_eq_one_of_mem hp (hall e)


end ChinesePostman.Mixed

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : ChinesePostman.Mixed.MixedGraph V E) (hconn : G.Connected) (heven : G.IsEven)
    (hsym : G.IsSymmetric) (r : V) :
    ∃ ns es, G.IsMixedEulerTour ns es ∧ ns.head? = some r := by
  exact ChinesePostman.Mixed.mixed_euler_tour G hconn heven hsym r
end
-- END COMPLETE MODULE MixedEulerRoot
