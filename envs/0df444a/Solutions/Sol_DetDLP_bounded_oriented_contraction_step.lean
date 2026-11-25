-- Prove2me | solution 1 for DetDLP.bounded_oriented_contraction_step
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T16:15:49.1008+00:00
-- url     : https://prove2.me/submissions/cf80097b-d8af-4e65-b923-66d0351c8ad7

import Definitions.Def_DetDLP_OrientedPacketInstance
import Mathlib
import Theorems.Thm_DetDLP_oriented_packet_slot_layout
import Definitions.Def_DetDLP_BTN
import Theorems.Thm_DetDLP_terminal_packing_cell_bounds
import Theorems.Thm_DetDLP_weighted_mode_branching_bound
import Theorems.Thm_DetDLP_oriented_dyadic_sample_child_contractions

section
namespace DetDLP.ContractionPortCounts
open Finset OrientedPacketInstance
variable {a r : ℕ} {P : Type} [Fintype P] [DecidableEq P]
variable (i : Fin a) (tag : P→Fin r×Fin r) (active : P→Finset (Pos a))
variable (G : BipartiteMultigraph) (layout : Fin G.nE ≃ Address active) (grp : Fin G.nV→Fin r)
abbrev Ports (g : Fin r) := Assigned i tag active g
abbrev Compat := ∀ e d,group i (tag (layout e).1) d (layout e).2.val.val=grp (endpoint G e d)
variable (align : Compat i tag active G layout grp)

theorem endpoint_side (e : Fin G.nE) (d : Bool) : G.side (endpoint G e d)=d := by
  unfold endpoint
  have h := G.bipartite e
  split_ifs with hd
  · exact hd
  · cases hr : G.side (G.endpoints e).1 <;> cases hl : G.side (G.endpoints e).2 <;> cases d <;> simp_all

def edge {g : Fin r} (e : Ports i tag active g) : Fin G.nE := layout.symm ⟨e.val.1,e.val.2.1,e.property.1⟩
include align in
theorem identify {g : Fin r} (e : Ports i tag active g) :
    grp (endpoint G (edge i tag active G layout e) e.val.2.2)=g := by
  let address : Address active := ⟨e.val.1,e.val.2.1,e.property.1⟩
  exact (align (layout.symm address) e.val.2.2).symm.trans
    ((congrArg (fun z : Address active => group i (tag z.1) e.val.2.2 z.2.val.val) (layout.apply_symm_apply address)).trans e.property.2)

theorem recover_address {g : Fin r} (e : Ports i tag active g) :
    layout (edge i tag active G layout e)=⟨e.val.1,e.val.2.1,e.property.1⟩ :=
  layout.apply_symm_apply _

theorem unique_port {g : Fin r} {e f : Ports i tag active g}
    (he : edge i tag active G layout e=edge i tag active G layout f) (hd : e.val.2.2=f.val.2.2) : e=f := by
  have u := congrArg layout he
  rw [recover_address,recover_address] at u
  have hq := congrArg (fun v : Address active => v.1) u
  have hk := congrArg (fun v : Address active => v.2.val) u
  exact Subtype.ext (Prod.ext hq (Prod.ext hk hd))

def marked (z : Address active) (d : Bool) : Σ g,Ports i tag active g :=
  ⟨_,⟨(z.1,z.2.val,d),z.2.property,rfl⟩⟩
def portsEquiv : (Σ g,Ports i tag active g) ≃ (Fin G.nE×Bool) where
  toFun e := (edge i tag active G layout e.2,e.2.val.2.2)
  invFun z := marked i tag active (layout z.1) z.2
  left_inv e := by
    obtain ⟨g,⟨⟨q,k,d⟩,hk,hg⟩⟩ := e
    dsimp only at hg
    subst g; exact congrArg (fun u => marked i tag active u d) (layout.apply_symm_apply ⟨q,k,hk⟩)
  right_inv e := by
    obtain ⟨j,d⟩ := e
    exact Prod.ext (layout.symm_apply_apply _) rfl

include layout in
theorem mass : (∑ g,Fintype.card (Ports i tag active g))=2*G.nE := by
  rw [← Fintype.card_sigma,Fintype.card_congr (portsEquiv i tag active G layout)]; simp [mul_comm]

def sidePorts (g : Fin r) (d : Bool) := {e : Fin G.nE // grp (endpoint G e d)=g}
instance (g : Fin r) (d : Bool) : Fintype (sidePorts G grp g d) := inferInstanceAs (Fintype {e : Fin G.nE // _})
include align in
theorem group_cap (g : Fin r) :
    Fintype.card (Ports i tag active g)≤Fintype.card (sidePorts G grp g false)+Fintype.card (sidePorts G grp g true) := by
  let f (e : Ports i tag active g) : (sidePorts G grp g false) ⊕ (sidePorts G grp g true) :=
    if hd : e.val.2.2=true then .inr ⟨edge i tag active G layout e,hd ▸ identify i tag active G layout grp align e⟩
    else .inl ⟨edge i tag active G layout e,(Bool.eq_false_iff.mpr hd) ▸ identify i tag active G layout grp align e⟩
  have hf : Function.Injective f := by
    intro e k H
    obtain h|h := Bool.eq_false_or_eq_true e.val.2.2 <;> obtain l|l := Bool.eq_false_or_eq_true k.val.2.2 <;>
      simp [f,h,l] at H <;> apply unique_port i tag active G layout _ (h.trans l.symm)
    · exact congrArg (fun x : sidePorts G grp g true => x.val) (Sum.inr.inj H)
    · exact congrArg (fun x : sidePorts G grp g false => x.val) (Sum.inl.inj H)
  simpa using Fintype.card_le_of_injective f hf

theorem packet_cap (g : Fin r) (q : P) :
    Fintype.card {e : Ports i tag active g // e.val.1=q}≤2*2^a := by
  let f (e : {e : Ports i tag active g // e.val.1=q}) := e.val.val.2
  have H : Function.Injective f := by intro e k h; exact Subtype.ext (Subtype.ext (Prod.ext (e.property.trans k.property.symm) h))
  simpa [f,Pos,mul_comm] using Fintype.card_le_of_injective f H

theorem owner_cap (g : Fin r) (v : Fin G.nV) :
    Fintype.card {e : Ports i tag active g // endpoint G (edge i tag active G layout e) e.val.2.2=v}≤G.deg v := by
  let J := {e : Ports i tag active g // endpoint G (edge i tag active G layout e) e.val.2.2=v}
  have mem (e : J) : edge i tag active G layout e.val∈G.ports v := by
    have hv := e.property
    simp only [endpoint] at hv
    simp only [BipartiteMultigraph.ports,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
    split at hv <;> tauto
  let f (e : J) : Fin (G.deg v) := ⟨(G.ports v).idxOf (edge i tag active G layout e.val),List.idxOf_lt_length_iff.mpr (mem e)⟩
  have H : Function.Injective f := by
    intro e k h; apply Subtype.ext
    have E := congrArg (G.ports v).get h
    change (G.ports v).get ⟨_,_⟩=(G.ports v).get ⟨_,_⟩ at E
    simp only [List.idxOf_get] at E
    have both (e : J) : e.val.val.2.2=G.side v :=
      (endpoint_side G _ _).symm.trans (congrArg G.side e.property)
    exact unique_port i tag active G layout E ((both e).trans (both k).symm)
  simpa using Fintype.card_le_of_injective f H
end DetDLP.ContractionPortCounts
end

section

namespace DetDLP.LocalLabelSearch
open Finset

/-- Each penalty depends on at most four vertex labels. -/
structure Term (n q : ℕ) where
  arity : ℕ
  small : arity ≤ 4
  vertex : Fin arity → Fin n
  distinct : Function.Injective vertex
  penalty : (Fin arity → Fin q) → ℕ

abbrev Partial (n q : ℕ) := Fin n → Option (Fin q)

def termScore {n q : ℕ} (t : Term n q) (s : Partial n q) : ℕ :=
  q^(4-t.arity) * ∑ z : Fin t.arity → Fin q,
    t.penalty (fun h => (s (t.vertex h)).getD (z h))

def score {n q : ℕ} (T : List (Term n q)) (s : Partial n q) : ℕ :=
  (T.map (termScore · s)).sum

private def swapAt {q r : ℕ} (h : Fin r) : (Fin q × (Fin r → Fin q)) ≃ (Fin q × (Fin r → Fin q)) where
  toFun x := (x.2 h, Function.update x.2 h x.1)
  invFun x := (x.2 h, Function.update x.2 h x.1)
  left_inv x := by simp
  right_inv x := by simp

private theorem term_average {n q : ℕ} (t : Term n q) (s : Partial n q)
    (v : Fin n) (fresh : s v = none) :
    ∑ x : Fin q, termScore t (Function.update s v (some x)) = q * termScore t s := by
  classical
  let f (z : Fin t.arity → Fin q) := t.penalty fun h => (s (t.vertex h)).getD (z h)
  by_cases hm : ∃ h, t.vertex h = v
  · obtain ⟨h,rfl⟩ := hm
    have he (x : Fin q) (z : Fin t.arity → Fin q) :
        t.penalty (fun a => (Function.update s (t.vertex h) (some x) (t.vertex a)).getD (z a)) =
        f (Function.update z h x) := by
      congr 1
      funext a
      by_cases ha : a = h
      · simp [ha,fresh]
      · simp [Function.update_of_ne ha,Function.update_of_ne (t.distinct.ne ha)]
    have hsum : ∑ x : Fin q, ∑ z : Fin t.arity → Fin q, f (Function.update z h x) =
        q * ∑ z : Fin t.arity → Fin q, f z := by
      let F (a : Fin q × (Fin t.arity → Fin q)) := f a.2
      calc
        _ = ∑ a : Fin q × (Fin t.arity → Fin q), F (swapAt h a) := Fintype.sum_prod_type _ |>.symm
        _ = ∑ a : Fin q × (Fin t.arity → Fin q), F a := (swapAt h).sum_comp F
        _ = _ := by rw [Fintype.sum_prod_type]; simp [F]
    unfold termScore
    simp_rw [he]
    rw [← mul_sum,hsum]
    dsimp only [f]
    ring
  · have he (x : Fin q) : termScore t (Function.update s v (some x)) = termScore t s := by
      unfold termScore
      congr 1
      apply sum_congr rfl
      intro z _
      congr 1; funext h
      rw [Function.update_of_ne (fun h' => hm ⟨h,h'⟩)]
    simp [he]

theorem score_average {n q : ℕ} (T : List (Term n q)) (s : Partial n q)
    (v : Fin n) (h : s v = none) :
    ∑ x : Fin q, score T (Function.update s v (some x)) = q * score T s := by
  induction T with
  | nil => simp [score]
  | cons t ts ih =>
    simp only [score,List.map_cons,List.sum_cons] at ih ⊢
    rw [sum_add_distrib,term_average t s v h,ih,Nat.mul_add]

private def better {q : ℕ} (f : Fin q → ℕ) (x y : Fin q) := if f y < f x then y else x

private theorem fold_min {q : ℕ} (f : Fin q → ℕ) (xs : List (Fin q)) (start : Fin q) :
    let z := xs.foldl (better f) start
    f z ≤ f start ∧ ∀ x ∈ xs, f z ≤ f x := by
  induction xs generalizing start with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨h0,h1⟩ := ih (better f start x)
    have hl : f (better f start x) ≤ f start ∧ f (better f start x) ≤ f x := by
      unfold better; split <;> omega
    exact ⟨h0.trans hl.1,fun y h => by
      rcases List.mem_cons.mp h with rfl|h
      · exact h0.trans hl.2
      · exact h1 y h⟩

def chooseLabel {n q : ℕ} [NeZero q] (T : List (Term n q)) (s : Partial n q) (v : Fin n) :=
  let cost (x : Fin q) := score T (Function.update s v (some x))
  (List.finRange q).foldl (better cost) 0

theorem chooseLabel_le {n q : ℕ} [NeZero q] (T : List (Term n q)) (s : Partial n q) (v : Fin n)
    (hf : s v = none) :
    score T (Function.update s v (some (chooseLabel T s v))) ≤ score T s := by
  let f (x : Fin q) := score T (Function.update s v (some x))
  let x := chooseLabel T s v
  have hl (y : Fin q) : f x ≤ f y :=
    (fold_min f (List.finRange q) 0).2 y (by simp)
  have hs : q*f x ≤ q*score T s := by
    rw [← score_average T s v hf,← show (∑ _ : Fin q, f x)=q*f x by simp]
    exact sum_le_sum (fun y _ => hl y)
  exact Nat.le_of_mul_le_mul_left hs (Nat.pos_of_ne_zero (NeZero.ne q))

def fixLabels {n q : ℕ} [NeZero q] (T : List (Term n q)) : ℕ → Partial n q
  | 0 => fun _ => none
  | k+1 =>
    let s := fixLabels T k
    if h : k < n then Function.update s ⟨k,h⟩ (some (chooseLabel T s ⟨k,h⟩)) else s

theorem fixLabels_spec {n q : ℕ} [NeZero q] (T : List (Term n q)) (k : ℕ) (hk : k ≤ n) :
    (∀ i : Fin n, (fixLabels T k i).isSome ↔ i.val < k) ∧
    score T (fixLabels T k) ≤ score T (fun _ => none) := by
  induction k with
  | zero => simp [fixLabels]
  | succ k ih =>
    have h : k < n := by omega
    obtain ⟨hset,hscore⟩ := ih (by omega)
    let v : Fin n := ⟨k,h⟩
    have hf : fixLabels T k v = none := by
      cases he : fixLabels T k v with
      | none => rfl
      | some x => have hh := (hset v).mp (by simp [he]); exact False.elim (lt_irrefl k hh)
    simp only [fixLabels,dif_pos h]
    refine ⟨fun i => ?_,(chooseLabel_le T _ v hf).trans hscore⟩
    by_cases he : i = v
    · subst i; simp [v]
    · rw [Function.update_of_ne he,hset]
      have hv : i.val ≠ k := fun e => he (Fin.ext e)
      omega

def labeling {n q : ℕ} [NeZero q] (T : List (Term n q)) : Fin n → Fin q :=
  fun v => (fixLabels T n v).getD 0

/-- The executable search attains at most the average score of all assignments;
each trial inspects at most q^4 local tuples per term. -/
theorem labeling_bound {n q : ℕ} [NeZero q] (T : List (Term n q)) :
    q^4 * (T.map (fun t => t.penalty (fun h => labeling T (t.vertex h)))).sum ≤
    score T (fun _ => none) := by
  obtain ⟨hfill,h⟩ := fixLabels_spec T n le_rfl
  have hs (v : Fin n) : fixLabels T n v = some (labeling T v) := by
    have hv := (hfill v).mpr v.isLt
    cases he : fixLabels T n v <;> simp_all [labeling]
  have ht (t : Term n q) : termScore t (fixLabels T n) = q^4 * t.penalty (fun h => labeling T (t.vertex h)) := by
    simp [termScore,hs,Fintype.card_fun,← mul_assoc,← pow_add, Nat.sub_add_cancel t.small]
  have sum_eq (ts : List (Term n q)) :
      score ts (fixLabels T n) = q^4*(ts.map (fun t => t.penalty (fun h => labeling T (t.vertex h)))).sum := by
    induction ts with
    | nil => simp [score]
    | cons t ts ih =>
      simp only [score,List.map_cons,List.sum_cons] at ih ⊢
      rw [ht,ih,Nat.mul_add]
  rw [sum_eq] at h
  exact h

end DetDLP.LocalLabelSearch
end

section

namespace DetDLP.EdgeLabelPartition
open Finset LocalLabelSearch

private def left (G : BipartiteMultigraph) (e : Fin G.nE) :=
  if G.side (G.endpoints e).1 then (G.endpoints e).2 else (G.endpoints e).1
private def right (G : BipartiteMultigraph) (e : Fin G.nE) :=
  if G.side (G.endpoints e).1 then (G.endpoints e).1 else (G.endpoints e).2

private theorem left_side (G : BipartiteMultigraph) (e : Fin G.nE) : G.side (left G e) = false := by
  have h := G.bipartite e
  cases ha : G.side (G.endpoints e).1 <;> cases hb : G.side (G.endpoints e).2 <;> simp_all [left]
private theorem right_side (G : BipartiteMultigraph) (e : Fin G.nE) : G.side (right G e) = true := by
  have h := G.bipartite e
  cases ha : G.side (G.endpoints e).1 <;> cases hb : G.side (G.endpoints e).2 <;> simp_all [right]
private theorem lr_ne (G : BipartiteMultigraph) (e f : Fin G.nE) : left G e ≠ right G f := by
  intro h
  have he := left_side G e
  rw [h,right_side] at he
  contradiction

private def eqTwo {q : ℕ} (z : Fin 2 → Fin q) : ℕ := if z 0 = z 1 then 1 else 0
private def eqFour {q : ℕ} (z : Fin 4 → Fin q) : ℕ :=
  if z 0 = z 1 ∧ z 2 = z 3 then 1 else 0

private theorem sum_eqTwo (q : ℕ) : ∑ z : Fin 2 → Fin q, eqTwo z = q := by
  classical
  let e : {z : Fin 2 → Fin q // z 0 = z 1} ≃ Fin q :=
    { toFun z := z.1 0, invFun x := ⟨![x,x],rfl⟩
      left_inv z := by apply Subtype.ext; funext i; fin_cases i <;> simp [z.property]
      right_inv _ := rfl }
  have hh := Fintype.card_congr e
  simpa [eqTwo,Fintype.card_subtype,Finset.sum_boole] using hh

private theorem sum_eqFour (q : ℕ) : ∑ z : Fin 4 → Fin q, eqFour z = q^2 := by
  classical
  let e : {z : Fin 4 → Fin q // z 0 = z 1 ∧ z 2 = z 3} ≃ Fin q × Fin q :=
    { toFun z := (z.1 0,z.1 2), invFun x := ⟨![x.1,x.1,x.2,x.2],rfl,rfl⟩
      left_inv z := by apply Subtype.ext; funext i; fin_cases i <;> simp [z.property.1,z.property.2]
      right_inv _ := rfl }
  have hh := Fintype.card_congr e
  simpa [eqFour,Fintype.card_subtype,Finset.sum_boole,pow_two] using hh

private def constantTerm (n q : ℕ) : Term n q :=
  ⟨0,by decide,Fin.elim0,fun x => Fin.elim0 x,fun _ => 1⟩

private def pairTerm {n q : ℕ} (x y : Fin n) (h : x ≠ y) : Term n q :=
  ⟨2,by decide,![x,y],by intro i j; fin_cases i <;> fin_cases j <;> simp_all [Ne.symm h],eqTwo⟩

private def fourTerm (G : BipartiteMultigraph) (q : ℕ) (e f : Fin G.nE)
    (hl : left G e ≠ left G f) (hr : right G e ≠ right G f) : Term G.nV q :=
  ⟨4,by decide,![left G e,left G f,right G e,right G f],by
      intro x y
      fin_cases x <;> fin_cases y <;> simp_all [lr_ne,Ne.symm hl,Ne.symm hr,Ne.symm (lr_ne G _ _)],eqFour⟩

private def edgeTerm (G : BipartiteMultigraph) (q : ℕ) (e f : Fin G.nE) : Term G.nV q :=
  if hl : left G e = left G f then
    if hr : right G e = right G f then constantTerm _ _ else pairTerm _ _ hr
  else if hr : right G e = right G f then pairTerm _ _ hl
  else fourTerm G q e f hl hr

private def pairCollision (G : BipartiteMultigraph) {q : ℕ} (e f : Fin G.nE) (L : Fin G.nV → Fin q) : ℕ :=
  if (L (left G e),L (right G e)) = (L (left G f),L (right G f)) then 1 else 0

private theorem cost_edge (G : BipartiteMultigraph) (q : ℕ) (e f : Fin G.nE)
    (L : Fin G.nV → Fin q) :
    (edgeTerm G q e f).penalty (fun i => L ((edgeTerm G q e f).vertex i)) =
    pairCollision G e f L := by
  by_cases hl : left G e = left G f
  · by_cases hr : right G e = right G f
    · have he : edgeTerm G q e f = constantTerm _ _ := by rw [edgeTerm,dif_pos hl,dif_pos hr]
      rw [he]; simp [constantTerm,pairCollision,hl,hr]
    · have he : edgeTerm G q e f = pairTerm _ _ hr := by rw [edgeTerm,dif_pos hl,dif_neg hr]
      rw [he]; simp [pairTerm,pairCollision,eqTwo,hl]
  · by_cases hr : right G e = right G f
    · have he : edgeTerm G q e f = pairTerm _ _ hl := by rw [edgeTerm,dif_neg hl,dif_pos hr]
      rw [he]; simp [pairTerm,pairCollision,eqTwo,hr]
    · have he : edgeTerm G q e f = fourTerm G q e f hl hr := by rw [edgeTerm,dif_neg hl,dif_neg hr]
      rw [he]; simp [fourTerm,pairCollision,eqFour,Prod.ext_iff]
      by_cases h : L (left G e) = L (left G f) <;> by_cases k : L (right G e) = L (right G f) <;> simp_all [h,k]

private theorem initial_edge (G : BipartiteMultigraph) (q : ℕ) [NeZero q] (e f : Fin G.nE) :
    termScore (edgeTerm G q e f) (fun _ => none) ≤
      q^2 + (if left G e = left G f ∨ right G e = right G f then q^4 else 0) := by
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hm : q^2*q ≤ q^4 := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right hq (by decide)
  have hs2 : (∑ z : Fin 2 → Fin q, eqTwo (fun h => z h)) = q := sum_eqTwo q
  have hs4 : (∑ z : Fin 4 → Fin q, eqFour (fun h => z h)) = q^2 := sum_eqFour q
  have hs0 : (∑ _ : Fin 0 → Fin q, 1 : ℕ) = 1 := by simp [Fintype.card_fun]
  have hc : termScore (constantTerm G.nV q) (fun _ => none) = q^4 := by
    change q^(4-0) * (∑ _ : Fin 0 → Fin q, 1 : ℕ) = q^4
    rw [hs0]; simp
  have hp (x y : Fin G.nV) (h : x ≠ y) : termScore (pairTerm (q := q) x y h) (fun _ => none) = q^2*q := by
    change q^2 * (∑ z : Fin 2 → Fin q, eqTwo z) = _
    rw [sum_eqTwo]
  by_cases hl : left G e = left G f
  · by_cases hr : right G e = right G f
    · rw [edgeTerm,dif_pos hl,dif_pos hr,hc,if_pos (Or.inl hl)]; omega
    · rw [edgeTerm,dif_pos hl,dif_neg hr,hp,if_pos (Or.inl hl)]; omega
  · by_cases hr : right G e = right G f
    · rw [edgeTerm,dif_neg hl,dif_pos hr,hp,if_pos (Or.inr hr)]; omega
    · rw [edgeTerm,dif_neg hl,dif_neg hr,if_neg (by tauto),add_zero]
      change q^(4-4) * (∑ z : Fin 4 → Fin q, eqFour z) ≤ _
      rw [sum_eqFour]; simp

private def edgePairs (G : BipartiteMultigraph) :=
  (List.finRange G.nE).flatMap fun e => (List.finRange G.nE).map fun f => (e,f)

private def terms (G : BipartiteMultigraph) (q : ℕ) :=
  (edgePairs G).map fun p => edgeTerm G q p.1 p.2

private theorem pair_sum {n : ℕ} (f : Fin n × Fin n → ℕ) :
    (((List.finRange n).flatMap fun e => (List.finRange n).map fun z => (e,z)).map f).sum =
    ∑ e, ∑ z, f (e,z) := by
  have hf (l : List (Fin n)) : (l.flatMap (fun a => (List.finRange n).map (fun z => f (a,z)))).sum =
      (l.map fun a => ((List.finRange n).map fun z => f (a,z)).sum).sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  simpa [List.map_flatMap,List.map_map,Function.comp_def,Fin.sum_univ_def] using hf (List.finRange n)

private theorem shared_subset (G : BipartiteMultigraph) (e f : Fin G.nE)
    (h : left G e = left G f ∨ right G e = right G f) :
    f ∈ G.ports (left G e) ∨ f ∈ G.ports (right G e) := by
  rcases h with hl|hr
  · left; rw [hl]; cases h : G.side (G.endpoints f).1 <;> simp [BipartiteMultigraph.ports,left,h]
  · right; rw [hr]; cases h : G.side (G.endpoints f).1 <;> simp [BipartiteMultigraph.ports,right,h]

private theorem ports_card (G : BipartiteMultigraph) (v : Fin G.nV) :
    (G.ports v).toFinset.card ≤ G.maxDeg := by
  refine (List.toFinset_card_le _).trans ?_
  change G.deg v ≤ (univ : Finset (Fin G.nV)).sup G.deg
  exact Finset.le_sup (f := G.deg) (Finset.mem_univ v)

private theorem shared_card (G : BipartiteMultigraph) (e : Fin G.nE) :
    (univ.filter fun f => left G e = left G f ∨ right G e = right G f).card ≤ 2*G.maxDeg := by
  let S := (G.ports (left G e)).toFinset
  let T := (G.ports (right G e)).toFinset
  have h : (univ.filter fun f => left G e = left G f ∨ right G e = right G f) ⊆ S ∪ T := by
    intro f hf
    simpa [S,T] using shared_subset G e f (mem_filter.mp hf).2
  calc
    _ ≤ (S ∪ T).card := card_le_card h
    _ ≤ S.card+T.card := card_union_le _ _
    _ ≤ _ := by have := ports_card G (left G e); have := ports_card G (right G e); dsimp [S,T]; omega

/-- Ordered pairs of edges sharing both endpoint labels. -/
def collisions (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) : ℕ :=
  ∑ e : Fin G.nE, ∑ f : Fin G.nE, pairCollision G e f L

def labels (G : BipartiteMultigraph) (q : ℕ) [NeZero q] : Fin G.nV → Fin q := labeling (terms G q)

private theorem initial_edge_sum (G : BipartiteMultigraph) (q : ℕ) [NeZero q] :
    score (terms G q) (fun _ => none) ≤ G.nE*(G.nE*q^2+2*G.maxDeg*q^4) := by
  have per (e : Fin G.nE) :
      (∑ f : Fin G.nE, termScore (edgeTerm G q e f) (fun _ => none)) ≤
        G.nE*q^2 + 2*G.maxDeg*q^4 := by
    calc
      _ ≤ ∑ f : Fin G.nE, (q^2 + if left G e = left G f ∨ right G e = right G f then q^4 else 0) :=
        sum_le_sum fun f _ => initial_edge G q e f
      _ ≤ _ := by
        rw [sum_add_distrib,Finset.sum_ite,Finset.sum_const_zero,add_zero]
        simp only [Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
        simpa using Nat.add_le_add_left (Nat.mul_le_mul_right (q^4) (shared_card G e)) (G.nE*q^2)
  have hs := sum_le_sum (s := univ) (fun e _ => per e)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  norm_cast at hs
  simpa only [score,terms,edgePairs,List.map_map,Function.comp_def,pair_sum] using hs
private def finalScore {n q : ℕ} (ts : List (Term n q)) (L : Fin n → Fin q) :=
  (ts.map (fun t => t.penalty (fun i => L (t.vertex i)))).sum

private theorem edge_final (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) :
    finalScore (terms G q) L = collisions G L := by
  simp only [finalScore,terms,edgePairs,List.map_map,Function.comp_def,cost_edge,pair_sum,collisions]

theorem collision_bound (G : BipartiteMultigraph) (q : ℕ) [NeZero q] :
    q^2 * collisions G (labels G q) ≤ G.nE^2+2*G.nE*G.maxDeg*q^2 := by
  have hl := labeling_bound (terms G q)
  change q^4 * finalScore (terms G q) (labels G q) ≤ _ at hl
  rw [edge_final] at hl
  have hu := hl.trans (initial_edge_sum G q)
  have hcancel : q^2 * (q^2 * collisions G (labels G q)) ≤
      q^2 * (G.nE^2+2*G.nE*G.maxDeg*q^2) := by
    norm_cast at hu
    nlinarith only [hu]
  exact Nat.le_of_mul_le_mul_left hcancel (pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) _)
private def edgeCell (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) (e : Fin G.nE) :=
  (L (left G e),L (right G e))

def cellSize (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) (c : Fin q × Fin q) : ℕ :=
  ∑ e, if edgeCell G L e = c then 1 else 0

theorem cell_sum (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) :
    ∑ c, cellSize G L c = G.nE := by
  unfold cellSize
  rw [sum_comm]; simp

theorem cell_square_sum (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) :
    ∑ c, cellSize G L c ^ 2 = collisions G L := by
  have hp (c : Fin q × Fin q) : cellSize G L c ^2 =
      ∑ e, if edgeCell G L e = c then cellSize G L c else 0 := by
    calc
      _ = (∑ e, if edgeCell G L e = c then 1 else 0)*cellSize G L c := by rw [pow_two]; rfl
      _ = _ := by rw [sum_mul]; simp [ite_mul]
  simp_rw [hp]; rw [sum_comm]; simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  unfold cellSize collisions pairCollision edgeCell
  apply sum_congr rfl; intro e he
  apply sum_congr rfl; intro f hf
  split_ifs <;> simp_all [eq_comm]

theorem cell_cap (G : BipartiteMultigraph) (q : ℕ) [NeZero q] (c : Fin q × Fin q)
    (hm : 2*G.maxDeg*q^4 ≤ G.nE) :
    q^2*cellSize G (labels G q) c ≤ 2*G.nE := by
  let X (g : Fin q × Fin q) : ℤ := cellSize G (labels G q) g
  let M : ℤ := G.nE
  let Q : ℤ := q
  let D : ℤ := G.maxDeg
  have hsum : ∑ g, X g = M := by dsimp only [X,M]; exact_mod_cast cell_sum G (labels G q)
  have henergy : Q^2*(∑ g, X g ^2) ≤ M^2+2*M*D*Q^2 := by
    have h := collision_bound G q
    rw [← cell_square_sum] at h
    dsimp only [Q,X,M,D]; exact_mod_cast h
  have hcard : (Fintype.card (Fin q × Fin q) : ℤ) = Q^2 := by simp [Q,pow_two]
  have hvar : ∑ g, (Q^2*X g-M)^2 = Q^4*∑ g, X g^2-Q^2*M^2 := by
    calc
      _ = ∑ g, (Q^4*X g^2-(2*Q^2*M)*X g+M^2) := by apply sum_congr rfl; intros; ring
      _ = _ := by rw [sum_add_distrib,sum_sub_distrib,← mul_sum,← mul_sum,hsum,sum_const,card_univ,nsmul_eq_mul,hcard]; ring
  have hsingle := Finset.single_le_sum (f := fun g => (Q^2*X g-M)^2)
    (fun g _ => sq_nonneg _) (mem_univ c)
  rw [hvar] at hsingle
  have he := mul_le_mul_of_nonneg_left henergy (sq_nonneg Q)
  have hm' : 2*D*Q^4 ≤ M := by dsimp only [D,Q,M]; exact_mod_cast hm
  have hh := mul_le_mul_of_nonneg_left hm' (show 0 ≤ M by dsimp [M]; positivity)
  have hx : 0 ≤ Q^2*X c := by dsimp [Q,X]; positivity
  have h : Q^2 * X c ≤ 2*M := by
    by_contra! hf
    nlinarith only [hsingle,he,hh,mul_pos (sub_pos.mpr hf) (show 0 < Q^2*X c by dsimp [M] at hf; omega)]
  dsimp only [Q,X,M] at h
  exact_mod_cast h

private def weighted {n q : ℕ} (w : ℕ) (t : Term n q) : Term n q :=
  { t with penalty := fun z => w*t.penalty z }

private theorem weight_score {n q : ℕ} (w : ℕ) (ts : List (Term n q)) (p : Partial n q) :
    score (ts.map (weighted w)) p = w * score ts p := by
  induction ts with
  | nil => simp [score]
  | cons t ts ih =>
    have ht : termScore (weighted w t) p = w*termScore t p := by
      unfold termScore
      change q^(4-t.arity) * (∑ z : Fin t.arity → Fin q, w*t.penalty (fun h => (p (t.vertex h)).getD (z h))) = _
      rw [← mul_sum,mul_left_comm]
    simp only [score,List.map_cons,List.sum_cons] at ih ⊢
    rw [ht,ih,Nat.mul_add]

private theorem weight_final {n q : ℕ} (w : ℕ) (ts : List (Term n q)) (L : Fin n → Fin q) :
    finalScore (ts.map (weighted w)) L = w * finalScore ts L := by
  induction ts with
  | nil => simp [finalScore]
  | cons t ts ih => simp only [finalScore,List.map_cons,List.sum_cons,weighted] at ih ⊢; rw [ih,Nat.mul_add]

private def digitMatch {q s : ℕ} (d : Fin q → Fin s) (z : Fin 2 → Fin q) : ℕ :=
  if d (z 0) = d (z 1) then 1 else 0

private def legTerm {n q s : ℕ} (d : Fin q → Fin s) (x y : Fin n) : Term n q :=
  if h : x = y then constantTerm _ _ else
    { (pairTerm (q := q) x y h) with penalty := digitMatch d }

private theorem leg_final {n q s : ℕ} (d : Fin q → Fin s) (x y : Fin n) (L : Fin n → Fin q) :
    (legTerm d x y).penalty (fun i => L ((legTerm d x y).vertex i)) =
      if d (L x) = d (L y) then 1 else 0 := by
  by_cases h : x = y
  · have he : legTerm d x y = constantTerm n q := by rw [legTerm,dif_pos h]
    rw [he]; simp [constantTerm,h]
  · have he : legTerm d x y = { (pairTerm (q := q) x y h) with penalty := digitMatch d } := by rw [legTerm,dif_neg h]
    rw [he]; simp [pairTerm,digitMatch]

private theorem leg_initial {n q s : ℕ} (d : Fin q → Fin s)
    (hd : s * (∑ z, digitMatch d z) ≤ q^2) (x y : Fin n) :
    s * termScore (legTerm d x y) (fun _ => none) ≤
       q^4 + (if x = y then s*q^4 else 0) := by
  by_cases h : x = y
  · have he : legTerm d x y = constantTerm n q := by rw [legTerm,dif_pos h]
    rw [he,if_pos h]
    have hs0 : (∑ _ : Fin 0 → Fin q, 1 : ℕ) = 1 := by simp
    change s*(q^(4-0)*(∑ _ : Fin 0 → Fin q, 1 : ℕ)) ≤ _
    rw [hs0]; simp
  · simp only [legTerm,dif_neg h,if_neg h,add_zero]
    change s*(q^2*(∑ z, digitMatch d z)) ≤ q^4
    have hi := Nat.mul_le_mul_left (q^2) hd
    nlinarith only [hi]

private def legTerms {a n q s b : ℕ} (d : Fin a → Fin q → Fin s) (host : Fin b → Fin n) :=
  (List.finRange a).flatMap fun i =>
    ((List.finRange b).flatMap fun x => (List.finRange b).map fun y => (x,y)).map
      fun p => legTerm (d i) (host p.1) (host p.2)

private theorem flat_sum {α γ : Type*} (F : α → List γ) (H : γ → ℕ) (l : List α) :
    ((l.flatMap F).map H).sum = (l.map fun x => ((F x).map H).sum).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

private theorem leg_cost_sum {a n q s b : ℕ} (d : Fin a → Fin q → Fin s) (host : Fin b → Fin n)
    (H : Term n q → ℕ) :
    ((legTerms d host).map H).sum = ∑ i, ∑ x, ∑ y, H (legTerm (d i) (host x) (host y)) := by
  rw [legTerms,flat_sum,← Fin.sum_univ_def]
  simp only [List.map_map,Function.comp_def,pair_sum]

def terminalCollisions {a n q s b : ℕ} (d : Fin a → Fin q → Fin s) (host : Fin b → Fin n)
    (L : Fin n → Fin q) : ℕ :=
  ∑ i, ∑ x, ∑ y, if d i (L (host x)) = d i (L (host y)) then 1 else 0

private theorem terminal_initial {a n q s b : ℕ} (d : Fin a → Fin q → Fin s) (host : Fin b → Fin n)
    (τ : ℕ) (ht : ∀ x, (univ.filter fun y => host x = host y).card ≤ τ)
    (hd : ∀ i, s * (∑ z, digitMatch (d i) z) ≤ q^2) :
    s * score (legTerms d host) (fun _ => none) ≤ a*(b*(b*q^4+τ*(s*q^4))) := by
  have per (i : Fin a) (x : Fin b) :
      (∑ y, s * termScore (legTerm (d i) (host x) (host y)) (fun _ => none)) ≤
        b*q^4+τ*(s*q^4) := by
    calc
      _ ≤ ∑ y, (q^4 + if host x = host y then s*q^4 else 0) := sum_le_sum fun y _ => leg_initial _ (hd i) _ _
      _ ≤ _ := by
        rw [sum_add_distrib,Finset.sum_ite,Finset.sum_const_zero,add_zero]
        simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (ht x)) _
  unfold score
  rw [leg_cost_sum]
  simp_rw [mul_sum]
  have hh := sum_le_sum (s := univ) (fun i _ => sum_le_sum (s := univ) (fun x _ => per i x))
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  exact_mod_cast hh

/-- Simultaneous edge and terminal collision control, with arbitrary integral objective weights. -/
theorem joint_collision_bound (G : BipartiteMultigraph) (q : ℕ) [NeZero q] {a s b : ℕ}
    (d : Fin a → Fin q → Fin s) (host : Fin b → Fin G.nV) (τ w v : ℕ)
    (ht : ∀ x, (univ.filter fun y => host x = host y).card ≤ τ)
    (hd : ∀ i, s * (∑ z, digitMatch (d i) z) ≤ q^2) :
    ∃ L : Fin G.nV → Fin q,
      s*q^2*(w*collisions G L + v*terminalCollisions d host L) ≤
        s*w*(G.nE^2+2*G.nE*G.maxDeg*q^2) + v*a*b*q^2*(b+τ*s) := by
  let E := terms G q
  let T := legTerms d host
  let ts := E.map (weighted w) ++ T.map (weighted v)
  let L := labeling ts
  refine ⟨L,?_⟩
  have he := initial_edge_sum G q
  have ht' := terminal_initial d host τ ht hd
  have hl := labeling_bound ts
  have hfin : finalScore ts L = w*collisions G L + v*terminalCollisions d host L := by
    change finalScore (_++_) L = _
    simp only [finalScore,List.map_append,List.sum_append]
    change finalScore (E.map _) L + finalScore (T.map _) L = _
    rw [weight_final,weight_final,edge_final]
    simp only [T,finalScore,leg_cost_sum,leg_final,terminalCollisions]
  have hinit : score ts (fun _ => none) = w*score E (fun _ => none)+v*score T (fun _ => none) := by
    simp only [ts,score,List.map_append,List.sum_append]
    exact congrArg₂ (·+·) (weight_score w E _) (weight_score v T _)
  change q^4 * finalScore ts L ≤ score ts (fun _ => none) at hl
  rw [hfin,hinit] at hl
  have R := Nat.mul_le_mul_left s hl
  have F := Nat.mul_le_mul_left (s*w) he
  have H := Nat.mul_le_mul_left v ht'
  change s * (q^4 * _) ≤ s*(w*score (terms G q) _ + v*score (legTerms d host) _) at R
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < q^2 from pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) _)
  nlinarith only [R,F,H]


private theorem coord_balanced {q s : ℕ} {R : Type*} [Fintype R]
    (e : Fin q ≃ Fin s × R) :
    s * (∑ z, digitMatch (fun t => (e t).1) z) = q^2 := by
  classical
  let P (z : Fin 2 → Fin q) := (e (z 0)).1 = (e (z 1)).1
  let equiv : {z // P z} ≃ Fin s × (R × R) := {
    toFun := fun z => ((e (z.1 0)).1,(e (z.1 0)).2,(e (z.1 1)).2)
    invFun := fun t => ⟨![e.symm (t.1,t.2.1),e.symm (t.1,t.2.2)],by simp [P]⟩
    left_inv := by
      intro z; apply Subtype.ext; funext k
      fin_cases k
      · simp
      · have hh := z.property
        change (e (z.1 0)).1 = (e (z.1 1)).1 at hh
        simp [hh]
    right_inv := by intro t; simp }
  have hcount : (∑ z, digitMatch (fun t => (e t).1) z) = s*Fintype.card R^2 := by
    simpa [digitMatch,P,Fintype.card_subtype,pow_two,mul_assoc] using Fintype.card_congr equiv
  have hq : q = s*Fintype.card R := by simpa using Fintype.card_congr e
  rw [hcount,hq]; ring

/-- Ordered label cells and base-s digit legs can be balanced with one vertex assignment. -/
theorem digit_collision_bound (G : BipartiteMultigraph) (s : ℕ) [NeZero s] (a : ℕ)
    {b : ℕ} (host : Fin b → Fin G.nV) (τ w v : ℕ)
    (ht : ∀ x, (univ.filter fun y => host x = host y).card ≤ τ) :
    ∃ L : Fin G.nV → Fin (s^a),
      s*(s^a)^2*(w*collisions G L +
          v*terminalCollisions (fun i z => finFunctionFinEquiv.symm z i) host L) ≤
        s*w*(G.nE^2+2*G.nE*G.maxDeg*(s^a)^2) + v*a*b*(s^a)^2*(b+τ*s) := by
  apply joint_collision_bound G _ _ _ _ _ _ ht
  intro i
  let e : Fin (s^a) ≃ Fin s × ({j : Fin a // j ≠ i} → Fin s) :=
    finFunctionFinEquiv.symm.trans (Equiv.funSplitAt i (Fin s))
  exact (coord_balanced e).le

end DetDLP.EdgeLabelPartition
end

section

namespace DetDLP.PacketSlotLayout
open Finset

abbrev SymbolPair (r : ℕ) := Fin r × Fin r
def flip {r : ℕ} (s : SymbolPair r × Bool) : SymbolPair r × Bool :=
  let (x,y) := s.1
  if x < y then (if s.2 then (y,x) else (x,y),false)
  else if y < x then (if s.2 then (x,y) else (y,x),true)
  else ((x,y),s.2)

theorem flip_twice {r : ℕ} (s : SymbolPair r × Bool) : flip (flip s)=s := by
  obtain ⟨⟨x,y⟩,b⟩ := s
  rcases lt_trichotomy x y with h|rfl|h <;> cases b <;>
    simp_all [flip,not_lt_of_gt]

def orient {r : ℕ} (p : SymbolPair r) (b : Bool) : SymbolPair r :=
  if b then (max p.1 p.2,min p.1 p.2) else (min p.1 p.2,max p.1 p.2)

theorem flip_orients {r : ℕ} (s : SymbolPair r × Bool) : orient (flip s).1 (flip s).2 = s.1 := by
  obtain ⟨⟨x,y⟩,b⟩ := s
  rcases lt_trichotomy x y with h|rfl|h <;> cases b <;>
    simp_all [flip,orient,not_lt_of_gt,min_eq_left,min_eq_right,max_eq_left,max_eq_right,le_of_lt]

abbrev Cell (r a : ℕ) := Fin a → SymbolPair r
def unpackBits {a : ℕ} (s : Fin (2^a)) (i : Fin a) : Bool := finTwoEquiv (finFunctionFinEquiv.symm s i)
def packBits {a : ℕ} (s : Fin a → Bool) : Fin (2^a) := finFunctionFinEquiv (fun i => finTwoEquiv.symm (s i))
@[simp] theorem unpack_pack {a : ℕ} (s : Fin a → Bool) (i : Fin a) : unpackBits (packBits s) i=s i := by
  simp [unpackBits,packBits]
@[simp] theorem pack_unpack {a : ℕ} (s : Fin (2^a)) : packBits (unpackBits s)=s := by
  simp [unpackBits,packBits]
theorem bits_eq {a} (s : Fin (2^a)) (i : Fin a) : unpackBits s i=s.val.testBit i.val := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change ((_ : Fin 2) == 1)=_
  change decide ((finFunctionFinEquiv.symm s i:Fin 2)=1)=_
  congr 1; exact propext Fin.ext_iff

def shuffle {r a : ℕ} (z : Cell r a × Fin (2^a)) : Cell r a × Fin (2^a) :=
  let f (i : Fin a) := flip (z.1 i,unpackBits z.2 i)
  (fun i => (f i).1, packBits (fun i => (f i).2))
theorem shuffle_twice {r a : ℕ} (z : Cell r a × Fin (2^a)) : shuffle (shuffle z)=z := by
  obtain ⟨c,s⟩ := z
  have e (i : Fin a) := flip_twice (c i,unpackBits s i)
  apply Prod.ext
  · funext i; simpa [shuffle] using congrArg Prod.fst (e i)
  · apply_fun unpackBits using fun x y h => by rw [← pack_unpack x,← pack_unpack y,h]
    funext i; simpa [shuffle] using congrArg Prod.snd (e i)

theorem slot_label {r a : ℕ} (z : Cell r a × Fin (2^a)) (i : Fin a) :
    orient ((shuffle z).1 i) ((shuffle z).2.val.testBit i.val)=z.1 i := by
  rw [← bits_eq]; simpa [shuffle] using flip_orients (z.1 i,unpackBits z.2 i)

def fiber {M r a : ℕ} (c : Fin M → Cell r a) (p : Cell r a) :=
  univ.filter (fun e => c e=p)
def rankAt {M r a : ℕ} (c : Fin M → Cell r a) (e : Fin M) : Fin (fiber c (c e)).card :=
  ((fiber c (c e)).orderIsoOfFin rfl).symm ⟨e,by simp [fiber]⟩

theorem rank_unique {M r a : ℕ} (c : Fin M → Cell r a) (e f : Fin M)
    (hc : c e=c f) (hr : (rankAt c e).val=(rankAt c f).val) : e=f := by
  let p := c f
  have em : e ∈ fiber c p := by simp [fiber,p,hc]
  have fm : f ∈ fiber c p := by simp [fiber,p]
  let iso := ((fiber c p).orderIsoOfFin rfl).symm
  have h1 : (iso ⟨e,em⟩).val = (rankAt c e).val := by simp [iso,rankAt,Finset.orderIsoOfFin_symm_apply,p,hc]
  have h2 : (iso ⟨f,fm⟩).val = (rankAt c f).val := rfl
  exact congrArg Subtype.val (iso.injective (Fin.ext (h1.trans (hr.trans h2.symm))))

def blocks (M D L : ℕ) := (2*M/D)/L+1

theorem layout {M r a : ℕ} (hr : 0 < r) (c : Fin M → Cell r a)
    (hcap : ∀ z,(r^a)^2*(fiber c z).card ≤ 2*M) (hpad : 2^a*(r^a)^2 ≤ M) :
    let L := 2^a
    let D := (r^a)^2
    let B := blocks M D L
    ∃ pos : Fin M → (Fin B × Cell r a) × Fin L, Function.Injective pos ∧
      (∀ e i,orient ((pos e).1.2 i) ((pos e).2.val.testBit i.val)=c e i) ∧
      Fintype.card (Fin B × Cell r a)*L ≤ 3*M := by
  intro L D B
  have hL : 0 < L := pow_pos (by decide) _
  have hD : 0 < D := pow_pos (pow_pos hr _) _
  have rankbound (e : Fin M) : (rankAt c e).val < B*L := by
    have hi := (rankAt c e).isLt
    have hb : (fiber c (c e)).card ≤ 2*M/D := (Nat.le_div_iff_mul_le hD).mpr (by simpa [D,mul_comm] using hcap (c e))
    exact (hi.trans_le hb).trans_le ((Nat.lt_mul_div_succ (2*M/D) hL).le.trans_eq (Nat.mul_comm ..))
  let chunk (e : Fin M) : Fin B := ⟨(rankAt c e).val/L,(Nat.div_lt_iff_lt_mul hL).mpr (rankbound e)⟩
  let slot (e : Fin M) : Fin L := ⟨(rankAt c e).val%L,Nat.mod_lt _ hL⟩
  let pos (e : Fin M) := ((chunk e,(shuffle (c e,slot e)).1),(shuffle (c e,slot e)).2)
  refine ⟨pos,?_,fun e i => slot_label (c e,slot e) i,?_⟩
  · intro e f h
    have hch := congrArg (fun z => z.1.1.val) h
    have hs := congrArg (fun z => (z.1.2,z.2)) h
    change shuffle (c e,slot e) = shuffle (c f,slot f) at hs
    have eq := congrArg shuffle hs; rw [shuffle_twice,shuffle_twice] at eq
    apply rank_unique c e f (congrArg Prod.fst eq)
    have hmod := congrArg (fun z => z.2.val) eq
    change (rankAt c e).val/L=(rankAt c f).val/L at hch
    change (rankAt c e).val%L=(rankAt c f).val%L at hmod
    rw [← Nat.mod_add_div (rankAt c e).val L,← Nat.mod_add_div (rankAt c f).val L,hch,hmod]
  · have C : Fintype.card (Cell r a) = D := by simp [Cell,SymbolPair,D,pow_two,mul_pow]
    rw [Fintype.card_prod,Fintype.card_fin,C]
    have hq := Nat.div_mul_le_self (2*M/D) L
    have hd := Nat.div_mul_le_self (2*M) D
    have H := (Nat.mul_le_mul_right D hq).trans hd
    change (2*M/D/L+1)*D*L ≤ 3*M
    change L*D ≤ M at hpad
    nlinarith only [H,hpad]

def pick {r a} (right : Bool) (i : Fin a) (z : Cell r a) := if right then (z i).2 else (z i).1

def swapLabels {r a} (x y : Fin r) (z : Cell r a) : Cell r a :=
  fun i => (Equiv.swap x y (z i).1,Equiv.swap x y (z i).2)

theorem pick_swap {r a} (u : Bool) (i : Fin a) (x y : Fin r) (z : Cell r a) :
    pick u i (swapLabels x y z)=Equiv.swap x y (pick u i z) := by cases u <;> rfl

def fiberEq {r a} (u : Bool) (i : Fin a) (x y : Fin r) :
    {z : Cell r a // pick u i z=x} ≃ {z : Cell r a // pick u i z=y} where
  toFun z := ⟨swapLabels x y z.val,by rw [pick_swap,z.property,Equiv.swap_apply_left]⟩
  invFun z := ⟨swapLabels x y z.val,by rw [pick_swap,z.property,Equiv.swap_apply_right]⟩
  left_inv z := by ext j <;> simp [swapLabels]
  right_inv z := by ext j <;> simp [swapLabels]

theorem class_card {r a} (u : Bool) (i : Fin a) (g : Fin r) :
    r*Fintype.card {z : Cell r a // pick u i z=g}=(r^a)^2 := by
  have H := Fintype.card_congr (Equiv.sigmaFiberEquiv (pick u i : Cell r a → Fin r))
  rw [Fintype.card_sigma] at H
  have hh (s : Fin r) := Fintype.card_congr (fiberEq u i s g)
  simp_rw [hh] at H
  simpa [Cell,SymbolPair,pow_two,mul_pow] using H

theorem symbol_cap {M r a} (hr : 0 < r) (c : Fin M → Cell r a)
    (hc : ∀ z,(r^a)^2*(fiber c z).card ≤ 2*M) (u : Bool) (i : Fin a) (g : Fin r) :
    r*Fintype.card {e : Fin M // pick u i (c e)=g} ≤ 2*M := by
  let D := (r^a)^2
  let T := 2*M/D
  have hD : 0 < D := pow_pos (pow_pos hr _) _
  have h (e : Fin M) : (rankAt c e).val < T :=
    (rankAt c e).isLt.trans_le ((Nat.le_div_iff_mul_le hD).mpr (by simpa [D,mul_comm] using hc (c e)))
  let f (e : {e : Fin M // pick u i (c e)=g}) : {z : Cell r a // pick u i z=g} × Fin T :=
    (⟨c e.val,e.property⟩,⟨(rankAt c e.val).val,h e.val⟩)
  have hf : Function.Injective f := by
    intro e d h
    exact Subtype.ext (rank_unique c _ _ (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h))
  have H := Nat.mul_le_mul_left r (Fintype.card_le_of_injective f hf)
  rw [Fintype.card_prod,Fintype.card_fin,← Nat.mul_assoc,class_card] at H
  exact H.trans (by simpa [T,D,mul_comm] using Nat.div_mul_le_self (2*M) D)

def labelCell {r a : ℕ} (s : Fin (r^a) × Fin (r^a)) : Cell r a :=
  fun i => (finFunctionFinEquiv.symm s.1 i,finFunctionFinEquiv.symm s.2 i)

def cellLabel {r a : ℕ} (s : Cell r a) : Fin (r^a) × Fin (r^a) :=
  (finFunctionFinEquiv (fun i => (s i).1),finFunctionFinEquiv (fun i => (s i).2))

@[simp] theorem cell_label {r a : ℕ} (s : Cell r a) : labelCell (cellLabel s)=s := by
  funext i; simp [cellLabel,labelCell]
@[simp] theorem label_cell {r a : ℕ} (s : Fin (r^a) × Fin (r^a)) : cellLabel (labelCell s)=s := by
  simp [labelCell,cellLabel]

def endpoints (G : BipartiteMultigraph) (e : Fin G.nE) : Fin G.nV × Fin G.nV :=
  if G.side (G.endpoints e).1 then (G.endpoints e).swap else G.endpoints e

def edgeLabels (G : BipartiteMultigraph) {r a : ℕ} (L : Fin G.nV → Fin (r^a)) (e : Fin G.nE) : Cell r a :=
  labelCell (L (endpoints G e).1,L (endpoints G e).2)

theorem graph_cap (G : BipartiteMultigraph) {r a : ℕ} (L : Fin G.nV → Fin (r^a))
    (h : ∀ z,(r^a)^2*EdgeLabelPartition.cellSize G L z ≤ 2*G.nE) :
    ∀ z,(r^a)^2*(fiber (edgeLabels G L) z).card ≤ 2*G.nE := by
  intro z
  have eq (e : Fin G.nE) : (edgeLabels G L e=z) ↔
      ((L (endpoints G e).1,L (endpoints G e).2)=cellLabel z) := by
    constructor
    · intro he; simpa only [edgeLabels,label_cell] using congrArg cellLabel he
    · intro he; simpa only [edgeLabels,cell_label] using congrArg labelCell he
  have hh := h (cellLabel z)
  unfold EdgeLabelPartition.cellSize at hh
  rw [Finset.sum_boole] at hh
  convert hh using 2
  congr 1
  ext e
  simp only [fiber,Finset.mem_filter,Finset.mem_univ,true_and,eq]
  change _ ↔ (L (if G.side (G.endpoints e).1 then (G.endpoints e).2 else (G.endpoints e).1),
    L (if G.side (G.endpoints e).1 then (G.endpoints e).1 else (G.endpoints e).2))=cellLabel z
  cases hs : G.side (G.endpoints e).1 <;> simp [endpoints,hs]

end DetDLP.PacketSlotLayout
end

section
namespace DetDLP.OriginalContractionLayout
open OrientedPacketInstance ContractionPortCounts Finset

theorem activate {E P : Type} [Fintype E] [DecidableEq P] {a : ℕ} (pos : E→P×Pos a) (inj : Function.Injective pos) :
    ∃ active : P→Finset (Pos a),∃ layout : E≃Address active,∀ e,
      ((layout e).1,(layout e).2.val)=pos e := by
  classical
  let active (q : P) := univ.filter (fun k : Pos a => ∃ e,pos e=(q,k))
  let f (e : E) : Address active := ⟨(pos e).1,(pos e).2,by simp [active]⟩
  have H : Function.Bijective f := by
    constructor
    · intro e e' h
      exact inj (congrArg (fun j : Address active => (j.1,j.2.val)) h)
    · rintro ⟨q,k,hk⟩
      obtain ⟨e,eq⟩ := (mem_filter.mp hk).2
      refine ⟨e,?_⟩
      have mono : Function.Injective (fun x : Address active => (x.1,x.2.val)) := by
        rintro ⟨y,j,hj⟩ ⟨y',j',hj'⟩ eq
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
        rfl
      exact mono eq
  exact ⟨active,Equiv.ofBijective f H,fun _ => rfl⟩

theorem of_labels (G : BipartiteMultigraph) {r a : ℕ} [NeZero r]
    (lab : Fin G.nV→Fin (r^a)) (bounds : ∀ z,(r^a)^2*EdgeLabelPartition.cellSize G lab z≤2*G.nE)
    (hpad : 2^a*(r^a)^2≤G.nE) :
    let grp (i : Fin a) (v : Fin G.nV) : Fin r := finFunctionFinEquiv.symm (lab v) i
    ∃ (N : ℕ) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active) (tag : Fin N→Fin a→Fin r×Fin r),
      N*2^a≤3*G.nE ∧ (∀ i,Compat i (fun q => tag q i) active G L (grp i)) ∧
      ∀ i d g,r*Fintype.card (sidePorts G (grp i) g d)≤2*G.nE := by
  classical
  intro grp
  let sides := PacketSlotLayout.endpoints G
  let cells := PacketSlotLayout.edgeLabels G (r:=r) (a:=a) lab
  have caps := PacketSlotLayout.graph_cap G (r:=r) (a:=a) lab bounds
  have hr := Nat.pos_of_ne_zero (NeZero.ne r)
  let n := PacketSlotLayout.blocks G.nE ((r^a)^2) (2^a)
  obtain ⟨pos,inj,orient,cap⟩ := PacketSlotLayout.layout hr cells caps hpad
  let P := Fin n×(Fin a→Fin r×Fin r)
  let idx := Fintype.equivFin P
  let tag (j : Fin (Fintype.card P)) := (idx.symm j).2
  let pos' (e : Fin G.nE) := (idx (pos e).1,(pos e).2)
  have h : Function.Injective pos' := by
    intro e e' eq
    exact inj (Prod.ext (idx.injective (congrArg Prod.fst eq)) (congrArg (fun x : Fin (Fintype.card P)×Pos a => x.2) eq))
  obtain ⟨active,L,hL⟩ := activate pos' h
  have endpoint_eq (e : Fin G.nE) (d : Bool) :
      endpoint G e d=if d then (sides e).2 else (sides e).1 := by
    cases d <;> cases h : G.side (G.endpoints e).1 <;> simp [endpoint,sides,PacketSlotLayout.endpoints,h]
  refine ⟨_,active,L,tag,cap,?_,?_⟩
  · intro i e d
    have q : tag (L e).1 i=(pos e).1.2 i := by
      rw [show (L e).1=idx (pos e).1 from congrArg Prod.fst (hL e)]
      simp [tag]
    have k : (L e).2.val=(pos e).2 := congrArg Prod.snd (hL e)
    have O := (orient e i).symm
    change (grp i (sides e).1,grp i (sides e).2)=_ at O
    rw [endpoint_eq,k,group]
    simp only [q]
    cases d
    · exact (congrArg Prod.fst O).symm
    · exact (congrArg Prod.snd O).symm
  · intro i d g
    have eq : (fun e => grp i (endpoint G e d)=g)=(fun e => grp i (if d then (sides e).2 else (sides e).1)=g) := by
      funext e; rw [endpoint_eq]
    change r*Fintype.card {e : Fin G.nE // grp i (endpoint G e d)=g}≤_
    have conv := Equiv.subtypeEquivRight (fun e => iff_of_eq (congrFun eq e))
    calc
      _ = r*Fintype.card {e : Fin G.nE // grp i (if d then (sides e).2 else (sides e).1)=g} :=
        congrArg (r*·) (Fintype.card_congr conv)
      _ ≤ _ := by
        have H := PacketSlotLayout.symbol_cap hr cells caps d i g
        cases d <;> exact H

theorem layout (G : BipartiteMultigraph) (r a : ℕ) [NeZero r]
    (hs : 2*G.maxDeg*(r^a)^4≤G.nE) (hp : 2^a*(r^a)^2≤G.nE) :
    ∃ (N : ℕ) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
      (tag : Fin N→Fin a→Fin r×Fin r) (grp : Fin a→Fin G.nV→Fin r),
      N*2^a≤3*G.nE ∧
      (∀ i,Compat i (fun q => tag q i) active G L (grp i)) ∧
      ∀ i d g,r*Fintype.card (sidePorts G (grp i) g d)≤2*G.nE := by
  classical
  let lab := EdgeLabelPartition.labels G (r^a)
  obtain ⟨N,active,L,tag,cap,align,small⟩ := of_labels G (r:=r) (a:=a) lab
    (fun z => EdgeLabelPartition.cell_cap G _ z hs) hp
  exact ⟨N,active,L,tag,_,cap,align,small⟩

theorem terminal_layout (G : BipartiteMultigraph) {a b : ℕ} (host : Fin b→Fin G.nV) (τ : ℕ)
    (ht : ∀ x, (univ.filter fun y => host x=host y).card≤τ) (hb : 0<b*τ) (hm : 0<G.nE*G.maxDeg)
    (hs : (a+2)*(64^a)^4*G.maxDeg≤G.nE) (hp : 2^a*(64^a)^2≤G.nE) :
    ∃ (N : ℕ) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
      (tag : Fin N→Fin a→Fin 64×Fin 64) (grp : Fin a→Fin G.nV→Fin 64),
      N*2^a≤3*G.nE ∧
      (∀ i,Compat i (fun q => tag q i) active G L (grp i)) ∧
      (∀ i d g,64*Fintype.card (sidePorts G (grp i) g d)≤2*G.nE) ∧
      ∀ i g,32*(univ.filter fun x => grp i (host x)=g).card≤b+512*(a+2)*τ := by
  classical
  obtain ⟨lab,caps,small⟩ := terminal_packing_cell_bounds G a host τ ht hb hm hs
  obtain ⟨N,active,L,tag,cap,align,sideCap⟩ := of_labels G (r:=64) (a:=a) lab caps hp
  refine ⟨N,active,L,tag,_,cap,align,sideCap,?_⟩
  intro i g; simpa [sum_boole] using small i g
end DetDLP.OriginalContractionLayout
end

section

namespace DetDLP.PacketModeCapacity
open OrientedPacketInstance Finset
variable {a r : ℕ} {P : Type} [Fintype P] [DecidableEq P] (i : Fin a) (tag : P→Fin r×Fin r) (p : ℕ)
abbrev J := Mode i tag p
abbrev Index := (h : Fin r×P) × J i tag p h
def wt (x : Index i tag p) : ℕ := x.2.2.val
abbrev Ticket := ∀ h,J i tag p h→Fin p
def load (b : Ticket i tag p) := ∑ h,∑ j : J i tag p h,(j.2.val+1)*(b h j).val
def flat : Ticket i tag p ≃ (Index i tag p→Fin p) where
  toFun b := fun j => b j.1 j.2
  invFun b := fun h j => b ⟨h,j⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem flat_load (b : Ticket i tag p) :
    load i tag p b=∑ j : Index i tag p,(wt i tag p j+1)*(flat i tag p b j).val := by
  rw [Fintype.sum_sigma]; rfl

theorem capacity (n : ℕ) :
    (univ.filter (fun j : Index i tag p => wt i tag p j=n)).card≤Fintype.card P*2^(i.val+1) := by
  let U := {j : Index i tag p // wt i tag p j=n}
  let f (j : U) : P×Fin (2^(i.val+1)) := (j.val.1.2,j.val.2.1.val)
  have inj : Function.Injective f := by
    rintro ⟨⟨⟨g,q⟩,⟨⟨k,hk⟩,b⟩⟩,hb⟩ ⟨⟨⟨g',q'⟩,⟨⟨k',hk'⟩,b'⟩⟩,hb'⟩ h
    dsimp [f] at h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    have hB : b=b' := Fin.ext (hb.trans hb'.symm)
    subst b'
    dsimp only at hk hk'; subst g; subst g'
    rfl
  rw [← Fintype.card_subtype (fun j : Index i tag p => wt i tag p j=n)]
  simpa [U] using Fintype.card_le_of_injective f inj

theorem count (M : ℕ) (C u : ℝ) (hC : 0≤C) (hu : 0<u) (hp : 0<p) (hP : 0<Fintype.card P)
    (pack : Fintype.card P*2^a≤3*M)
    (prec : (p:ℝ)≤C*M*(2:ℝ)^(a-i.val)/u) :
    (((univ.filter (fun b : Ticket i tag p => load i tag p b<p)).card:ℕ):ℝ)≤
      Real.exp (3*Real.sqrt (6*C)*M/Real.sqrt u) := by
  classical
  let D := (2:ℝ)^(a-i.val)
  let B := Fintype.card P*2^(i.val+1)
  have BD : (B:ℝ)≤6*(M:ℝ)/D := by
    apply (le_div_iff₀ (by dsimp [D]; positivity)).mpr
    have e : (i.val+1)+(a-i.val)=a+1 := by have := i.isLt; omega
    have h : B*2^(a-i.val)≤6*M := by
      dsimp [B]; rw [Nat.mul_assoc,← pow_add,e,pow_succ,← Nat.mul_assoc]; omega
    dsimp [D]; exact_mod_cast h
  obtain ⟨_,H⟩ := weighted_mode_branching_bound (wt i tag p) B p (capacity i tag p)
    (Nat.mul_pos hP (by positivity)) hp M D u C (Nat.cast_nonneg _) (by dsimp [D]; positivity) hu hC BD prec
  let T := univ.filter (fun b : Ticket i tag p => load i tag p b<p)
  let F := univ.filter (fun f : Index i tag p→Fin p => (∑ j,(wt i tag p j+1)*(f j).val)<p)
  have eq : T.card=F.card := by
    apply Finset.card_bij (fun b _ => flat i tag p b)
    · intro b hb; simpa [F,T,← flat_load] using hb
    · intro b hb c hc eq; exact (flat i tag p).injective eq
    · intro f hf
      refine ⟨(flat i tag p).symm f,?_,(flat i tag p).apply_symm_apply f⟩
      simpa [T,F,flat_load] using hf
  change (T.card:ℝ)≤_; rw [eq]; exact H
end DetDLP.PacketModeCapacity
end

section

namespace DetDLP.ContractionSampleBounds
open Finset Polynomial OrientedPacketInstance ContractionPortCounts
theorem sample {a : ℕ} (G : BipartiteMultigraph) {N : ℕ} (active : Fin N→Finset (Pos a))
    (L : Fin G.nE ≃ Address active) (i : Fin a) (tag : Fin N→Fin 64×Fin 64) (grp : Fin G.nV→Fin 64)
    (hpacks : N*2^a≤3*G.nE) (hM : 0<G.nE) (align : Compat i tag active G L grp)
    (hs : ∀ d g,64*Fintype.card (sidePorts G grp g d)≤2*G.nE)
    (p : ℕ) (hp : 0<p) (t : ZMod (2^(a+1))) (ht : t≠0) (hi : padicValNat 2 t.val=i.val)
    (C u : ℝ) (hC : 0≤C) (hu : 0<u) (prec : (p:ℝ)≤C*G.nE*(2:ℝ)^(a-i.val)/u) :
    let J := Mode i tag p
    let beta := ∀ h,J h→Fin p
    let wt (b : beta) := ∑ h,∑ j : J h,(j.2.val+1)*(b h j).val
    let legal := univ.filter (fun b : beta => wt b<p)
    (legal.card:ℝ)≤Real.exp (3*Real.sqrt (6*C)*G.nE/Real.sqrt u) ∧
    ∃ U : ZMod (2^(a+1))→(ZMod (2^p))[X], Represents t U ∧
    ∀ (R : Type) [CommRing R] [Algebra (ZMod (2^p)) R]
      (T : Fin 64→Type) (V : (v : Fin G.nV)→T (grp v)→(Fin (G.deg v)→Bool)→R) (z : R),
    ∃ (H : Fin 64→BipartiteMultigraph)
      (child : beta→(g : Fin 64)→T g→(v : Fin (H g).nV)→(Fin ((H g).deg v)→Bool)→R),
      (∀ g,16*(H g).nE≤G.nE) ∧ (∑ g,(H g).nE)=2*G.nE ∧
      (∀ g,(H g).maxDeg ≤ max G.maxDeg (2*2^a)) ∧
      (∀ g,(H g).nV=Fintype.card {v : Fin G.nV // grp v=g}+N) ∧
      ∀ τ : ∀ g,T g,
        (∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
          DeformedContraction.weight (fun v => V v (τ (grp v))) x y *
            ∏ e,selector G active L U z x y e) =
          ∑ b ∈ legal,(2:R)^(wt b)*∏ g,BTNContract (H g) (child b g (τ g)) := by
  classical
  intro J beta wt legal
  have posN : 0<N := by
    obtain ⟨q,k⟩ := L ⟨0,hM⟩
    exact Nat.zero_lt_of_lt q.isLt
  constructor
  · apply PacketModeCapacity.count i tag p G.nE C u hC hu hp (by simpa using posN) (by simpa using hpacks) prec
  obtain ⟨U,rep,hh⟩ := oriented_dyadic_sample_child_contractions i hp t ht hi
  refine ⟨U,rep,?_⟩; intro R _ _ T V z
  obtain ⟨H,cnt,degrees,child,id⟩ := hh (Fin N) R G active L tag grp align T V z
  refine ⟨H,child,?_,?_,?_,?_,id⟩
  · intro g
    rw [(cnt g).1]
    have b := group_cap i tag active G L grp align g
    simp only [Ports] at b
    have x := hs false g
    have y := hs true g
    omega
  · calc
      (∑ g,(H g).nE)=∑ g,Fintype.card (Assigned i tag active g) := sum_congr rfl fun g _ => (cnt g).1
      _=2*G.nE := mass i tag active G L
  · intro g; apply degrees g
    · intro v
      exact (owner_cap i tag active G L g v).trans
        ((Finset.le_sup (f:=G.deg) (mem_univ v)).trans (le_max_left ..))
    · intro q; exact (packet_cap i tag active g q).trans (le_max_right ..)
  · intro g; simpa using (cnt g).2
end DetDLP.ContractionSampleBounds
end

section

namespace DetDLP.BoundedContractionStep
open Finset Polynomial OrientedPacketInstance

theorem full (G : BipartiteMultigraph) {a b : ℕ} (host : Fin b→Fin G.nV) (τ : ℕ)
    (ht : ∀ x,(univ.filter fun y => host x=host y).card≤τ) (hm : 0<G.nE*G.maxDeg)
    (hc : (a+2)*(64^a)^4*G.maxDeg≤G.nE) (hpad : 2^a*(64^a)^2≤G.nE) :
    ∃ (N : ℕ) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
      (tag : Fin N→Fin a→Fin 64×Fin 64) (grp : Fin a→Fin G.nV→Fin 64),
    N*2^a≤3*G.nE ∧ (∀ i g,32*(univ.filter fun x => grp i (host x)=g).card≤b+512*(a+2)*τ) ∧
    ∀ (i : Fin a) (p : ℕ) (hp : 0<p) (t : ZMod (2^(a+1))) (ht : t≠0) (hi : padicValNat 2 t.val=i.val)
      (C u : ℝ) (hC : 0≤C) (hu : 0<u) (prec : (p:ℝ)≤C*G.nE*(2:ℝ)^(a-i.val)/u),
    let J := Mode i (fun q => tag q i) p
    let beta := ∀ h,J h→Fin p
    let wt (b : beta) := ∑ h,∑ j : J h,(j.2.val+1)*(b h j).val
    let legal := univ.filter (fun b : beta => wt b<p)
    (legal.card:ℝ)≤Real.exp (3*Real.sqrt (6*C)*G.nE/Real.sqrt u) ∧
    ∃ U : ZMod (2^(a+1))→(ZMod (2^p))[X], Represents t U ∧
    ∀ (R : Type) [CommRing R] [Algebra (ZMod (2^p)) R]
      (T : Fin 64→Type) (V : (v : Fin G.nV)→T (grp i v)→(Fin (G.deg v)→Bool)→R) (z : R),
    ∃ (H : Fin 64→BipartiteMultigraph)
      (child : beta→(g : Fin 64)→T g→(v : Fin (H g).nV)→(Fin ((H g).deg v)→Bool)→R),
      (∀ g,16*(H g).nE≤G.nE) ∧ (∑ g,(H g).nE)=2*G.nE ∧
      (∀ g,(H g).maxDeg ≤ max G.maxDeg (2*2^a)) ∧
      (∀ g,(H g).nV=Fintype.card {v : Fin G.nV // grp i v=g}+N) ∧
      ∀ τ : ∀ g,T g,
        (∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
          DeformedContraction.weight (fun v => V v (τ (grp i v))) x y *
            ∏ e,selector G active L U z x y e) =
          ∑ b ∈ legal,(2:R)^(wt b)*∏ g,BTNContract (H g) (child b g (τ g)) := by
  classical
  have layout :
      ∃ (N : ℕ) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
        (tag : Fin N→Fin a→Fin 64×Fin 64) (grp : Fin a→Fin G.nV→Fin 64),
        N*2^a≤3*G.nE ∧ (∀ i,ContractionPortCounts.Compat i (fun q => tag q i) active G L (grp i)) ∧
        (∀ i d g,64*Fintype.card (ContractionPortCounts.sidePorts G (grp i) g d)≤2*G.nE) ∧
        ∀ i g,32*(univ.filter fun x => grp i (host x)=g).card≤b+512*(a+2)*τ := by
    by_cases h : b=0
    · subst b
      have cap : 2*G.maxDeg*(64^a)^4≤G.nE := by
        calc
          _ = 2*((64^a)^4*G.maxDeg) := by ring
          _ ≤ (a+2)*((64^a)^4*G.maxDeg) := Nat.mul_le_mul_right _ (by omega)
          _ ≤ _ := by simpa [Nat.mul_assoc] using hc
      obtain ⟨N,active,L,tag,grp,cap,align,small⟩ := OriginalContractionLayout.layout G 64 a cap hpad
      exact ⟨N,active,L,tag,grp,cap,align,small,by simp⟩
    · let x : Fin b := ⟨0,Nat.pos_of_ne_zero h⟩
      have one : 0 < (univ.filter fun y => host x=host y).card := card_pos.mpr ⟨x,by simp⟩
      exact OriginalContractionLayout.terminal_layout G host τ ht (Nat.mul_pos (Nat.pos_of_ne_zero h) (one.trans_le (ht x))) hm hc hpad
  obtain ⟨N,active,L,tag,grp,cap,align,small,legs⟩ := layout
  refine ⟨N,active,L,tag,grp,cap,legs,?_⟩
  intro i p hp t ht' hi C u hC hu prec
  exact ContractionSampleBounds.sample G active L i _ (grp i) cap (Nat.pos_of_mul_pos_right hm) (align i) (small i) p hp t ht' hi C u hC hu prec
end DetDLP.BoundedContractionStep
end

open DetDLP Finset Polynomial DetDLP.OrientedPacketInstance

theorem solution (G : BipartiteMultigraph) {a b : ℕ} (host : Fin b→Fin G.nV) (τ : ℕ)
    (ht : ∀ x,(univ.filter fun y => host x=host y).card≤τ) (hm : 0<G.nE*G.maxDeg)
    (hc : (a+2)*(64^a)^4*G.maxDeg≤G.nE) (hpad : 2^a*(64^a)^2≤G.nE) :
    ∃ (N : ℕ) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
      (tag : Fin N→Fin a→Fin 64×Fin 64) (grp : Fin a→Fin G.nV→Fin 64),
    N*2^a≤3*G.nE ∧ (∀ i g,32*(univ.filter fun x => grp i (host x)=g).card≤b+512*(a+2)*τ) ∧
    ∀ (i : Fin a) (p : ℕ) (hp : 0<p) (t : ZMod (2^(a+1))) (ht : t≠0) (hi : padicValNat 2 t.val=i.val)
      (C u : ℝ) (hC : 0≤C) (hu : 0<u) (prec : (p:ℝ)≤C*G.nE*(2:ℝ)^(a-i.val)/u),
    let J := Mode i (fun q => tag q i) p
    let beta := ∀ h,J h→Fin p
    let wt (b : beta) := ∑ h,∑ j : J h,(j.2.val+1)*(b h j).val
    let legal := univ.filter (fun b : beta => wt b<p)
    (legal.card:ℝ)≤Real.exp (3*Real.sqrt (6*C)*G.nE/Real.sqrt u) ∧
    ∃ U : ZMod (2^(a+1))→(ZMod (2^p))[X], Represents t U ∧
    ∀ (R : Type) [CommRing R] [Algebra (ZMod (2^p)) R]
      (T : Fin 64→Type) (V : (v : Fin G.nV)→T (grp i v)→(Fin (G.deg v)→Bool)→R) (z : R),
    ∃ (H : Fin 64→BipartiteMultigraph)
      (child : beta→(g : Fin 64)→T g→(v : Fin (H g).nV)→(Fin ((H g).deg v)→Bool)→R),
      (∀ g,16*(H g).nE≤G.nE) ∧ (∑ g,(H g).nE)=2*G.nE ∧
      (∀ g,(H g).maxDeg ≤ max G.maxDeg (2*2^a)) ∧
      (∀ g,(H g).nV=Fintype.card {v : Fin G.nV // grp i v=g}+N) ∧
      ∀ τ : ∀ g,T g,
        (∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
          DeformedContraction.weight (fun v => V v (τ (grp i v))) x y *
            ∏ e,selector G active L U z x y e) =
          ∑ b ∈ legal,(2:R)^(wt b)*∏ g,BTNContract (H g) (child b g (τ g)) := by
  exact BoundedContractionStep.full G host τ ht hm hc hpad
