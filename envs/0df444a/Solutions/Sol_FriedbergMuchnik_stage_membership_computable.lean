-- Prove2me | solution 1 for FriedbergMuchnik.stage_membership_computable
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T21:00:38.577865+00:00
-- url     : https://prove2.me/submissions/5c50d96f-7124-4df9-a2b5-1d26388475c7

import Theorems.Thm_FriedbergMuchnik_finite_oracle_evaln_primrec

set_option autoImplicit false
attribute [local irreducible] Primrec

open Primrec

namespace FriedbergMuchnik

private theorem list_mem_primrec :
    PrimrecRel (fun (l : List ℕ) (n : ℕ) => n ∈ l) :=
  (Primrec.eq.exists_mem_list).of_eq (by simp)

private theorem list_find_primrec {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).find? (p a)) := by
  simpa only [List.find?_eq_getElem?_findIdx] using
    Primrec.list_getElem?.comp hf (Primrec.list_findIdx hf hp)

/-- Compute an indexed map by enumerating the valid list indices. -/
private theorem list_mapIdx_primrec {α β γ : Type}
    [Primcodable α] [Primcodable β] [Primcodable γ] [Inhabited β]
    {l : α → List β} {f : α → ℕ → β → γ} (hl : Primrec l)
    (hf : Primrec (fun p : α × (ℕ × β) => f p.1 p.2.1 p.2.2)) :
    Primrec (fun a => (l a).mapIdx (f a)) := by
  have hm : Primrec (fun a => (List.range (l a).length).map
      (fun k => f a k (((l a)[k]?).getD default))) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp hl))
      (hf.comp (Primrec.fst.pair (Primrec.snd.pair
        (Primrec.option_getD.comp
          (Primrec.list_getElem?.comp (hl.comp Primrec.fst) Primrec.snd)
          (Primrec.const default)))))
  apply hm.of_eq
  intro a
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    simp [hi]

private theorem stateList_primrec : Primrec₂ stateList := by
  unfold stateList
  exact (Primrec.cond Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).of_eq
    (fun p => by cases p.2 <;> rfl)

private theorem side_primrec : Primrec side :=
  Primrec.beq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 1)

/-- Attention is a bounded simulation followed by a waiting-flag and zero test. -/
private theorem wantsAttention_primrec
    (hEval : Primrec (fun p : List ℕ × (ℕ × (Program × ℕ)) =>
      oracleEvaln (fun n => if n ∈ p.1 then 1 else 0) p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : (ℕ × PriorityState) × ℕ => wantsAttention p.1.1 p.1.2 p.2) := by
  have he : Primrec (fun p : (ℕ × PriorityState) × ℕ =>
      (p.1.2.2[p.2]?).getD (0, false)) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd) (Primrec.const (0, false))
  have hsim : Primrec (fun p : (ℕ × PriorityState) × ℕ =>
      oracleEvaln (stateOracle p.1.2 (side p.2)) p.1.1
        (Denumerable.ofNat Program (p.2 / 2))
        ((p.1.2.2[p.2]?).getD (0, false)).1) :=
    hEval.comp ((stateList_primrec.comp (Primrec.snd.comp Primrec.fst)
      (side_primrec.comp Primrec.snd)).pair
      ((Primrec.fst.comp Primrec.fst).pair
        (((Primrec.ofNat Program).comp
          (Primrec.nat_div.comp Primrec.snd (Primrec.const 2))).pair
          (Primrec.fst.comp he))))
  have hz := (Primrec.eq.comp hsim (Primrec.const (some 0))).decide
  have hresult := Primrec.and.comp (Primrec.not.comp (Primrec.snd.comp he)) hz
  apply hresult.of_eq
  intro p
  simp only [wantsAttention, Bool.beq_eq_decide_eq]

private theorem reset_entries_primrec :
    Primrec (fun p : ℕ × (ℕ × List (ℕ × Bool)) => p.2.2.mapIdx
      (fun k entry => if p.2.1 < k then (Nat.pair k (p.1 + 1), false)
        else if k = p.2.1 then (entry.1, true) else entry)) := by
  apply list_mapIdx_primrec (Primrec.snd.comp Primrec.snd)
  exact Primrec.ite
    (Primrec.nat_lt.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd))
    ((Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))).pair (Primrec.const false))
    (Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair (Primrec.const true))
      (Primrec.snd.comp Primrec.snd))

private theorem priorityStep_primrec
    (hEval : Primrec (fun p : List ℕ × (ℕ × (Program × ℕ)) =>
      oracleEvaln (fun n => if n ∈ p.1 then 1 else 0) p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec₂ priorityStep := by
  have hfresh : Primrec (fun p : ℕ × PriorityState => (Nat.pair p.1 (p.1 + 1), false)) :=
    (Primrec₂.natPair.comp Primrec.fst (Primrec.succ.comp Primrec.fst)).pair
      (Primrec.const false)
  have hx : Primrec (fun p : (ℕ × PriorityState) × ℕ =>
      ((p.1.2.2[p.2]?).getD (0, false)).1) :=
    Primrec.fst.comp (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd) (Primrec.const (0, false)))
  have hsets : Primrec (fun p : (ℕ × PriorityState) × ℕ =>
      if side p.2 then
        (((p.1.2.2[p.2]?).getD (0, false)).1 :: p.1.2.1.1, p.1.2.1.2)
      else (p.1.2.1.1, ((p.1.2.2[p.2]?).getD (0, false)).1 :: p.1.2.1.2)) := by
    have ha : Primrec (fun p : (ℕ × PriorityState) × ℕ => p.1.2.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    have hb : Primrec (fun p : (ℕ × PriorityState) × ℕ => p.1.2.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    exact (Primrec.cond (side_primrec.comp Primrec.snd)
      ((Primrec.list_cons.comp hx ha).pair hb)
      (ha.pair (Primrec.list_cons.comp hx hb))).of_eq
      (fun p => by cases side p.2 <;> rfl)
  have hfind : Primrec (fun p : ℕ × PriorityState =>
      (List.range p.1).find? (wantsAttention p.1 p.2)) :=
    list_find_primrec (Primrec.list_range.comp Primrec.fst) (wantsAttention_primrec hEval)
  have hnone := (Primrec.fst.comp Primrec.snd).pair
    (Primrec.list_concat.comp (Primrec.snd.comp Primrec.snd) hfresh)
  have hsome := hsets.pair (Primrec.list_concat.comp
      (reset_entries_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
      (hfresh.comp Primrec.fst))
  have hresult := Primrec.option_casesOn hfind hnone hsome.to₂
  apply hresult.of_eq
  intro p
  unfold priorityStep
  cases (List.range p.1).find? (wantsAttention p.1 p.2) <;> rfl

/-- The whole finite-stage construction is effective once bounded simulation is. -/
theorem stage_membership_of_evaln
    (hEval : Primrec (fun p : List ℕ × (ℕ × (Program × ℕ)) =>
      oracleEvaln (fun n => if n ∈ p.1 then 1 else 0) p.2.1 p.2.2.1 p.2.2.2)) :
    ComputablePred (fun p : ℕ × (Bool × ℕ) => p.2.2 ∈ stageList p.2.1 p.1) := by
  have hstage : Primrec priorityStage :=
    (Primrec.nat_rec₁ (([], []), []) (priorityStep_primrec hEval)).of_eq
      (fun s => by induction s <;> simp [priorityStage, *])
  have hl : Primrec (fun p : ℕ × (Bool × ℕ) => stageList p.2.1 p.1) :=
    stateList_primrec.comp (hstage.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  exact (list_mem_primrec.comp hl (Primrec.snd.comp Primrec.snd)).decide.to_comp.computablePred

end FriedbergMuchnik

theorem solution :
    ComputablePred (fun p : ℕ × (Bool × ℕ) =>
      p.2.2 ∈ FriedbergMuchnik.stageList p.2.1 p.1) :=
  FriedbergMuchnik.stage_membership_of_evaln
    FriedbergMuchnik.finite_oracle_evaln_primrec
