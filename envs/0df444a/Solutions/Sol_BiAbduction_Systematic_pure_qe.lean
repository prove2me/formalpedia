-- Prove2me | solution 1 for BiAbduction.Systematic.pure_qe
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T03:46:13.706556+00:00
-- url     : https://prove2.me/submissions/1e4bd335-fb77-4b95-a79c-c2d4d3fc11ca

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Syntax

open BiAbduction.Systematic

noncomputable section

namespace SolBiAbductionPureQE

attribute [local instance] Classical.propDecidable

def selfNeAtom (X : ℕ) : PureAtom := (false, Sum.inl X, Sum.inl X)

def substE (X : ℕ) (e : Expr) (u : Expr) : Expr :=
  if u = Sum.inl X then e else u

def substAtom (X : ℕ) (e : Expr) (a : PureAtom) : PureAtom :=
  (a.1, substE X e a.2.1, substE X e a.2.2)

def atomEqTarget (X : ℕ) (a : PureAtom) : Option Expr :=
  if a.1 = true ∧ a.2.1 = Sum.inl X ∧ a.2.2 ≠ Sum.inl X then some a.2.2
  else if a.1 = true ∧ a.2.2 = Sum.inl X ∧ a.2.1 ≠ Sum.inl X then some a.2.1
  else none

def findEq (X : ℕ) (pi : List PureAtom) : Option Expr :=
  (pi.filterMap (atomEqTarget X)).head?

def keepAtom (X : ℕ) (a : PureAtom) : Option PureAtom :=
  if a.2.1 = Sum.inl X ∨ a.2.2 = Sum.inl X then none else some a

def qe (X : ℕ) (pi : List PureAtom) : List PureAtom :=
  if selfNeAtom X ∈ pi then
    [(false, Sum.inr 0, Sum.inr 0)]
  else
    Option.casesOn (findEq X pi)
      (pi.filterMap (keepAtom X))
      (fun e => pi.map (substAtom X e))

private theorem primrec_substE :
    Primrec (fun p : (ℕ × Expr) × Expr => substE p.1.1 p.1.2 p.2) := by
  unfold substE
  refine Primrec.ite ?_ (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact Primrec.eq.comp Primrec.snd (Primrec.sumInl.comp (Primrec.fst.comp Primrec.fst))

private theorem primrec₂_substAtom :
    Primrec₂ (fun (p : ℕ × Expr) (a : PureAtom) => substAtom p.1 p.2 a) := by
  unfold Primrec₂ substAtom
  refine Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.pair ?_ ?_)
  · exact primrec_substE.comp (Primrec.pair Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  · exact primrec_substE.comp (Primrec.pair Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem primrec₂_atomEqTarget : Primrec₂ atomEqTarget := by
  unfold Primrec₂ atomEqTarget
  have hX : Primrec (fun p : ℕ × PureAtom => (Sum.inl p.1 : Expr)) :=
    Primrec.sumInl.comp Primrec.fst
  have ha1 : Primrec (fun p : ℕ × PureAtom => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha21 : Primrec (fun p : ℕ × PureAtom => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha22 : Primrec (fun p : ℕ × PureAtom => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hc1 : PrimrecPred (fun p : ℕ × PureAtom =>
      p.2.1 = true ∧ p.2.2.1 = Sum.inl p.1 ∧ p.2.2.2 ≠ Sum.inl p.1) :=
    (Primrec.eq.comp ha1 (Primrec.const true)).and
      ((Primrec.eq.comp ha21 hX).and (Primrec.eq.comp ha22 hX).not)
  have hc2 : PrimrecPred (fun p : ℕ × PureAtom =>
      p.2.1 = true ∧ p.2.2.2 = Sum.inl p.1 ∧ p.2.2.1 ≠ Sum.inl p.1) :=
    (Primrec.eq.comp ha1 (Primrec.const true)).and
      ((Primrec.eq.comp ha22 hX).and (Primrec.eq.comp ha21 hX).not)
  exact Primrec.ite hc1 (Primrec.option_some.comp ha22)
    (Primrec.ite hc2 (Primrec.option_some.comp ha21) (Primrec.const none))

private theorem primrec₂_findEq : Primrec₂ findEq := by
  unfold Primrec₂ findEq
  exact Primrec.list_head?.comp
    (Primrec.listFilterMap Primrec.snd
      (Primrec.to₂ (primrec₂_atomEqTarget.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)))

private theorem primrec₂_keepAtom : Primrec₂ keepAtom := by
  unfold Primrec₂ keepAtom
  have hX : Primrec (fun p : ℕ × PureAtom => (Sum.inl p.1 : Expr)) :=
    Primrec.sumInl.comp Primrec.fst
  have ha21 : Primrec (fun p : ℕ × PureAtom => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha22 : Primrec (fun p : ℕ × PureAtom => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hc : PrimrecPred (fun p : ℕ × PureAtom => p.2.2.1 = Sum.inl p.1 ∨ p.2.2.2 = Sum.inl p.1) :=
    (Primrec.eq.comp ha21 hX).or (Primrec.eq.comp ha22 hX)
  exact Primrec.ite hc (Primrec.const none) (Primrec.option_some.comp Primrec.snd)

private theorem primrec₂_qe : Primrec₂ qe := by
  unfold Primrec₂ qe
  have hSelfAtom : Primrec (fun p : ℕ × List PureAtom => selfNeAtom p.1) :=
    Primrec.pair (Primrec.const false)
      (Primrec.pair (Primrec.sumInl.comp Primrec.fst) (Primrec.sumInl.comp Primrec.fst))
  have hMem : PrimrecPred (fun p : ℕ × List PureAtom => selfNeAtom p.1 ∈ p.2) := by
    have hRel : PrimrecRel (fun (L : List PureAtom) (b : PureAtom) => b ∈ L) :=
      (PrimrecRel.exists_mem_list Primrec.eq).of_eq (fun L b => by simp)
    exact hRel.comp Primrec.snd hSelfAtom
  have hFilter : Primrec (fun p : ℕ × List PureAtom => p.2.filterMap (keepAtom p.1)) :=
    Primrec.listFilterMap Primrec.snd
      (Primrec.to₂ (primrec₂_keepAtom.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
  have hMap : Primrec₂ (fun (p : ℕ × List PureAtom) (e : Expr) => p.2.map (substAtom p.1 e)) := by
    unfold Primrec₂
    exact Primrec.list_map (Primrec.snd.comp Primrec.fst)
      (Primrec.to₂
        (primrec₂_substAtom.comp
          (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))
          Primrec.snd))
  exact Primrec.ite hMem
    (Primrec.const [(false, Sum.inr 0, Sum.inr 0)])
    (Primrec.option_casesOn primrec₂_findEq hFilter hMap)

private theorem mem_exprVars_iff (X : ℕ) (e : Expr) : X ∈ exprVars e ↔ e = Sum.inl X := by
  cases e <;> simp [exprVars, eq_comm]

private theorem mem_pureVars_iff (X : ℕ) (pi : List PureAtom) :
    X ∈ pureVars pi ↔ ∃ a ∈ pi, a.2.1 = Sum.inl X ∨ a.2.2 = Sum.inl X := by
  simp [pureVars, mem_exprVars_iff]

private theorem substE_ne_self (X : ℕ) {e : Expr} (he : e ≠ Sum.inl X) (u : Expr) :
    substE X e u ≠ Sum.inl X := by
  unfold substE
  split_ifs with h
  · exact he
  · exact h

private theorem evalE_update_self (s : Stack) (X : ℕ) (v : ℕ) :
    evalE (Function.update s X v) (Sum.inl X) = v := by
  simp [evalE]

private theorem evalE_update_of_ne (s : Stack) (X : ℕ) (v : ℕ) {u : Expr} (hu : u ≠ Sum.inl X) :
    evalE (Function.update s X v) u = evalE s u := by
  cases u with
  | inl y =>
    have hy : y ≠ X := fun h => hu (by rw [h])
    simp [evalE, Function.update_of_ne hy]
  | inr k => rfl

private theorem evalE_substE (s : Stack) (X : ℕ) (e u : Expr) :
    evalE s (substE X e u) = evalE (Function.update s X (evalE s e)) u := by
  unfold substE
  split_ifs with h
  · subst h
    simp [evalE]
  · exact (evalE_update_of_ne s X (evalE s e) h).symm

private theorem atomHolds_substAtom (s : Stack) (X : ℕ) (e : Expr) (a : PureAtom) :
    atomHolds s (substAtom X e a) ↔ atomHolds (Function.update s X (evalE s e)) a := by
  rcases a with ⟨b, u1, u2⟩
  simp [substAtom, atomHolds, evalE_substE]

private theorem atomEqTarget_some_iff (X : ℕ) (a : PureAtom) (e : Expr) :
    atomEqTarget X a = some e ↔
      a.1 = true ∧ e ≠ Sum.inl X ∧
        ((a.2.1 = Sum.inl X ∧ a.2.2 = e) ∨ (a.2.2 = Sum.inl X ∧ a.2.1 = e)) := by
  unfold atomEqTarget
  split_ifs with h1 h2
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨h1.1, h1.2.2, Or.inl ⟨h1.2.1, rfl⟩⟩
    · rintro ⟨_, _, ⟨_, rfl⟩ | ⟨h22, _⟩⟩
      · rfl
      · exact absurd h22 h1.2.2
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨h2.1, h2.2.2, Or.inr ⟨h2.2.1, rfl⟩⟩
    · rintro ⟨ha1, he, ⟨h21, rfl⟩ | ⟨_, rfl⟩⟩
      · exact absurd ⟨ha1, h21, he⟩ h1
      · rfl
  · simp only [false_iff]
    rintro ⟨ha1, he, ⟨h21, rfl⟩ | ⟨h22, rfl⟩⟩
    · exact h1 ⟨ha1, h21, he⟩
    · exact h2 ⟨ha1, h22, he⟩

private theorem atomEqTarget_eq_none_of_true (X : ℕ) (a : PureAtom)
    (hnone : atomEqTarget X a = none) (ha1 : a.1 = true)
    (hX : a.2.1 = Sum.inl X ∨ a.2.2 = Sum.inl X) :
    a.2.1 = Sum.inl X ∧ a.2.2 = Sum.inl X := by
  unfold atomEqTarget at hnone
  split_ifs at hnone with h1 h2
  rcases hX with h21 | h22
  · refine ⟨h21, ?_⟩
    by_contra hne
    exact h1 ⟨ha1, h21, hne⟩
  · refine ⟨?_, h22⟩
    by_contra hne
    exact h2 ⟨ha1, h22, hne⟩

private theorem keepAtom_some_iff (X : ℕ) (a b : PureAtom) :
    keepAtom X a = some b ↔ a = b ∧ b.2.1 ≠ Sum.inl X ∧ b.2.2 ≠ Sum.inl X := by
  unfold keepAtom
  split_ifs with h
  · simp only [false_iff]
    rintro ⟨rfl, h1, h2⟩
    exact h.elim h1 h2
  · rw [not_or] at h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨rfl, h.1, h.2⟩
    · rintro ⟨rfl, _⟩
      rfl

private theorem le_foldr_max_eval (s : Stack) (pi : List PureAtom) (a : PureAtom) (ha : a ∈ pi) :
    evalE s a.2.1 ≤ pi.foldr (fun x m => max m (max (evalE s x.2.1) (evalE s x.2.2))) 0 ∧
    evalE s a.2.2 ≤ pi.foldr (fun x m => max m (max (evalE s x.2.1) (evalE s x.2.2))) 0 := by
  induction pi with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact ⟨le_trans (le_max_left _ _) (le_max_right _ _),
             le_trans (le_max_right _ _) (le_max_right _ _)⟩
    · obtain ⟨ih1, ih2⟩ := ih hmem
      exact ⟨le_trans ih1 (le_max_left _ _), le_trans ih2 (le_max_left _ _)⟩

theorem qe_spec (X : ℕ) (pi : List PureAtom) :
    X ∉ pureVars (qe X pi) ∧ exQ X (pureDen pi) = pureDen (qe X pi) := by
  unfold qe
  by_cases hSelf : selfNeAtom X ∈ pi
  · simp only [hSelf, ↓reduceIte]
    refine ⟨by simp [pureVars, exprVars], ?_⟩
    ext ⟨s, h⟩
    simp only [exQ, pureDen, Set.mem_setOf_eq, List.mem_singleton]
    constructor
    · rintro ⟨v, hv⟩
      have hfalse := hv (selfNeAtom X) hSelf
      simp [selfNeAtom, atomHolds] at hfalse
    · intro hfalse
      have := hfalse (false, Sum.inr 0, Sum.inr 0) rfl
      simp [atomHolds, evalE] at this
  · simp only [hSelf, ↓reduceIte]
    cases hFind : findEq X pi with
    | none =>
      simp only
      have hNoEq : ∀ a ∈ pi, atomEqTarget X a = none := by
        unfold findEq at hFind
        exact List.filterMap_eq_nil_iff.mp (List.head?_eq_none_iff.mp hFind)
      refine ⟨?_, ?_⟩
      · rw [mem_pureVars_iff]
        rintro ⟨b, hb, hbX⟩
        obtain ⟨a, _, hab⟩ := List.mem_filterMap.mp hb
        obtain ⟨rfl, h1, h2⟩ := (keepAtom_some_iff X a b).mp hab
        exact hbX.elim h1 h2
      · ext ⟨s, h⟩
        simp only [exQ, pureDen, Set.mem_setOf_eq, List.mem_filterMap]
        constructor
        · rintro ⟨v, hv⟩ b ⟨a, ha, hab⟩
          obtain ⟨rfl, h1, h2⟩ := (keepAtom_some_iff X a b).mp hab
          have hhold := hv a ha
          simp only [atomHolds, evalE_update_of_ne s X v h1, evalE_update_of_ne s X v h2] at hhold
          exact hhold
        · intro hfilt
          let v := (pi.foldr (fun x m => max m (max (evalE s x.2.1) (evalE s x.2.2))) 0) + 1
          refine ⟨v, fun a ha => ?_⟩
          by_cases hmen : a.2.1 = Sum.inl X ∨ a.2.2 = Sum.inl X
          · cases ha1 : a.1 with
            | true =>
              have hboth := atomEqTarget_eq_none_of_true X a (hNoEq a ha) ha1 hmen
              simp [atomHolds, ha1, hboth.1, hboth.2]
            | false =>
              have ⟨hle1, hle2⟩ := le_foldr_max_eval s pi a ha
              rcases hmen with h21 | h22
              · have h22 : a.2.2 ≠ Sum.inl X := by
                  intro hc
                  apply hSelf
                  rcases a with ⟨b, u1, u2⟩
                  simp only at ha1 h21 hc
                  subst ha1 h21 hc
                  exact ha
                simp only [atomHolds, ha1, Bool.false_eq_true, ↓reduceIte, h21,
                  evalE_update_self, evalE_update_of_ne s X v h22]
                exact Nat.ne_of_gt (Nat.lt_succ_of_le hle2)
              · have h21 : a.2.1 ≠ Sum.inl X := by
                  intro hc
                  apply hSelf
                  rcases a with ⟨b, u1, u2⟩
                  simp only at ha1 h22 hc
                  subst ha1 h22 hc
                  exact ha
                simp only [atomHolds, ha1, Bool.false_eq_true, ↓reduceIte, h22,
                  evalE_update_self, evalE_update_of_ne s X v h21]
                exact Nat.ne_of_lt (Nat.lt_succ_of_le hle1)
          · rw [not_or] at hmen
            have hhold := hfilt a ⟨a, ha, (keepAtom_some_iff X a a).mpr ⟨rfl, hmen.1, hmen.2⟩⟩
            simpa only [atomHolds, evalE_update_of_ne s X v hmen.1,
              evalE_update_of_ne s X v hmen.2] using hhold
    | some e =>
      simp only
      have hMemFind : e ∈ pi.filterMap (atomEqTarget X) :=
        List.mem_of_mem_head? hFind
      obtain ⟨a₀, ha₀, hTarget⟩ := List.mem_filterMap.mp hMemFind
      obtain ⟨ha₀1, heNe, ha₀Eq⟩ := (atomEqTarget_some_iff X a₀ e).mp hTarget
      refine ⟨?_, ?_⟩
      · rw [mem_pureVars_iff]
        rintro ⟨b, hb, hbX⟩
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
        rcases hbX with h1 | h2
        · exact substE_ne_self X heNe a.2.1 h1
        · exact substE_ne_self X heNe a.2.2 h2
      · ext ⟨s, h⟩
        simp only [exQ, pureDen, Set.mem_setOf_eq, List.mem_map]
        constructor
        · rintro ⟨v, hv⟩ b ⟨a, ha, rfl⟩
          have hv_eq : v = evalE s e := by
            have h0 := hv a₀ ha₀
            rcases ha₀Eq with ⟨h21, h22⟩ | ⟨h22, h21⟩
            · simp only [atomHolds, ha₀1, ↓reduceIte, h21, h22,
                evalE_update_self, evalE_update_of_ne s X v heNe] at h0
              exact h0
            · simp only [atomHolds, ha₀1, ↓reduceIte, h21, h22,
                evalE_update_self, evalE_update_of_ne s X v heNe] at h0
              exact h0.symm
          rw [atomHolds_substAtom, ← hv_eq]
          exact hv a ha
        · intro hmap
          refine ⟨evalE s e, fun a ha => ?_⟩
          rw [← atomHolds_substAtom]
          exact hmap (substAtom X e a) ⟨a, ha, rfl⟩

end SolBiAbductionPureQE

open SolBiAbductionPureQE

theorem solution :
    ∃ qe : ℕ → List PureAtom → List PureAtom, Computable₂ qe ∧
      ∀ (X : ℕ) (pi : List PureAtom),
        X ∉ pureVars (qe X pi) ∧ exQ X (pureDen pi) = pureDen (qe X pi) :=
  ⟨qe, primrec₂_qe.to_comp, qe_spec⟩
