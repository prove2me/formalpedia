-- Prove2me | solution 1 for BiAbduction.Systematic.lemma_3_18
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T04:15:14.743043+00:00
-- url     : https://prove2.me/submissions/d0df0abd-dadb-4d97-ad66-7f33914b6e1c

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Rules

open BiAbduction.Systematic

noncomputable section

namespace SolBiAbductionLemma318

attribute [local instance] Classical.propDecidable

instance instPrimcodableExpr : Primcodable Expr := inferInstance
instance instPrimcodablePureAtom : Primcodable PureAtom := inferInstance
instance instPrimcodablePtsTo : Primcodable PtsTo := inferInstance
instance instPrimcodableLHS : Primcodable LHS := inferInstance
instance instPrimcodableQF : Primcodable QF := inferInstance
instance instPrimcodableSH : Primcodable SH := inferInstance
instance instPrimcodableDisj : Primcodable Disj := inferInstance
instance instPrimcodableListDisj : Primcodable (List Disj) := inferInstance
instance instPrimcodableListPtsTo : Primcodable (List PtsTo) := inferInstance
instance instPrimcodableListPureAtom : Primcodable (List PureAtom) := inferInstance

def defaultPt : PtsTo := (Sum.inr 0, Sum.inr 0)

def searchBase (pi' : List PureAtom) (tr : Bool) (sig : List PtsTo) : Disj :=
  if tr = true then
    [([], (pi', [], false))]
  else if sig = [] then
    [([], (pi', [], false))]
  else
    []

def searchQF (pi' : List PureAtom) (tr : Bool) : List PtsTo → List PtsTo → Disj
  | [], sig => searchBase pi' tr sig
  | pt :: rest, sig =>
    let recCall := searchQF pi' tr rest
    ((List.finRange sig.length).flatMap (fun j : Fin sig.length =>
        (recCall (sig.eraseIdx j.1)).map
          (addAtoms [(true, (sig.get j).1, pt.1), (true, (sig.get j).2, pt.2)]))) ++
      (recCall sig).map (addPts pt)

def search (Δ : LHS) (H : SH) : Disj :=
  (searchQF H.2.1 H.2.2.2 H.2.2.1 Δ.2).map (bindVars H.1)

theorem searchQF_derives (pi : List PureAtom) (pi' : List PureAtom) (tr : Bool) :
    ∀ (sig' sig : List PtsTo), Derives (pi, sig) (searchQF pi' tr sig' sig) ([], (pi', sig', tr))
  | [], sig => by
    unfold searchQF searchBase
    cases tr
    · by_cases hsig : sig = []
      · subst hsig
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact Derives.emp_ax pi pi'
      · simp only [Bool.false_eq_true, hsig, ↓reduceIte]
        exact Derives.false_ax pi sig pi' hsig
    · simp only [↓reduceIte]
      exact Derives.true_ax pi sig pi'
  | pt :: rest, sig => by
    unfold searchQF
    exact Derives.psto pi sig pi' (pt :: rest) tr ⟨0, Nat.succ_pos rest.length⟩
      (fun j => searchQF pi' tr rest (sig.eraseIdx j.1))
      (searchQF pi' tr rest sig)
      (fun j => searchQF_derives pi pi' tr rest (sig.eraseIdx j.1))
      (searchQF_derives pi pi' tr rest sig)

theorem search_derives (Δ : LHS) (H : SH) : Derives Δ (search Δ H) H := by
  rcases Δ with ⟨pi, sig⟩
  rcases H with ⟨X, pi', sig', tr⟩
  exact Derives.exists_r (pi, sig) (searchQF pi' tr sig' sig) (pi', sig', tr) X
    (searchQF_derives pi pi' tr sig' sig)

private theorem list_eraseIdx_eq {α : Type*} (L : List α) (i : ℕ) :
    L.eraseIdx i = L.take i ++ L.drop (i + 1) := by
  induction L generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ k => simp [ih k]

private theorem primrec₂_eraseIdx {α : Type*} [Primcodable α] :
    Primrec₂ (@List.eraseIdx α) :=
  (Primrec.list_append.comp
    (Primrec.list_take.comp Primrec.snd Primrec.fst)
    (Primrec.list_drop.comp (Primrec.succ.comp Primrec.snd) Primrec.fst)).to₂.of_eq
    (fun L i => (list_eraseIdx_eq L i).symm)

private theorem primrec₂_addAtoms : Primrec₂ addAtoms := by
  unfold Primrec₂ addAtoms
  exact Primrec.pair (Primrec.fst.comp Primrec.snd)
    (Primrec.pair
      (Primrec.list_append.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem primrec₂_addPts : Primrec₂ addPts := by
  unfold Primrec₂ addPts
  exact Primrec.pair (Primrec.fst.comp Primrec.snd)
    (Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.pair
        (Primrec.list_cons.comp Primrec.fst
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

private theorem primrec₂_bindVars : Primrec₂ bindVars := by
  unfold Primrec₂ bindVars
  exact Primrec.pair
    (Primrec.list_append.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

private theorem primrec_searchBase :
    Primrec (fun p : (List PureAtom × Bool) × List PtsTo => searchBase p.1.1 p.1.2 p.2) := by
  unfold searchBase
  have hSingle : Primrec (fun p : (List PureAtom × Bool) × List PtsTo =>
      ([([], (p.1.1, [], false))] : Disj)) :=
    Primrec.list_cons.comp
      (Primrec.pair (Primrec.const ([] : List ℕ))
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.pair (Primrec.const ([] : List PtsTo)) (Primrec.const false))))
      (Primrec.const ([] : Disj))
  have hc1 : PrimrecPred (fun p : (List PureAtom × Bool) × List PtsTo => p.1.2 = true) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const true)
  have hc2 : PrimrecPred (fun p : (List PureAtom × Bool) × List PtsTo => p.2 = []) :=
    Primrec.eq.comp Primrec.snd (Primrec.const ([] : List PtsTo))
  exact Primrec.ite hc1 hSingle (Primrec.ite hc2 hSingle (Primrec.const ([] : Disj)))

def children (_ : List PureAtom × Bool) (b : List PtsTo × List PtsTo) :
    List (List PtsTo × List PtsTo) :=
  if b.1 = [] then
    []
  else
    (b.1.tail, b.2) :: (List.range b.2.length).map (fun i => (b.1.tail, b.2.eraseIdx i))

def eqAtoms (pti pt : PtsTo) : List PureAtom :=
  [(true, pti.1, pt.1), (true, pti.2, pt.2)]

def mapAddEqAtoms (pt pti : PtsTo) (D : Disj) : Disj :=
  D.map (addAtoms (eqAtoms pti pt))

def combineAt (pt : PtsTo) (sig : List PtsTo) (vals : List Disj) (i : ℕ) : Disj :=
  mapAddEqAtoms pt (List.getD sig i defaultPt) (List.getD vals.tail i [])

def combineStep (pt : PtsTo) (sig : List PtsTo) (vals : List Disj) : Disj :=
  ((List.range sig.length).flatMap (combineAt pt sig vals)) ++
    (List.getD vals 0 []).map (addPts pt)

def stepG (a : List PureAtom × Bool) (p : (List PtsTo × List PtsTo) × List Disj) : Option Disj :=
  some (if p.1.1 = [] then
    searchBase a.1 a.2 p.1.2
  else
    combineStep (List.getD p.1.1 0 defaultPt) p.1.2 p.2)

private theorem primrec₂_children : Primrec₂ children := by
  unfold Primrec₂ children
  let P := (List PureAtom × Bool) × (List PtsTo × List PtsTo)
  have hB1 : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hRest : Primrec (fun p : P => p.2.1.tail) := Primrec.list_tail.comp hB1
  have hSig : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hc : PrimrecPred (fun p : P => p.2.1 = []) :=
    Primrec.eq.comp hB1 (Primrec.const ([] : List PtsTo))
  have hMap : Primrec (fun p : P =>
      (List.range p.2.2.length).map (fun i => (p.2.1.tail, p.2.2.eraseIdx i))) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp hSig))
      (Primrec.to₂ (Primrec.pair (hRest.comp Primrec.fst)
        (primrec₂_eraseIdx.comp (hSig.comp Primrec.fst) Primrec.snd)))
  exact Primrec.ite hc (Primrec.const [])
    (Primrec.list_cons.comp (Primrec.pair hRest hSig) hMap)

private theorem primrec₂_eqAtoms : Primrec₂ eqAtoms := by
  unfold Primrec₂ eqAtoms
  have h1 : Primrec (fun p : PtsTo × PtsTo => ((true, p.1.1, p.2.1) : PureAtom)) :=
    Primrec.pair (Primrec.const true)
      (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
  have h2 : Primrec (fun p : PtsTo × PtsTo => ((true, p.1.2, p.2.2) : PureAtom)) :=
    Primrec.pair (Primrec.const true)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_cons.comp h1 (Primrec.list_cons.comp h2 (Primrec.const ([] : List PureAtom)))

private theorem primrec_mapAddEqAtoms :
    Primrec (fun p : (PtsTo × PtsTo) × Disj => mapAddEqAtoms p.1.1 p.1.2 p.2) := by
  unfold mapAddEqAtoms
  have hEq : Primrec (fun p : (PtsTo × PtsTo) × Disj => eqAtoms p.1.2 p.1.1) :=
    primrec₂_eqAtoms.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst)
  exact Primrec.list_map Primrec.snd
    (Primrec.to₂ (primrec₂_addAtoms.comp (hEq.comp Primrec.fst) Primrec.snd))

private theorem primrec₂_combineAt :
    Primrec₂ (fun (q : (PtsTo × List PtsTo) × List Disj) (i : ℕ) => combineAt q.1.1 q.1.2 q.2 i) := by
  unfold Primrec₂ combineAt
  let R := ((PtsTo × List PtsTo) × List Disj) × ℕ
  have hPt : Primrec (fun r : R => r.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hSig : Primrec (fun r : R => r.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hVals : Primrec (fun r : R => r.1.2) := Primrec.snd.comp Primrec.fst
  have hPti : Primrec (fun r : R => List.getD r.1.1.2 r.2 defaultPt) :=
    (Primrec.list_getD defaultPt).comp hSig Primrec.snd
  have hDi : Primrec (fun r : R => List.getD r.1.2.tail r.2 ([] : Disj)) :=
    (Primrec.list_getD ([] : Disj)).comp (Primrec.list_tail.comp hVals) Primrec.snd
  exact primrec_mapAddEqAtoms.comp (Primrec.pair (Primrec.pair hPt hPti) hDi)

private theorem primrec_combineStep :
    Primrec (fun q : (PtsTo × List PtsTo) × List Disj => combineStep q.1.1 q.1.2 q.2) := by
  unfold combineStep
  let Q := (PtsTo × List PtsTo) × List Disj
  have hPt : Primrec (fun q : Q => q.1.1) := Primrec.fst.comp Primrec.fst
  have hSig : Primrec (fun q : Q => q.1.2) := Primrec.snd.comp Primrec.fst
  have hVals : Primrec (fun q : Q => q.2) := Primrec.snd
  have hFlat : Primrec (fun q : Q =>
      (List.range q.1.2.length).flatMap (combineAt q.1.1 q.1.2 q.2)) :=
    Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp hSig)) primrec₂_combineAt
  have hRight : Primrec (fun q : Q => (List.getD q.2 0 []).map (addPts q.1.1)) :=
    Primrec.list_map
      ((Primrec.list_getD ([] : Disj)).comp hVals (Primrec.const 0))
      (Primrec.to₂ (primrec₂_addPts.comp (hPt.comp Primrec.fst) Primrec.snd))
  exact Primrec.list_append.comp hFlat hRight

private abbrev StepGDom := (List PureAtom × Bool) × ((List PtsTo × List PtsTo) × List Disj)

private theorem primrecPred_stepG_nil :
    PrimrecPred (fun p : StepGDom => p.2.1.1 = []) :=
  Primrec.eq.comp
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.const ([] : List PtsTo))

private theorem primrec_stepG_base :
    Primrec (fun p : StepGDom => searchBase p.1.1 p.1.2 p.2.1.2) :=
  primrec_searchBase.comp
    (Primrec.pair Primrec.fst (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))

private theorem primrec_combineStep_q :
    Primrec (fun q : (List PtsTo × List PtsTo) × List Disj =>
      combineStep (List.getD q.1.1 0 defaultPt) q.1.2 q.2) := by
  have hPt0 : Primrec (fun q : (List PtsTo × List PtsTo) × List Disj => List.getD q.1.1 0 defaultPt) :=
    (Primrec.list_getD defaultPt).comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)
  exact primrec_combineStep.comp
    (Primrec.pair (Primrec.pair hPt0 (Primrec.snd.comp Primrec.fst)) Primrec.snd)

private theorem primrec_stepG_comb :
    Primrec (fun p : StepGDom => combineStep (List.getD p.2.1.1 0 defaultPt) p.2.1.2 p.2.2) :=
  primrec_combineStep_q.comp Primrec.snd

private theorem primrec₂_stepG : Primrec₂ stepG :=
  Primrec.option_some.comp
    (Primrec.ite primrecPred_stepG_nil primrec_stepG_base primrec_stepG_comb) |>.of_eq
    (fun _ => rfl)

private theorem map_val_finRange (n : ℕ) :
    (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

private theorem flatMap_range_eq_finRange {α : Type*} (n : ℕ) (f : ℕ → List α) :
    (List.range n).flatMap f = (List.finRange n).flatMap (fun j => f j.1) := by
  rw [← map_val_finRange n, List.flatMap_map]

private theorem primrec₂_searchQF_uncurried :
    Primrec₂ (fun (a : List PureAtom × Bool) (b : List PtsTo × List PtsTo) =>
      searchQF a.1 a.2 b.1 b.2) := by
  refine Primrec.nat_omega_rec
    (fun (a : List PureAtom × Bool) (b : List PtsTo × List PtsTo) => searchQF a.1 a.2 b.1 b.2)
    (m := fun _ b => b.1.length)
    (l := children)
    (g := stepG)
    (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)).to₂
    primrec₂_children
    primrec₂_stepG
    ?_ ?_
  · rintro a ⟨sig', sig⟩ b' hb'
    cases sig' with
    | nil => simp [children] at hb'
    | cons pt rest =>
      simp only [children, List.cons_ne_nil, ↓reduceIte, List.tail_cons,
        List.mem_cons, List.mem_map, List.mem_range] at hb'
      rcases hb' with rfl | ⟨i, _, rfl⟩ <;> simp
  · rintro a ⟨sig', sig⟩
    cases sig' with
    | nil => simp [stepG, searchQF]
    | cons pt rest =>
      simp only [children, stepG, searchQF, List.cons_ne_nil, ↓reduceIte, List.tail_cons,
        List.map_cons, List.map_map, Option.some.injEq]
      unfold combineStep
      rw [flatMap_range_eq_finRange]
      congr 1
      refine List.flatMap_congr (fun j _ => ?_)
      unfold combineAt mapAddEqAtoms eqAtoms
      have hj : j.1 < sig.length := j.isLt
      have hTail :
          List.getD
            (List.map
              ((fun b : List PtsTo × List PtsTo => searchQF a.1 a.2 b.1 b.2) ∘
                fun i => (rest, sig.eraseIdx i))
              (List.range sig.length))
            j.1 [] = searchQF a.1 a.2 rest (sig.eraseIdx j.1) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
        rfl
      have hGet : List.getD sig j.1 defaultPt = sig.get j := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        rfl
      simp only [List.tail_cons, hTail, hGet, List.getD_cons_zero]

private theorem primrec₂_search : Primrec₂ search := by
  unfold Primrec₂ search
  have hA : Primrec (fun p : LHS × SH => (p.2.2.1, p.2.2.2.2)) :=
    Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hB : Primrec (fun p : LHS × SH => (p.2.2.2.1, p.1.2)) :=
    Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.fst)
  have hQF : Primrec (fun p : LHS × SH => searchQF p.2.2.1 p.2.2.2.2 p.2.2.2.1 p.1.2) :=
    primrec₂_searchQF_uncurried.comp hA hB
  exact Primrec.list_map hQF
    (Primrec.to₂ (primrec₂_bindVars.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))

end SolBiAbductionLemma318

open SolBiAbductionLemma318

theorem solution :
    ∃ search : LHS → SH → Disj, Computable₂ search ∧
      ∀ (Δ : LHS) (H : SH), Derives Δ (search Δ H) H :=
  ⟨search, primrec₂_search.to_comp, search_derives⟩
