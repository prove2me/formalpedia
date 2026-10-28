-- Prove2me | solution 1 for BiAbduction.Systematic.theorem_3_25
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T04:27:13.587986+00:00
-- url     : https://prove2.me/submissions/3adf47c4-00b9-46af-a5c4-441e17925e64

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Syntax
import Definitions.Def_BiAbduction_Systematic_Rules
import Definitions.Def_BiAbduction_Systematic_Incompat
import Theorems.Thm_BiAbduction_Systematic_lemma_3_16
import Theorems.Thm_BiAbduction_Systematic_derives_sound
import Theorems.Thm_BiAbduction_Systematic_lemma_3_18
import Theorems.Thm_BiAbduction_Systematic_lemma_3_19
import Theorems.Thm_BiAbduction_Systematic_lemma_3_20
import Theorems.Thm_BiAbduction_Systematic_lemma_3_23
import Theorems.Thm_BiAbduction_Systematic_pure_qe
import Theorems.Thm_BiAbduction_Systematic_sub_quantified

open BiAbduction.Systematic

set_option linter.deprecated false

namespace SolBiAbductionTheorem325

/-! ## Computability combinators for `List` -/

private theorem comp_nat_iterate {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f : α → ℕ} {g : α → σ} {h : α → σ → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable fun p : α × σ => h p.1 p.2) :
    Computable fun a => (h a)^[f a] (g a) :=
  (Computable.nat_rec hf hg
    (Computable.to₂ (hh.comp (Computable.pair Computable.fst (Computable.snd.comp Computable.snd))))).of_eq
    fun a => by
      induction f a with
      | zero => rfl
      | succ n ih => simp only [Function.iterate_succ_apply', ← ih]

private theorem comp_list_foldl {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g)
    (hh : Computable fun p : α × (σ × β) => h p.1 p.2) :
    Computable fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  let G (a : α) (IH : σ × List β) : σ × List β :=
    Option.casesOn IH.2.head? IH (fun b => (h a (IH.1, b), IH.2.tail))
  have hG : Computable fun p : α × (σ × List β) => G p.1 p.2 := by
    refine Computable.option_casesOn
      (Primrec.list_head?.to_comp.comp (Computable.snd.comp Computable.snd))
      Computable.snd ?_
    show Computable fun p : (α × (σ × List β)) × β =>
      (h p.1.1 (p.1.2.1, p.2), p.1.2.2.tail)
    exact Computable.pair
      (hh.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst)) Computable.snd)))
      (Primrec.list_tail.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hF : Computable fun a => ((G a)^[(f a).length] (g a, f a)).1 :=
    Computable.fst.comp
      (comp_nat_iterate (Computable.list_length.comp hf) (Computable.pair hg hf) hG)
  refine hF.of_eq fun a => ?_
  suffices ∀ l : List β, ∀ s : σ,
      (G a)^[l.length] (s, l) = (l.foldl (fun s b => h a (s, b)) s, []) by
    rw [this]
  intro l
  induction l with
  | nil => intro s; rfl
  | cons b l ih =>
    intro s
    simp only [List.length_cons, Function.iterate_succ_apply, G, List.head?_cons,
       List.tail_cons, List.foldl_cons]
    exact ih (h a (s, b))

private theorem comp_list_foldr {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → σ} {h : α → β × σ → σ}
    (hf : Computable f) (hg : Computable g)
    (hh : Computable fun p : α × (β × σ) => h p.1 p.2) :
    Computable fun a => (f a).foldr (fun b s => h a (b, s)) (g a) :=
  (comp_list_foldl (f := fun a => (f a).reverse) (g := g)
    (h := fun a p => h a (p.2, p.1))
    (Computable.list_reverse.comp hf) hg
    (hh.comp (Computable.pair Computable.fst
      (Computable.pair (Computable.snd.comp Computable.snd)
        (Computable.fst.comp Computable.snd))))).of_eq
    fun a => by simp [List.foldl_reverse]

private theorem comp_list_map {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → β → σ}
    (hf : Computable f) (hg : Computable fun p : α × β => g p.1 p.2) :
    Computable fun a => (f a).map (g a) :=
  (comp_list_foldr (f := f) (g := fun _ => []) (h := fun a p => g a p.1 :: p.2)
    hf (Computable.const [])
    (Computable.list_cons.comp
      (hg.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd))).of_eq
    fun a => by induction f a <;> simp [*]

private theorem comp_list_flatMap {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → β → List σ}
    (hf : Computable f) (hg : Computable fun p : α × β => g p.1 p.2) :
    Computable fun a => (f a).flatMap (g a) :=
  Primrec.list_flatten.to_comp.comp (comp_list_map (f := f) (g := g) hf hg)

/-! ## Syntactic transformations and their primitivity -/

def qVars (q : QF) : List ℕ := pureVars q.1 ++ ptsVars q.2.1

def shVars (H : SH) : List ℕ := H.1 ++ qVars H.2

def shiftVar (X : List ℕ) (base x : ℕ) : ℕ :=
  if x ∈ X then x + base else x

def shiftExpr (X : List ℕ) (base : ℕ) : Expr → Expr
  | Sum.inl x => Sum.inl (shiftVar X base x)
  | Sum.inr k => Sum.inr k

def shiftAtom (X : List ℕ) (base : ℕ) (a : PureAtom) : PureAtom :=
  (a.1, shiftExpr X base a.2.1, shiftExpr X base a.2.2)

def shiftPts (X : List ℕ) (base : ℕ) (pt : PtsTo) : PtsTo :=
  (shiftExpr X base pt.1, shiftExpr X base pt.2)

def shiftQF (X : List ℕ) (base : ℕ) (q : QF) : QF :=
  (q.1.map (shiftAtom X base), q.2.1.map (shiftPts X base), q.2.2)

def shiftSH (base : ℕ) (H : SH) : SH :=
  (H.1.map (· + base), shiftQF H.1 base H.2)

def extendInjMaps (n : ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
  acc.flatMap (fun l =>
    (List.range n).flatMap (fun j => if j ∈ l then [] else [j :: l]))

def injMaps (n m : ℕ) : List (List ℕ) :=
  (extendInjMaps n)^[m] [[]]

def activeMaps (sig' sig : List PtsTo) : List (List ℕ) :=
  if sig'.length < sig.length then injMaps sig.length sig'.length else []

def defaultPts : PtsTo := (Sum.inr 0, Sum.inr 0)

def matchAtomsOne (sig' sig : List PtsTo) (l : List ℕ) (k : ℕ) : List PureAtom :=
  let pt' := sig'.getD k defaultPts
  let pt := sig.getD (l.getD k 0) defaultPts
  [(true, pt'.1, pt.1), (true, pt'.2, pt.2)]

def matchAtoms (sig' sig : List PtsTo) (l : List ℕ) : List PureAtom :=
  (List.range sig'.length).flatMap (matchAtomsOne sig' sig l)

def negChoicesStep (as : List PureAtom) (acc : List (List PureAtom)) : List (List PureAtom) :=
  as.flatMap (fun a => acc.map (fun c => negAtom a :: c))

def negChoices (L : List (List PureAtom)) : List (List PureAtom) :=
  L.foldr negChoicesStep [[]]

def listMax (l : List ℕ) : ℕ :=
  l.foldr max 0

def base₁ (H H' : SH) : ℕ :=
  listMax (shVars H ++ shVars H') + 1

def base₂ (H H' : SH) : ℕ :=
  2 * base₁ H H'

def elimList (qe : ℕ → List PureAtom → List PureAtom) (Y : List ℕ) (pi : List PureAtom) :
    List PureAtom :=
  Y.foldr qe pi

def mkSubDisj (H₁ : SH) (L : List (List PureAtom)) : Disj :=
  (negChoices L).map (fun extra => (H₁.1, (extra ++ H₁.2.1, H₁.2.2.1, false)))

def subSHCore (qe : ℕ → List PureAtom → List PureAtom) (H₁ H'₁ : SH) : Disj :=
  let L := (activeMaps H'₁.2.2.1 H₁.2.2.1).map (fun l =>
    elimList qe H'₁.1 (H'₁.2.1 ++ matchAtoms H'₁.2.2.1 H₁.2.2.1 l))
  mkSubDisj H₁ L

def subSH (qe : ℕ → List PureAtom → List PureAtom) (H H' : SH) : Disj :=
  subSHCore qe (shiftSH (base₁ H H') H) (shiftSH (base₂ H H') H')

def stripTrue (K : SH) : SH :=
  (K.1, (K.2.1, K.2.2.1, false))

def subDisjBySH (qe : ℕ → List PureAtom → List PureAtom) (acc : Disj) (H' : SH) : Disj :=
  acc.flatMap (fun K => subSH qe K H')

def subSHByList (qe : ℕ → List PureAtom → List PureAtom) (K : SH) (D₁ : Disj) : Disj :=
  D₁.foldl (subDisjBySH qe) [K]

def minDisj (qe : ℕ → List PureAtom → List PureAtom) (D₁ : Disj) : Disj :=
  D₁.flatMap (fun K => subSHByList qe K D₁)

def convBase (Δ : LHS) (H : SH) : ℕ :=
  listMax (lhsVars Δ ++ shVars H) + 1

def solveAbduction (qe : ℕ → List PureAtom → List PureAtom) (search : LHS → SH → Disj)
    (Δ : LHS) (H : SH) : Disj :=
  let H₀ := shiftSH (convBase Δ H) H
  let D₀ := search Δ H₀
  let D₁ := (D₀ ++ incompat Δ).map stripTrue
  minDisj qe D₁

private theorem primrec_exprVars : Primrec exprVars := by
  refine (Primrec.sumCasesOn Primrec.id
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to₂
    (Primrec.const []).to₂).of_eq ?_
  intro e
  cases e <;> rfl

private theorem primrec_pureVars : Primrec pureVars := by
  unfold pureVars
  refine Primrec.list_flatMap Primrec.id ?_
  show Primrec fun p : List PureAtom × PureAtom => exprVars p.2.2.1 ++ exprVars p.2.2.2
  exact Primrec.list_append.comp
    (primrec_exprVars.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    (primrec_exprVars.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem primrec_ptsVars : Primrec ptsVars := by
  unfold ptsVars
  refine Primrec.list_flatMap Primrec.id ?_
  show Primrec fun p : List PtsTo × PtsTo => exprVars p.2.1 ++ exprVars p.2.2
  exact Primrec.list_append.comp
    (primrec_exprVars.comp (Primrec.fst.comp Primrec.snd))
    (primrec_exprVars.comp (Primrec.snd.comp Primrec.snd))

private theorem primrec_lhsVars : Primrec lhsVars :=
  Primrec.list_append.comp
    (primrec_pureVars.comp Primrec.fst)
    (primrec_ptsVars.comp Primrec.snd)

private theorem primrec_qVars : Primrec qVars :=
  Primrec.list_append.comp
    (primrec_pureVars.comp Primrec.fst)
    (primrec_ptsVars.comp (Primrec.fst.comp Primrec.snd))

private theorem primrec_shVars : Primrec shVars :=
  Primrec.list_append.comp Primrec.fst (primrec_qVars.comp Primrec.snd)

private theorem primrec_mem_nat : PrimrecRel ((· ∈ ·) : ℕ → List ℕ → Prop) := by
  have h : PrimrecRel (fun (l : List ℕ) (x : ℕ) => ∃ a ∈ l, a = x) :=
    PrimrecRel.exists_mem_list Primrec.eq
  exact (h.comp Primrec.snd Primrec.fst).of_eq (fun ⟨x, l⟩ => by simp)

private theorem primrec_shiftVar : Primrec fun p : List ℕ × ℕ × ℕ => shiftVar p.1 p.2.1 p.2.2 := by
  unfold shiftVar
  exact Primrec.ite
    (primrec_mem_nat.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

private theorem primrec_shiftExpr :
    Primrec fun p : List ℕ × ℕ × Expr => shiftExpr p.1 p.2.1 p.2.2 := by
  refine (Primrec.sumCasesOn (Primrec.snd.comp Primrec.snd)
    (Primrec.sumInl.comp (primrec_shiftVar.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)))).to₂
    (Primrec.sumInr.comp Primrec.snd).to₂).of_eq ?_
  rintro ⟨X, base, x | k⟩ <;> rfl

private theorem primrec_shiftAtom :
    Primrec fun p : List ℕ × ℕ × PureAtom => shiftAtom p.1 p.2.1 p.2.2 := by
  unfold shiftAtom
  have h1 : Primrec fun p : List ℕ × ℕ × PureAtom => shiftExpr p.1 p.2.1 p.2.2.2.1 :=
    primrec_shiftExpr.comp (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have h2 : Primrec fun p : List ℕ × ℕ × PureAtom => shiftExpr p.1 p.2.1 p.2.2.2.2 :=
    primrec_shiftExpr.comp (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.pair h1 h2)

private theorem primrec_shiftPts :
    Primrec fun p : List ℕ × ℕ × PtsTo => shiftPts p.1 p.2.1 p.2.2 := by
  unfold shiftPts
  have h1 : Primrec fun p : List ℕ × ℕ × PtsTo => shiftExpr p.1 p.2.1 p.2.2.1 :=
    primrec_shiftExpr.comp (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have h2 : Primrec fun p : List ℕ × ℕ × PtsTo => shiftExpr p.1 p.2.1 p.2.2.2 :=
    primrec_shiftExpr.comp (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact Primrec.pair h1 h2

private theorem primrec_shiftQF :
    Primrec fun p : List ℕ × ℕ × QF => shiftQF p.1 p.2.1 p.2.2 := by
  unfold shiftQF
  have h1 : Primrec fun p : List ℕ × ℕ × QF => p.2.2.1.map (shiftAtom p.1 p.2.1) := by
    refine Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) ?_
    show Primrec fun q : (List ℕ × ℕ × QF) × PureAtom => shiftAtom q.1.1 q.1.2.1 q.2
    exact primrec_shiftAtom.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  have h2 : Primrec fun p : List ℕ × ℕ × QF => p.2.2.2.1.map (shiftPts p.1 p.2.1) := by
    refine Primrec.list_map
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) ?_
    show Primrec fun q : (List ℕ × ℕ × QF) × PtsTo => shiftPts q.1.1 q.1.2.1 q.2
    exact primrec_shiftPts.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  have h3 : Primrec fun p : List ℕ × ℕ × QF => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.pair h1 (Primrec.pair h2 h3)

private theorem primrec_shiftSH : Primrec₂ shiftSH := by
  show Primrec fun p : ℕ × SH => shiftSH p.1 p.2
  unfold shiftSH
  have h1 : Primrec fun p : ℕ × SH => p.2.1.map (· + p.1) := by
    refine Primrec.list_map (Primrec.fst.comp Primrec.snd) ?_
    show Primrec fun q : (ℕ × SH) × ℕ => q.2 + q.1.1
    exact Primrec.nat_add.comp Primrec.snd (Primrec.fst.comp Primrec.fst)
  have h2 : Primrec fun p : ℕ × SH => shiftQF p.2.1 p.1 p.2.2 :=
    primrec_shiftQF.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)))
  exact Primrec.pair h1 h2

private theorem primrec_extendInjMaps : Primrec₂ extendInjMaps := by
  show Primrec fun p : ℕ × List (List ℕ) => extendInjMaps p.1 p.2
  unfold extendInjMaps
  refine Primrec.list_flatMap Primrec.snd ?_
  show Primrec fun q : (ℕ × List (List ℕ)) × List ℕ =>
    (List.range q.1.1).flatMap (fun j => if j ∈ q.2 then [] else [j :: q.2])
  refine Primrec.list_flatMap (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)) ?_
  show Primrec fun r : ((ℕ × List (List ℕ)) × List ℕ) × ℕ =>
    if r.2 ∈ r.1.2 then ([] : List (List ℕ)) else [r.2 :: r.1.2]
  exact Primrec.ite
    (primrec_mem_nat.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
    (Primrec.const [])
    (Primrec.list_cons.comp
      (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (Primrec.const []))

private theorem primrec_injMaps : Primrec₂ injMaps := by
  show Primrec fun p : ℕ × ℕ => injMaps p.1 p.2
  unfold injMaps
  exact Primrec.nat_iterate Primrec.snd (Primrec.const [[]])
    (primrec_extendInjMaps.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

private theorem primrec_activeMaps : Primrec₂ activeMaps := by
  show Primrec fun p : List PtsTo × List PtsTo => activeMaps p.1 p.2
  unfold activeMaps
  exact Primrec.ite
    (Primrec.nat_lt.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd))
    (primrec_injMaps.comp (Primrec.list_length.comp Primrec.snd) (Primrec.list_length.comp Primrec.fst))
    (Primrec.const [])

private theorem primrec_matchAtomsOne :
    Primrec fun q : (List PtsTo × List PtsTo × List ℕ) × ℕ =>
      matchAtomsOne q.1.1 q.1.2.1 q.1.2.2 q.2 := by
  unfold matchAtomsOne
  have hpt' : Primrec fun q : (List PtsTo × List PtsTo × List ℕ) × ℕ =>
      q.1.1.getD q.2 defaultPts :=
    (Primrec.list_getD defaultPts).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hidx : Primrec fun q : (List PtsTo × List PtsTo × List ℕ) × ℕ =>
      q.1.2.2.getD q.2 0 :=
    (Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hpt : Primrec fun q : (List PtsTo × List PtsTo × List ℕ) × ℕ =>
      q.1.2.1.getD (q.1.2.2.getD q.2 0) defaultPts :=
    (Primrec.list_getD defaultPts).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hidx
  have ha1 : Primrec fun q : (List PtsTo × List PtsTo × List ℕ) × ℕ =>
      (true, (q.1.1.getD q.2 defaultPts).1, (q.1.2.1.getD (q.1.2.2.getD q.2 0) defaultPts).1) :=
    Primrec.pair (Primrec.const true)
      (Primrec.pair (Primrec.fst.comp hpt') (Primrec.fst.comp hpt))
  have ha2 : Primrec fun q : (List PtsTo × List PtsTo × List ℕ) × ℕ =>
      (true, (q.1.1.getD q.2 defaultPts).2, (q.1.2.1.getD (q.1.2.2.getD q.2 0) defaultPts).2) :=
    Primrec.pair (Primrec.const true)
      (Primrec.pair (Primrec.snd.comp hpt') (Primrec.snd.comp hpt))
  exact Primrec.list_cons.comp ha1 (Primrec.list_cons.comp ha2 (Primrec.const []))

private theorem primrec_matchAtoms :
    Primrec fun p : List PtsTo × List PtsTo × List ℕ => matchAtoms p.1 p.2.1 p.2.2 := by
  unfold matchAtoms
  exact Primrec.list_flatMap
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
    primrec_matchAtomsOne

private theorem primrec_negAtom : Primrec negAtom :=
  Primrec.pair (Primrec.not.comp Primrec.fst) Primrec.snd

private theorem primrec_negChoicesStep : Primrec₂ negChoicesStep := by
  show Primrec fun p : List PureAtom × List (List PureAtom) => negChoicesStep p.1 p.2
  unfold negChoicesStep
  refine Primrec.list_flatMap Primrec.fst ?_
  show Primrec fun q : (List PureAtom × List (List PureAtom)) × PureAtom =>
    q.1.2.map (fun c => negAtom q.2 :: c)
  refine Primrec.list_map (Primrec.snd.comp Primrec.fst) ?_
  show Primrec fun r : ((List PureAtom × List (List PureAtom)) × PureAtom) × List PureAtom =>
    negAtom r.1.2 :: r.2
  exact Primrec.list_cons.comp (primrec_negAtom.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd

private theorem primrec_negChoices : Primrec negChoices := by
  unfold negChoices
  have hstep : Primrec₂ fun (_ : List (List PureAtom)) (p : List PureAtom × List (List PureAtom)) =>
      negChoicesStep p.1 p.2 :=
    Primrec.to₂ (primrec_negChoicesStep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_foldr Primrec.id (Primrec.const [[]]) hstep

private theorem primrec_listMax : Primrec listMax := by
  unfold listMax
  have hstep : Primrec₂ fun (_ : List ℕ) (p : ℕ × ℕ) => max p.1 p.2 :=
    Primrec.to₂ (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hstep

private theorem primrec_base₁ : Primrec fun p : SH × SH => base₁ p.1 p.2 := by
  unfold base₁
  exact Primrec.succ.comp (primrec_listMax.comp
    (Primrec.list_append.comp (primrec_shVars.comp Primrec.fst) (primrec_shVars.comp Primrec.snd)))

private theorem primrec_base₂ : Primrec fun p : SH × SH => base₂ p.1 p.2 := by
  unfold base₂
  exact Primrec.nat_mul.comp (Primrec.const 2) primrec_base₁

private theorem computable_elimList {qe : ℕ → List PureAtom → List PureAtom}
    (hqe : Computable₂ qe) :
    Computable fun p : List ℕ × List PureAtom => elimList qe p.1 p.2 := by
  have hstep : Computable fun r : (List ℕ × List PureAtom) × (ℕ × List PureAtom) => qe r.2.1 r.2.2 :=
    (Computable.comp hqe Computable.snd).of_eq (fun _ => rfl)
  exact (comp_list_foldr (f := Prod.fst) (g := Prod.snd) (h := fun _ q => qe q.1 q.2)
    Computable.fst Computable.snd hstep).of_eq (fun _ => rfl)

private theorem primrec_mkSubDisj : Primrec fun p : SH × List (List PureAtom) => mkSubDisj p.1 p.2 := by
  unfold mkSubDisj
  refine Primrec.list_map (primrec_negChoices.comp Primrec.snd) ?_
  show Primrec fun q : (SH × List (List PureAtom)) × List PureAtom =>
    (q.1.1.1, (q.2 ++ q.1.1.2.1, q.1.1.2.2.1, false))
  have hX : Primrec fun q : (SH × List (List PureAtom)) × List PureAtom => q.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hpi : Primrec fun q : (SH × List (List PureAtom)) × List PureAtom => q.1.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hsig : Primrec fun q : (SH × List (List PureAtom)) × List PureAtom => q.1.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  exact Primrec.pair hX
    (Primrec.pair (Primrec.list_append.comp Primrec.snd hpi)
      (Primrec.pair hsig (Primrec.const false)))

private theorem computable_subSHCore {qe : ℕ → List PureAtom → List PureAtom}
    (hqe : Computable₂ qe) :
    Computable fun p : SH × SH => subSHCore qe p.1 p.2 := by
  have hsig₁ : Primrec fun p : SH × SH => p.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hY₁ : Primrec fun p : SH × SH => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hpi'₁ : Primrec fun p : SH × SH => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hsig'₁ : Primrec fun p : SH × SH => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hact : Computable fun p : SH × SH => activeMaps p.2.2.2.1 p.1.2.2.1 :=
    ((primrec_activeMaps.comp hsig'₁ hsig₁).to_comp).of_eq (fun _ => rfl)
  have harg : Primrec fun q : (SH × SH) × List ℕ =>
      (q.1.2.1, q.1.2.2.1 ++ matchAtoms q.1.2.2.2.1 q.1.1.2.2.1 q.2) :=
    Primrec.pair (hY₁.comp Primrec.fst)
      (Primrec.list_append.comp (hpi'₁.comp Primrec.fst)
        (primrec_matchAtoms.comp
          (Primrec.pair (hsig'₁.comp Primrec.fst)
            (Primrec.pair (hsig₁.comp Primrec.fst) Primrec.snd))))
  have helim : Computable fun q : (SH × SH) × List ℕ =>
      elimList qe q.1.2.1 (q.1.2.2.1 ++ matchAtoms q.1.2.2.2.1 q.1.1.2.2.1 q.2) :=
    (Computable.comp (computable_elimList hqe) harg.to_comp).of_eq (fun _ => rfl)
  have hL : Computable fun p : SH × SH =>
      (activeMaps p.2.2.2.1 p.1.2.2.1).map (fun l =>
        elimList qe p.2.1 (p.2.2.1 ++ matchAtoms p.2.2.2.1 p.1.2.2.1 l)) :=
    comp_list_map (f := fun p : SH × SH => activeMaps p.2.2.2.1 p.1.2.2.1)
      (g := fun (p : SH × SH) (l : List ℕ) =>
        elimList qe p.2.1 (p.2.2.1 ++ matchAtoms p.2.2.2.1 p.1.2.2.1 l))
      hact helim
  exact (Computable.comp primrec_mkSubDisj.to_comp (Computable.pair Computable.fst hL)).of_eq
    (fun _ => rfl)

private theorem computable_subSH {qe : ℕ → List PureAtom → List PureAtom} (hqe : Computable₂ qe) :
    Computable fun p : SH × SH => subSH qe p.1 p.2 := by
  have hpair : Primrec fun p : SH × SH =>
      (shiftSH (base₁ p.1 p.2) p.1, shiftSH (base₂ p.1 p.2) p.2) :=
    Primrec.pair (primrec_shiftSH.comp primrec_base₁ Primrec.fst)
      (primrec_shiftSH.comp primrec_base₂ Primrec.snd)
  exact (Computable.comp (computable_subSHCore hqe) hpair.to_comp).of_eq (fun _ => rfl)

private theorem primrec_stripTrue : Primrec stripTrue := by
  unfold stripTrue
  exact Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const false)))

private theorem primrec_freshVar : Primrec freshVar := by
  have h : Primrec (fun Δ : LHS => listMax (lhsVars Δ) + 1) :=
    Primrec.succ.comp (primrec_listMax.comp primrec_lhsVars)
  exact h.of_eq (fun _ => rfl)

def incompatPairsOne (sig : List PtsTo) (i j : ℕ) : Disj :=
  if i = j then []
  else [([], ([(true, (sig.getD i defaultPts).1, (sig.getD j defaultPts).1)], [], true))]

def incompatPairs (sig : List PtsTo) : Disj :=
  (List.range sig.length).flatMap (fun i =>
    (List.range sig.length).flatMap (fun j => incompatPairsOne sig i j))

private theorem getD_eq_get {α : Type*} (l : List α) (d : α) (k : Fin l.length) :
    l.getD k.1 d = l.get k := by
  simp [List.getD_eq_getElem?_getD, k.isLt]

private theorem map_val_finRange (n : ℕ) :
    (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

private theorem incompatPairs_eq (sig : List PtsTo) :
    incompatPairs sig =
      (List.finRange sig.length).flatMap (fun i =>
        (List.finRange sig.length).flatMap (fun j =>
          if i = j then [] else [([], ([(true, (sig.get i).1, (sig.get j).1)], [], true))])) := by
  unfold incompatPairs incompatPairsOne
  rw [← map_val_finRange sig.length, List.flatMap_map]
  refine List.flatMap_congr (fun i _ => ?_)
  rw [List.flatMap_map]
  refine List.flatMap_congr (fun j _ => ?_)
  simp [Fin.ext_iff]

private instance : Primcodable Expr := inferInstance
private instance : Primcodable PureAtom := inferInstance
private instance : Primcodable PtsTo := inferInstance
private instance : Primcodable QF := inferInstance
private instance : Primcodable SH := inferInstance
private instance : Primcodable Disj := inferInstance
private instance : Primcodable LHS := inferInstance

private theorem primrec_incompatPairs : Primrec incompatPairs := by
  unfold incompatPairs incompatPairsOne
  refine Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length) ?_
  show Primrec fun p : List PtsTo × ℕ =>
    (List.range p.1.length).flatMap (fun j =>
      if p.2 = j then []
      else [([], ([(true, (p.1.getD p.2 defaultPts).1, (p.1.getD j defaultPts).1)], [], true))])
  refine Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) ?_
  show Primrec fun q : (List PtsTo × ℕ) × ℕ =>
    if q.1.2 = q.2 then ([] : Disj)
    else [([], ([(true, (q.1.1.getD q.1.2 defaultPts).1, (q.1.1.getD q.2 defaultPts).1)], [], true))]
  have hpti : Primrec fun q : (List PtsTo × ℕ) × ℕ => (q.1.1.getD q.1.2 defaultPts).1 :=
    Primrec.fst.comp ((Primrec.list_getD defaultPts).comp
      (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
  have hptj : Primrec fun q : (List PtsTo × ℕ) × ℕ => (q.1.1.getD q.2 defaultPts).1 :=
    Primrec.fst.comp ((Primrec.list_getD defaultPts).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hatom : Primrec fun q : (List PtsTo × ℕ) × ℕ =>
      (true, (q.1.1.getD q.1.2 defaultPts).1, (q.1.1.getD q.2 defaultPts).1) :=
    Primrec.pair (Primrec.const true) (Primrec.pair hpti hptj)
  have hsh : Primrec fun q : (List PtsTo × ℕ) × ℕ =>
      (([] : List ℕ), ([((true, (q.1.1.getD q.1.2 defaultPts).1,
        (q.1.1.getD q.2 defaultPts).1) : PureAtom)], ([] : List PtsTo), true)) :=
    Primrec.pair (Primrec.const [])
      (Primrec.pair (Primrec.list_cons.comp hatom (Primrec.const []))
        (Primrec.pair (Primrec.const []) (Primrec.const true)))
  exact Primrec.ite
    (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
    (Primrec.const [])
    (Primrec.list_cons.comp hsh (Primrec.const []))

private theorem primrec_incompat : Primrec incompat := by
  have h1 : Primrec fun Δ : LHS =>
      Δ.1.map (fun a => (([] : List ℕ), ([negAtom a], ([] : List PtsTo), true))) := by
    refine Primrec.list_map Primrec.fst ?_
    show Primrec fun q : LHS × PureAtom => (([] : List ℕ), ([negAtom q.2], ([] : List PtsTo), true))
    exact Primrec.pair (Primrec.const [])
      (Primrec.pair (Primrec.list_cons.comp (primrec_negAtom.comp Primrec.snd) (Primrec.const []))
        (Primrec.pair (Primrec.const []) (Primrec.const true)))
  have h2 : Primrec fun Δ : LHS =>
      Δ.2.map (fun pt => (([] : List ℕ), ([(true, pt.1, (Sum.inr 0 : Expr))], ([] : List PtsTo), true))) := by
    refine Primrec.list_map Primrec.snd ?_
    show Primrec fun q : LHS × PtsTo =>
      (([] : List ℕ), ([(true, q.2.1, (Sum.inr 0 : Expr))], ([] : List PtsTo), true))
    have hatom : Primrec fun q : LHS × PtsTo => (true, q.2.1, (Sum.inr 0 : Expr)) :=
      Primrec.pair (Primrec.const true)
        (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.const (Sum.inr 0)))
    exact Primrec.pair (Primrec.const [])
      (Primrec.pair (Primrec.list_cons.comp hatom (Primrec.const []))
        (Primrec.pair (Primrec.const []) (Primrec.const true)))
  have h3 : Primrec fun Δ : LHS => incompatPairs Δ.2 :=
    primrec_incompatPairs.comp Primrec.snd
  have h4 : Primrec fun Δ : LHS =>
      Δ.2.map (fun pt => ([freshVar Δ], (([] : List PureAtom), [(pt.1, (Sum.inl (freshVar Δ) : Expr))], true))) := by
    refine Primrec.list_map Primrec.snd ?_
    show Primrec fun q : LHS × PtsTo =>
      ([freshVar q.1], (([] : List PureAtom), [(q.2.1, (Sum.inl (freshVar q.1) : Expr))], true))
    have hf : Primrec fun q : LHS × PtsTo => freshVar q.1 :=
      primrec_freshVar.comp Primrec.fst
    have hpt : Primrec fun q : LHS × PtsTo => (q.2.1, (Sum.inl (freshVar q.1) : Expr)) :=
      Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.sumInl.comp hf)
    exact Primrec.pair (Primrec.list_cons.comp hf (Primrec.const []))
      (Primrec.pair (Primrec.const [])
        (Primrec.pair (Primrec.list_cons.comp hpt (Primrec.const [])) (Primrec.const true)))
  have hall := Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.list_append.comp h1 h2) h3) h4
  refine hall.of_eq (fun Δ => ?_)
  unfold incompat
  rw [incompatPairs_eq]

private theorem computable_subDisjBySH {qe : ℕ → List PureAtom → List PureAtom}
    (hqe : Computable₂ qe) :
    Computable fun p : Disj × SH => subDisjBySH qe p.1 p.2 := by
  have hstep : Computable fun q : (Disj × SH) × SH => subSH qe q.2 q.1.2 :=
    (Computable.comp (computable_subSH hqe)
      (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))).of_eq (fun _ => rfl)
  exact (comp_list_flatMap (f := Prod.fst) (g := fun p K => subSH qe K p.2)
    Computable.fst hstep).of_eq (fun _ => rfl)

private theorem computable_subSHByList {qe : ℕ → List PureAtom → List PureAtom}
    (hqe : Computable₂ qe) :
    Computable fun p : SH × Disj => subSHByList qe p.1 p.2 := by
  have hinit : Computable fun p : SH × Disj => ([p.1] : Disj) :=
    (Primrec.list_cons.comp Primrec.fst (Primrec.const [])).to_comp
  have hstep : Computable fun q : (SH × Disj) × (Disj × SH) => subDisjBySH qe q.2.1 q.2.2 :=
    (Computable.comp (computable_subDisjBySH hqe) Computable.snd).of_eq (fun _ => rfl)
  exact (comp_list_foldl (f := Prod.snd) (g := fun p => [p.1])
    (h := fun _ r => subDisjBySH qe r.1 r.2)
    Computable.snd hinit hstep).of_eq (fun _ => rfl)

private theorem computable_minDisj {qe : ℕ → List PureAtom → List PureAtom}
    (hqe : Computable₂ qe) :
    Computable (minDisj qe) := by
  have hstep : Computable fun q : Disj × SH => subSHByList qe q.2 q.1 :=
    (Computable.comp (computable_subSHByList hqe)
      (Computable.pair Computable.snd Computable.fst)).of_eq (fun _ => rfl)
  exact (comp_list_flatMap (f := id) (g := fun D₁ K => subSHByList qe K D₁)
    Computable.id hstep).of_eq (fun _ => rfl)

private theorem primrec_convBase : Primrec fun p : LHS × SH => convBase p.1 p.2 := by
  unfold convBase
  exact Primrec.succ.comp (primrec_listMax.comp
    (Primrec.list_append.comp (primrec_lhsVars.comp Primrec.fst) (primrec_shVars.comp Primrec.snd)))

private theorem computable_solveAbduction {qe : ℕ → List PureAtom → List PureAtom}
    {search : LHS → SH → Disj} (hqe : Computable₂ qe) (hsearch : Computable₂ search) :
    Computable₂ (solveAbduction qe search) := by
  have hH₀ : Primrec fun p : LHS × SH => shiftSH (convBase p.1 p.2) p.2 :=
    primrec_shiftSH.comp primrec_convBase Primrec.snd
  have hD₀ : Computable fun p : LHS × SH => search p.1 (shiftSH (convBase p.1 p.2) p.2) :=
    (Computable.comp hsearch (Computable.pair Computable.fst hH₀.to_comp)).of_eq (fun _ => rfl)
  have hinc : Computable fun p : LHS × SH => incompat p.1 :=
    (primrec_incompat.comp Primrec.fst).to_comp
  have hmapStrip : Primrec fun D : Disj => D.map stripTrue :=
    Primrec.list_map Primrec.id (primrec_stripTrue.comp Primrec.snd)
  have hD₁ : Computable fun p : LHS × SH =>
      (search p.1 (shiftSH (convBase p.1 p.2) p.2) ++ incompat p.1).map stripTrue :=
    (Computable.comp hmapStrip.to_comp (Computable.list_append.comp hD₀ hinc)).of_eq (fun _ => rfl)
  exact (Computable.comp (computable_minDisj hqe) hD₁).of_eq (fun _ => rfl)

/-! ## Heap and subheap lemmas -/

private theorem heap_ext {h k : Heap} (hc : h.cell = k.cell) : h = k := by
  cases h
  cases k
  cases hc
  rfl

private theorem subheap_antisymm {a b : Heap} (hab : Heap.Subheap a b) (hba : Heap.Subheap b a) :
    a = b := by
  apply heap_ext
  funext l
  cases ha : a.cell l with
  | some v => exact (hab l v ha).symm
  | none =>
    cases hb : b.cell l with
    | none => rfl
    | some v =>
      have := hba l v hb
      rw [ha] at this
      cases this

private theorem subheap_trans {a b c : Heap} (hab : Heap.Subheap a b) (hbc : Heap.Subheap b c) :
    Heap.Subheap a c :=
  fun l v hv => hbc l v (hab l v hv)

private theorem union_sub_right {h a b : Heap} (hu : Heap.IsUnion h a b) :
    Heap.Subheap b h := by
  intro l v hv
  have hdisj := hu.1 l
  have hcell := hu.2 l
  rcases hdisj with ha | hb
  · simp [ha, hv] at hcell
    exact hcell
  · simp [hb] at hv

private theorem sub_split {a h : Heap} (ha : Heap.Subheap a h) :
    ∃ b, Heap.IsUnion h b a := by
  classical
  let b : Heap := {
    cell := fun l => if a.cell l = none then h.cell l else none
    nil_unalloc := by simp [a.nil_unalloc, h.nil_unalloc]
    finite_dom := h.finite_dom.subset (by
      intro l hl
      simp only [Set.mem_setOf_eq] at hl ⊢
      by_contra hn
      simp [hn] at hl) }
  refine ⟨b, ?_, ?_⟩
  · intro l
    by_cases hn : a.cell l = none
    · exact Or.inr hn
    · exact Or.inl (by simp [b, hn])
  · intro l
    cases he : a.cell l with
    | none => simp [b, he]
    | some v => simp [b, he, ha l v he]

private theorem mem_sepConj_emp_compl_iff (G : Pred) (p : State) :
    p ∈ sepConj empᶜ G ↔
      ∃ h' : Heap, Heap.Subheap h' p.2 ∧ (p.1, h') ∈ G ∧ h' ≠ p.2 := by
  constructor
  · rintro ⟨h₀, h₁, hu, hh₀, hh₁⟩
    refine ⟨h₁, union_sub_right hu, hh₁, ?_⟩
    intro h_eq
    apply hh₀
    intro l
    rcases hu.1 l with h0 | h1
    · exact h0
    · have hcell := hu.2 l
      rw [h_eq] at h1
      rw [h1] at hcell
      cases hh0 : h₀.cell l with
      | none => rfl
      | some v =>
        rw [hh0] at hcell
        cases hcell
  · rintro ⟨h₁, hsub, hh₁, hne⟩
    obtain ⟨h₀, hu⟩ := sub_split hsub
    refine ⟨h₀, h₁, hu, ?_, hh₁⟩
    intro hh₀
    apply hne
    apply heap_ext
    funext l
    have h0 : h₀.cell l = none := hh₀ l
    have hcell := hu.2 l
    rw [h0] at hcell
    simpa using hcell.symm

private theorem mem_subP_iff_no_proper (F G : Pred) (p : State) :
    p ∈ subP F G ↔
      p ∈ F ∧ ¬ ∃ h' : Heap, Heap.Subheap h' p.2 ∧ h' ≠ p.2 ∧ (p.1, h') ∈ G := by
  simp only [subP, Set.mem_inter_iff, Set.mem_compl_iff, mem_sepConj_emp_compl_iff]
  refine and_congr_right (fun _ => not_congr ?_)
  constructor
  · rintro ⟨h', hsub, hh', hne⟩
    exact ⟨h', hsub, hne, hh'⟩
  · rintro ⟨h', hsub, hne, hh'⟩
    exact ⟨h', hsub, hh', hne⟩

/-! ## `spatialDen` and `mkHeap` lemmas -/

private def union (h₀ h₁ : Heap) : Heap where
  cell := fun l => (h₀.cell l).or (h₁.cell l)
  nil_unalloc := by simp [h₀.nil_unalloc, h₁.nil_unalloc]
  finite_dom := by
    refine Set.Finite.subset (h₀.finite_dom.union h₁.finite_dom) ?_
    intro l hl
    simp only [Set.mem_setOf_eq, Set.mem_union] at hl ⊢
    change (h₀.cell l).or (h₁.cell l) ≠ none at hl
    cases h0 : h₀.cell l with
    | some v => exact Or.inl (by simp)
    | none =>
      cases h1 : h₁.cell l with
      | some v => exact Or.inr (by simp)
      | none =>
        exfalso
        apply hl
        rw [h0, h1]
        rfl

private theorem union_cell (h₀ h₁ : Heap) (l : ℕ) :
    (union h₀ h₁).cell l = (h₀.cell l).or (h₁.cell l) := rfl

private def emptyHeap : Heap where
  cell := fun _ => none
  nil_unalloc := rfl
  finite_dom := by
    refine Set.Finite.subset (Set.finite_singleton 0) ?_
    intro l hl
    exact absurd rfl hl

private def ptsHeap (l v : ℕ) : Heap where
  cell := fun l' => if l' = l ∧ l ≠ 0 then some v else none
  nil_unalloc := by
    by_cases h : (0 : ℕ) = l
    · subst h; simp
    · simp [h]
  finite_dom := by
    refine Set.Finite.subset (Set.finite_singleton l) ?_
    intro l' hl
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hl ⊢
    by_cases h : l' = l
    · exact h
    · exact absurd (by simp [h]) hl

private theorem ptsHeap_cell_self (l v : ℕ) (hl : l ≠ 0) : (ptsHeap l v).cell l = some v :=
  show (if l = l ∧ l ≠ 0 then some v else none) = some v from if_pos ⟨rfl, hl⟩

private theorem ptsHeap_cell_of_ne {l l' v : ℕ} (h : l' ≠ l) : (ptsHeap l v).cell l' = none :=
  show (if l' = l ∧ l ≠ 0 then some v else none) = none from if_neg (fun hc => h hc.1)

private theorem or_none_eq (x : Option ℕ) : x.or none = x := by cases x <;> rfl

private theorem isUnion_iff {h h₀ h₁ : Heap} :
    Heap.IsUnion h h₀ h₁ ↔ h = union h₀ h₁ ∧ Heap.Disjoint h₀ h₁ := by
  constructor
  · rintro ⟨hd, hc⟩
    exact ⟨heap_ext (funext fun l => hc l), hd⟩
  · rintro ⟨rfl, hd⟩
    exact ⟨hd, fun l => union_cell h₀ h₁ l⟩

private theorem spatialDen_cons (pt : PtsTo) (sig : List PtsTo) (tr : Bool) :
    spatialDen (pt :: sig) tr = sepConj (ptsDen pt) (spatialDen sig tr) := rfl

private theorem get_cons_zero' (a : PtsTo) (rest : List PtsTo) :
    (a :: rest).get (0 : Fin (a :: rest).length) = a := List.get_cons_zero ..

private theorem get_cons_succ' {a : PtsTo} {rest : List PtsTo} (k : Fin rest.length) :
    (a :: rest).get k.succ = rest.get k := List.get_cons_succ ..

private theorem spatialDen_cell_aux : ∀ (sig : List PtsTo) (tr : Bool) (s : Stack) (h : Heap)
    (k : Fin sig.length), (s, h) ∈ spatialDen sig tr →
      h.cell (evalE s (sig.get k).1) = some (evalE s (sig.get k).2) := by
  intro sig
  induction sig with
  | nil => intro tr s h k _; exact absurd k.isLt (Nat.not_lt_zero k.1)
  | cons a rest ih =>
    intro tr s h k hh
    rw [spatialDen_cons] at hh
    obtain ⟨h₀, h₁, hu, h0, h1⟩ := hh
    obtain ⟨hd, hc⟩ := hu
    cases k using Fin.cases with
    | zero =>
      rw [get_cons_zero']
      have h0' : h₀.cell (evalE s a.1) = some (evalE s a.2) := by
        have h2 := h0
        simp only [ptsDen, Set.mem_setOf_eq] at h2
        simpa using h2.2 (evalE s a.1)
      rw [hc (evalE s a.1), h0']
      simp
    | succ i =>
      rw [get_cons_succ']
      have h1' : h₁.cell (evalE s (rest.get i).1) = some (evalE s (rest.get i).2) :=
        ih tr s h₁ i h1
      rcases hd (evalE s (rest.get i).1) with hd0 | hd1
      · rw [hc (evalE s (rest.get i).1), hd0, h1']
        simp
      · rw [h1'] at hd1
        exact absurd hd1 (by simp)

private theorem spatialDen_cell {s : Stack} {h : Heap} {sig : List PtsTo} {tr : Bool}
    (hh : (s, h) ∈ spatialDen sig tr) (k : Fin sig.length) :
    h.cell (evalE s (sig.get k).1) = some (evalE s (sig.get k).2) :=
  spatialDen_cell_aux sig tr s h k hh

private theorem spatialDen_inj_aux : ∀ (sig : List PtsTo) (tr : Bool) (s : Stack) (h : Heap)
    (i j : Fin sig.length), (s, h) ∈ spatialDen sig tr →
      evalE s (sig.get i).1 = evalE s (sig.get j).1 → i = j := by
  intro sig
  induction sig with
  | nil => intro tr s h i _ _ _; exact absurd i.isLt (Nat.not_lt_zero i.1)
  | cons a rest ih =>
    intro tr s h i j hh hij
    rw [spatialDen_cons] at hh
    obtain ⟨h₀, h₁, hu, h0, h1⟩ := hh
    obtain ⟨hd, _⟩ := hu
    have h0' : h₀.cell (evalE s a.1) = some (evalE s a.2) := by
      have h2 := h0
      simp only [ptsDen, Set.mem_setOf_eq] at h2
      simpa using h2.2 (evalE s a.1)
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j' =>
        exfalso
        rw [get_cons_zero', get_cons_succ'] at hij
        have hcell := spatialDen_cell h1 j'
        rw [← hij] at hcell
        rcases hd (evalE s a.1) with hd0 | hd1
        · rw [h0'] at hd0
          exact absurd hd0 (by simp)
        · rw [hcell] at hd1
          exact absurd hd1 (by simp)
    | succ i' =>
      cases j using Fin.cases with
      | zero =>
        exfalso
        rw [get_cons_zero', get_cons_succ'] at hij
        have hcell := spatialDen_cell h1 i'
        rw [hij] at hcell
        rcases hd (evalE s a.1) with hd0 | hd1
        · rw [h0'] at hd0
          exact absurd hd0 (by simp)
        · rw [hcell] at hd1
          exact absurd hd1 (by simp)
      | succ j' =>
        rw [get_cons_succ'] at hij
        exact Fin.succ_inj.mpr (ih tr s h₁ i' j' h1 hij)

private theorem spatialDen_inj {s : Stack} {h : Heap} {sig : List PtsTo} {tr : Bool}
    (hh : (s, h) ∈ spatialDen sig tr) (i j : Fin sig.length)
    (hij : evalE s (sig.get i).1 = evalE s (sig.get j).1) : i = j :=
  spatialDen_inj_aux sig tr s h i j hh hij

private theorem spatialDen_dom : ∀ (sig : List PtsTo) {s : Stack} {h : Heap} {l v : ℕ},
    (s, h) ∈ spatialDen sig false → h.cell l = some v →
      ∃ j : Fin sig.length, l = evalE s (sig.get j).1 ∧ v = evalE s (sig.get j).2 := by
  intro sig
  induction sig with
  | nil =>
    intro s h l v hh hl
    have hnone : h.cell l = none := hh l
    rw [hnone] at hl
    cases hl
  | cons a rest ih =>
    intro s h l v hh hl
    rw [spatialDen_cons] at hh
    obtain ⟨h₀, h₁, hu, h0, h1⟩ := hh
    have hcell := hu.2 l
    rw [hl] at hcell
    cases hc0 : h₀.cell l with
    | some v0 =>
      rw [hc0] at hcell
      injection hcell with hcell'
      have h0' := h0.2 l
      rw [hc0] at h0'
      by_cases heq : l = evalE s a.1
      · rw [if_pos heq] at h0'
        injection h0' with h0''
        exact ⟨0, heq, hcell'.trans h0''⟩
      · rw [if_neg heq] at h0'
        cases h0'
    | none =>
      rw [hc0] at hcell
      obtain ⟨j', hj1, hj2⟩ := ih h1 hcell.symm
      exact ⟨j'.succ, hj1, hj2⟩

private def mkHeap (s : Stack) : List PtsTo → Heap
  | [] => emptyHeap
  | pt :: rest => union (ptsHeap (evalE s pt.1) (evalE s pt.2)) (mkHeap s rest)

private theorem mkHeap_spec (s : Stack) (sig : List PtsTo)
    (hne : ∀ k : Fin sig.length, evalE s (sig.get k).1 ≠ 0)
    (hinj : ∀ i j : Fin sig.length, i ≠ j → evalE s (sig.get i).1 ≠ evalE s (sig.get j).1) :
    (s, mkHeap s sig) ∈ spatialDen sig false := by
  suffices (s, mkHeap s sig) ∈ spatialDen sig false ∧
      (∀ k : Fin sig.length,
        (mkHeap s sig).cell (evalE s (sig.get k).1) = some (evalE s (sig.get k).2)) ∧
      (∀ l, (∀ k : Fin sig.length, evalE s (sig.get k).1 ≠ l) →
        (mkHeap s sig).cell l = none) from this.1
  induction sig with
  | nil =>
    refine ⟨?_, ?_, ?_⟩
    · show (s, emptyHeap) ∈ emp
      intro l
      rfl
    · intro k
      exact absurd k.isLt (Nat.not_lt_zero k.1)
    · intro l _
      rfl
  | cons a rest ih =>
    have hne' : ∀ k : Fin rest.length, evalE s (rest.get k).1 ≠ 0 := by
      intro k
      simpa using hne k.succ
    have hinj' : ∀ i j : Fin rest.length, i ≠ j →
        evalE s (rest.get i).1 ≠ evalE s (rest.get j).1 := by
      intro i j hij
      simpa using hinj i.succ j.succ (fun hc => hij (Fin.succ_inj.mp hc))
    obtain ⟨ih1, ih2, ih3⟩ := ih hne' hinj'
    have ha0 : evalE s a.1 ≠ 0 := by simpa using hne 0
    have hcons : ∀ k : Fin rest.length, evalE s (rest.get k).1 ≠ evalE s a.1 := by
      intro k
      have h := hinj 0 k.succ (Fin.succ_ne_zero k).symm
      rw [get_cons_zero', get_cons_succ'] at h
      exact h.symm
    refine ⟨?_, ?_, ?_⟩
    · rw [spatialDen_cons]
      refine ⟨ptsHeap (evalE s a.1) (evalE s a.2), mkHeap s rest, ?_, ?_, ih1⟩
      · refine isUnion_iff.2 ⟨rfl, ?_⟩
        intro l
        by_cases hl : l = evalE s a.1
        · right
          refine ih3 l ?_
          intro k
          rw [hl]
          exact hcons k
        · left
          simp [ptsHeap, hl]
      · refine ⟨ha0, ?_⟩
        intro l
        by_cases hl : l = evalE s a.1
        · subst hl
          simp [ptsHeap, ha0]
        · simp [ptsHeap, hl]
    · intro k
      cases k using Fin.cases with
      | zero =>
        rw [get_cons_zero']
        have hM : (mkHeap s rest).cell (evalE s a.1) = none := ih3 _ hcons
        change (union (ptsHeap (evalE s a.1) (evalE s a.2)) (mkHeap s rest)).cell
          (evalE s a.1) = some (evalE s a.2)
        rw [union_cell, hM, or_none_eq]
        exact ptsHeap_cell_self _ _ ha0
      | succ i =>
        rw [get_cons_succ']
        have hP : (ptsHeap (evalE s a.1) (evalE s a.2)).cell
            (evalE s (rest.get i).1) = none := ptsHeap_cell_of_ne (hcons i)
        change (union (ptsHeap (evalE s a.1) (evalE s a.2)) (mkHeap s rest)).cell
          (evalE s (rest.get i).1) = some (evalE s (rest.get i).2)
        rw [union_cell, hP]
        simpa using ih2 i
    · intro l hl
      change (union (ptsHeap (evalE s a.1) (evalE s a.2)) (mkHeap s rest)).cell l = none
      rw [union_cell]
      have hP : (ptsHeap (evalE s a.1) (evalE s a.2)).cell l = none := by
        have h0 := hl 0
        rw [get_cons_zero'] at h0
        exact ptsHeap_cell_of_ne h0.symm
      have hM : (mkHeap s rest).cell l = none := by
        refine ih3 l ?_
        intro k
        have h := hl k.succ
        rw [get_cons_succ'] at h
        exact h
      rw [hP, hM]
      rfl

private theorem spatialDen_false_sub_true : ∀ (sig : List PtsTo) {s : Stack} {h : Heap},
    (s, h) ∈ spatialDen sig false → (s, h) ∈ spatialDen sig true := by
  intro sig
  induction sig with
  | nil =>
    intro s h _
    exact Set.mem_univ _
  | cons a rest ih =>
    intro s h hh
    rw [spatialDen_cons] at hh ⊢
    obtain ⟨h₀, h₁, hu, h0, h1⟩ := hh
    exact ⟨h₀, h₁, hu, h0, ih h1⟩

private theorem spatialDen_exists_sub_false {sig : List PtsTo} {tr : Bool} {s : Stack} {h : Heap}
    (hh : (s, h) ∈ spatialDen sig tr) :
    ∃ h' : Heap, Heap.Subheap h' h ∧ (s, h') ∈ spatialDen sig false := by
  have hne : ∀ k : Fin sig.length, evalE s (sig.get k).1 ≠ 0 := by
    intro k h0
    have hc := spatialDen_cell hh k
    rw [h0, h.nil_unalloc] at hc
    cases hc
  have hinj : ∀ i j : Fin sig.length, i ≠ j → evalE s (sig.get i).1 ≠ evalE s (sig.get j).1 :=
    fun i j hij heq => hij (spatialDen_inj hh i j heq)
  have hmk := mkHeap_spec s sig hne hinj
  refine ⟨mkHeap s sig, ?_, hmk⟩
  intro l v hlv
  obtain ⟨k, rfl, rfl⟩ := spatialDen_dom sig hmk hlv
  exact spatialDen_cell hh k

/-! ## Stack congruence, `NotFree`, and alpha-renaming (`shiftSH`) -/

private theorem evalE_congr {s s' : Stack} {e : Expr} (h : ∀ x ∈ exprVars e, s' x = s x) :
    evalE s' e = evalE s e := by
  rcases e with x | k
  · simpa [exprVars, evalE] using h x (by simp [exprVars])
  · rfl

private theorem pureDen_congr {pi : List PureAtom} {s s' : Stack} {h : Heap}
    (hs : ∀ x ∈ pureVars pi, s' x = s x) (hp : (s, h) ∈ pureDen pi) : (s', h) ∈ pureDen pi := by
  intro a ha
  have hv : ∀ x ∈ exprVars a.2.1 ++ exprVars a.2.2, s' x = s x := by
    intro x hx
    exact hs x (List.mem_flatMap.mpr ⟨a, ha, hx⟩)
  have e1 := evalE_congr (e := a.2.1) (fun x hx => hv x (List.mem_append.mpr (Or.inl hx)))
  have e2 := evalE_congr (e := a.2.2) (fun x hx => hv x (List.mem_append.mpr (Or.inr hx)))
  have hpa := hp a ha
  simp only [atomHolds] at hpa ⊢
  rw [e1, e2]
  exact hpa

private theorem ptsDen_congr {pt : PtsTo} {s s' : Stack} {h : Heap}
    (hs : ∀ x ∈ exprVars pt.1 ++ exprVars pt.2, s' x = s x) (hp : (s, h) ∈ ptsDen pt) :
    (s', h) ∈ ptsDen pt := by
  simp only [ptsDen, Set.mem_setOf_eq] at hp ⊢
  have e1 := evalE_congr (e := pt.1) (fun x hx => hs x (List.mem_append.mpr (Or.inl hx)))
  have e2 := evalE_congr (e := pt.2) (fun x hx => hs x (List.mem_append.mpr (Or.inr hx)))
  exact ⟨by rw [e1]; exact hp.1, fun l => by rw [e1, e2]; exact hp.2 l⟩

private theorem spatialDen_congr : ∀ (sig : List PtsTo) (tr : Bool) {s s' : Stack} {h : Heap},
    (∀ x ∈ ptsVars sig, s' x = s x) → (s, h) ∈ spatialDen sig tr →
      (s', h) ∈ spatialDen sig tr := by
  intro sig
  induction sig with
  | nil =>
    intro tr s s' h _ hh
    simpa [spatialDen, emp] using hh
  | cons a rest ih =>
    intro tr s s' h hs hh
    rw [spatialDen_cons] at hh ⊢
    obtain ⟨h₀, h₁, hu, h0, h1⟩ := hh
    have hs1 : ∀ x ∈ exprVars a.1 ++ exprVars a.2, s' x = s x :=
      fun x hx => hs x (List.mem_flatMap.mpr ⟨a, List.mem_cons.mpr (Or.inl rfl), hx⟩)
    have hs2 : ∀ x ∈ ptsVars rest, s' x = s x := by
      intro x hx
      obtain ⟨pt, hmem, hx'⟩ := List.mem_flatMap.1 hx
      exact hs x (List.mem_flatMap.mpr ⟨pt, List.mem_cons.mpr (Or.inr hmem), hx'⟩)
    exact ⟨h₀, h₁, hu, ptsDen_congr hs1 h0, ih tr hs2 h1⟩

private theorem qfDen_congr {q : QF} {s s' : Stack} {h : Heap}
    (hs : ∀ x ∈ qVars q, s' x = s x) (hp : (s, h) ∈ qfDen q) : (s', h) ∈ qfDen q := by
  obtain ⟨hp1, hp2⟩ := hp
  refine ⟨pureDen_congr (fun x hx => hs x (List.mem_append.mpr (Or.inl hx))) hp1,
    spatialDen_congr q.2.1 q.2.2 (fun x hx => hs x (List.mem_append.mpr (Or.inr hx))) hp2⟩

private theorem mem_foldr_exQ_of_mem {F : Pred} : ∀ {X : List ℕ} {p : State},
    p ∈ X.foldr exQ F → ∃ s' : Stack, (∀ x ∉ X, s' x = p.1 x) ∧ (s', p.2) ∈ F := by
  intro X
  induction X with
  | nil =>
    intro p hp
    exact ⟨p.1, by simp, hp⟩
  | cons x xs ih =>
    intro p hp
    rw [List.foldr_cons] at hp
    obtain ⟨v, hv⟩ := hp
    obtain ⟨s', hs', hsF⟩ := ih hv
    refine ⟨s', ?_, hsF⟩
    intro y hy
    have hyx : y ≠ x := fun hc => hy (List.mem_cons.mpr (Or.inl hc))
    have hy' : y ∉ xs := fun hc => hy (List.mem_cons.mpr (Or.inr hc))
    simpa [Function.update_of_ne hyx] using hs' y hy'

private theorem mem_foldr_exQ_of_stack {F : Pred} : ∀ {X : List ℕ} {s s' : Stack} {h : Heap},
    (∀ x ∉ X, s' x = s x) → (s', h) ∈ F → (s, h) ∈ X.foldr exQ F := by
  intro X
  induction X with
  | nil =>
    intro s s' h hs hp
    have heq : s' = s := funext (fun x => hs x (by simp))
    rwa [heq] at hp
  | cons x xs ih =>
    intro s s' h hs hp
    rw [List.foldr_cons]
    refine ⟨s' x, ih ?_ hp⟩
    intro y hy
    by_cases hyx : y = x
    · subst hyx
      simp [Function.update]
    · have hy_cons : y ∉ x :: xs := by
        intro hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact hyx rfl
        · exact hy hc'
      rw [hs y hy_cons, Function.update_of_ne hyx]

private theorem mem_foldr_exQ_qf {q : QF} {X : List ℕ} {s s' : Stack} {h : Heap}
    (hs : ∀ x ∈ qVars q, x ∉ X → s' x = s x) (hp : (s', h) ∈ qfDen q) :
    (s, h) ∈ X.foldr exQ (qfDen q) := by
  classical
  let s'' : Stack := fun x => if x ∈ X then s' x else s x
  have h1 : ∀ x ∉ X, s'' x = s x := fun x hx => if_neg hx
  have h2 : ∀ x ∈ qVars q, s'' x = s' x := by
    intro x hx
    dsimp [s'']
    by_cases hxX : x ∈ X
    · exact if_pos hxX
    · rw [if_neg hxX, hs x hx hxX]
  exact mem_foldr_exQ_of_stack h1 (qfDen_congr h2 hp)

private theorem evalE_shiftExpr {X : List ℕ} {base : ℕ} {s₁ s₂ : Stack} {e : Expr}
    (hs : ∀ x ∈ exprVars e, s₂ (shiftVar X base x) = s₁ x) :
    evalE s₂ (shiftExpr X base e) = evalE s₁ e := by
  cases e with
  | inl x =>
    simpa [shiftExpr, evalE] using hs x (by simp [exprVars])
  | inr k => rfl

private theorem atomHolds_shiftAtom {X : List ℕ} {base : ℕ} {s₁ s₂ : Stack} {a : PureAtom}
    (hs : ∀ x ∈ exprVars a.2.1 ++ exprVars a.2.2, s₂ (shiftVar X base x) = s₁ x) :
    atomHolds s₂ (shiftAtom X base a) ↔ atomHolds s₁ a := by
  have e1 := evalE_shiftExpr (X := X) (base := base) (e := a.2.1)
    (fun x hx => hs x (List.mem_append.mpr (Or.inl hx)))
  have e2 := evalE_shiftExpr (X := X) (base := base) (e := a.2.2)
    (fun x hx => hs x (List.mem_append.mpr (Or.inr hx)))
  simp only [shiftAtom, atomHolds, e1, e2]

private theorem pureDen_shift {X : List ℕ} {base : ℕ} {s₁ s₂ : Stack} {h : Heap}
    {pi : List PureAtom} (hs : ∀ x ∈ pureVars pi, s₂ (shiftVar X base x) = s₁ x) :
    (s₂, h) ∈ pureDen (pi.map (shiftAtom X base)) ↔ (s₁, h) ∈ pureDen pi := by
  simp only [pureDen, Set.mem_setOf_eq, List.forall_mem_map]
  refine forall₂_congr (fun a ha => ?_)
  exact atomHolds_shiftAtom (fun x hx => hs x (List.mem_flatMap.mpr ⟨a, ha, hx⟩))

private theorem ptsDen_shift {X : List ℕ} {base : ℕ} {s₁ s₂ : Stack} {h : Heap} {pt : PtsTo}
    (hs : ∀ x ∈ exprVars pt.1 ++ exprVars pt.2, s₂ (shiftVar X base x) = s₁ x) :
    (s₂, h) ∈ ptsDen (shiftPts X base pt) ↔ (s₁, h) ∈ ptsDen pt := by
  have e1 := evalE_shiftExpr (X := X) (base := base) (e := pt.1)
    (fun x hx => hs x (List.mem_append.mpr (Or.inl hx)))
  have e2 := evalE_shiftExpr (X := X) (base := base) (e := pt.2)
    (fun x hx => hs x (List.mem_append.mpr (Or.inr hx)))
  simp only [shiftPts, ptsDen, Set.mem_setOf_eq, e1, e2]

private theorem spatialDen_shift : ∀ (sig : List PtsTo) (tr : Bool) {X : List ℕ} {base : ℕ}
    {s₁ s₂ : Stack} {h : Heap},
    (∀ x ∈ ptsVars sig, s₂ (shiftVar X base x) = s₁ x) →
      ((s₂, h) ∈ spatialDen (sig.map (shiftPts X base)) tr ↔ (s₁, h) ∈ spatialDen sig tr) := by
  intro sig
  induction sig with
  | nil =>
    intro tr X base s₁ s₂ h _
    simp [spatialDen, emp]
  | cons a rest ih =>
    intro tr X base s₁ s₂ h hs
    simp only [List.map_cons, spatialDen_cons, sepConj, Set.mem_setOf_eq]
    have hs1 : ∀ x ∈ exprVars a.1 ++ exprVars a.2, s₂ (shiftVar X base x) = s₁ x :=
      fun x hx => hs x (List.mem_flatMap.mpr ⟨a, List.mem_cons.mpr (Or.inl rfl), hx⟩)
    have hs2 : ∀ x ∈ ptsVars rest, s₂ (shiftVar X base x) = s₁ x := by
      intro x hx
      obtain ⟨pt, hmem, hx'⟩ := List.mem_flatMap.1 hx
      exact hs x (List.mem_flatMap.mpr ⟨pt, List.mem_cons.mpr (Or.inr hmem), hx'⟩)
    refine exists_congr (fun h₀ => exists_congr (fun h₁ => and_congr Iff.rfl (and_congr ?_ ?_)))
    · exact ptsDen_shift hs1
    · exact ih tr hs2

private theorem qfDen_shift {X : List ℕ} {base : ℕ} {s₁ s₂ : Stack} {h : Heap} {q : QF}
    (hs : ∀ x ∈ qVars q, s₂ (shiftVar X base x) = s₁ x) :
    (s₂, h) ∈ qfDen (shiftQF X base q) ↔ (s₁, h) ∈ qfDen q := by
  simp only [qfDen, shiftQF, Set.mem_inter_iff]
  exact and_congr
    (pureDen_shift (fun x hx => hs x (List.mem_append.mpr (Or.inl hx))))
    (spatialDen_shift q.2.1 q.2.2 (fun x hx => hs x (List.mem_append.mpr (Or.inr hx))))

private theorem mem_exprVars_shiftExpr {X : List ℕ} {base : ℕ} {e : Expr} {y : ℕ}
    (hy : y ∈ exprVars (shiftExpr X base e)) :
    ∃ x ∈ exprVars e, y = shiftVar X base x := by
  cases e with
  | inl x =>
    simp only [shiftExpr, exprVars, List.mem_singleton] at hy ⊢
    exact ⟨x, rfl, hy⟩
  | inr k =>
    simp [shiftExpr, exprVars] at hy

private theorem mem_pureVars_shift {X : List ℕ} {base : ℕ} {pi : List PureAtom} {y : ℕ}
    (hy : y ∈ pureVars (pi.map (shiftAtom X base))) :
    ∃ x ∈ pureVars pi, y = shiftVar X base x := by
  obtain ⟨a', ha', hy'⟩ := List.mem_flatMap.mp hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
  rcases List.mem_append.mp hy' with h1 | h2
  · obtain ⟨x, hx, rfl⟩ := mem_exprVars_shiftExpr h1
    exact ⟨x, List.mem_flatMap.mpr ⟨a, ha, List.mem_append.mpr (Or.inl hx)⟩, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := mem_exprVars_shiftExpr h2
    exact ⟨x, List.mem_flatMap.mpr ⟨a, ha, List.mem_append.mpr (Or.inr hx)⟩, rfl⟩

private theorem mem_ptsVars_shift {X : List ℕ} {base : ℕ} {sig : List PtsTo} {y : ℕ}
    (hy : y ∈ ptsVars (sig.map (shiftPts X base))) :
    ∃ x ∈ ptsVars sig, y = shiftVar X base x := by
  obtain ⟨pt', hpt', hy'⟩ := List.mem_flatMap.mp hy
  obtain ⟨pt, hpt, rfl⟩ := List.mem_map.mp hpt'
  rcases List.mem_append.mp hy' with h1 | h2
  · obtain ⟨x, hx, rfl⟩ := mem_exprVars_shiftExpr h1
    exact ⟨x, List.mem_flatMap.mpr ⟨pt, hpt, List.mem_append.mpr (Or.inl hx)⟩, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := mem_exprVars_shiftExpr h2
    exact ⟨x, List.mem_flatMap.mpr ⟨pt, hpt, List.mem_append.mpr (Or.inr hx)⟩, rfl⟩

private theorem mem_qVars_shiftQF {X : List ℕ} {base : ℕ} {q : QF} {y : ℕ}
    (hy : y ∈ qVars (shiftQF X base q)) :
    ∃ x ∈ qVars q, y = shiftVar X base x := by
  rcases List.mem_append.mp hy with h1 | h2
  · obtain ⟨x, hx, rfl⟩ := mem_pureVars_shift h1
    exact ⟨x, List.mem_append.mpr (Or.inl hx), rfl⟩
  · obtain ⟨x, hx, rfl⟩ := mem_ptsVars_shift h2
    exact ⟨x, List.mem_append.mpr (Or.inr hx), rfl⟩

private theorem shDen_shiftSH {base : ℕ} {H : SH} (hbase : ∀ x ∈ qVars H.2, x < base) :
    shDen (shiftSH base H) = shDen H := by
  ext ⟨s, h⟩
  simp only [shDen, shiftSH]
  constructor
  · intro hp
    obtain ⟨s₂, hs₂, hq₂⟩ := mem_foldr_exQ_of_mem hp
    let s₁ : Stack := fun x => s₂ (shiftVar H.1 base x)
    have hq₁ : (s₁, h) ∈ qfDen H.2 :=
      (qfDen_shift (s₁ := s₁) (s₂ := s₂) (fun _ _ => rfl)).mp hq₂
    refine mem_foldr_exQ_qf (s' := s₁) ?_ hq₁
    intro x hxq hxX
    have hlt : x < base := hbase x hxq
    have hnot : x ∉ H.1.map (· + base) := by
      intro hmem
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hmem
      omega
    show s₂ (shiftVar H.1 base x) = s x
    rw [shiftVar, if_neg hxX]
    exact hs₂ x hnot
  · intro hp
    obtain ⟨s₁, hs₁, hq₁⟩ := mem_foldr_exQ_of_mem hp
    let s₂ : Stack := fun y => if base ≤ y then s₁ (y - base) else s y
    have hshift : ∀ x ∈ qVars H.2, s₂ (shiftVar H.1 base x) = s₁ x := by
      intro x hxq
      have hlt : x < base := hbase x hxq
      by_cases hxX : x ∈ H.1
      · simp only [shiftVar, if_pos hxX, s₂]
        rw [if_pos (by omega), Nat.add_sub_cancel]
      · simp only [shiftVar, if_neg hxX, s₂]
        rw [if_neg (by omega), hs₁ x hxX]
    have hq₂ : (s₂, h) ∈ qfDen (shiftQF H.1 base H.2) :=
      (qfDen_shift hshift).mpr hq₁
    refine mem_foldr_exQ_qf (s' := s₂) ?_ hq₂
    intro y hyq hyX
    obtain ⟨x, hxq, rfl⟩ := mem_qVars_shiftQF hyq
    have hlt : x < base := hbase x hxq
    have hxX : x ∉ H.1 := by
      intro hx
      apply hyX
      rw [shiftVar, if_pos hx]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    simp only [shiftVar, if_neg hxX, s₂]
    exact if_neg (by omega)

private theorem le_listMax {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ listMax l := by
  unfold listMax
  induction l with
  | nil => cases hx
  | cons a rest ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact le_max_left _ _
    · exact le_trans (ih hx') (le_max_right _ _)

private theorem lt_base₁_left {H H' : SH} {x : ℕ} (hx : x ∈ shVars H) : x < base₁ H H' := by
  have hle := le_listMax (l := shVars H ++ shVars H') (List.mem_append.mpr (Or.inl hx))
  unfold base₁
  omega

private theorem lt_base₁_right {H H' : SH} {x : ℕ} (hx : x ∈ shVars H') : x < base₁ H H' := by
  have hle := le_listMax (l := shVars H ++ shVars H') (List.mem_append.mpr (Or.inr hx))
  unfold base₁
  omega

private theorem notFree_qfDen {x : ℕ} {q : QF} (hx : x ∉ qVars q) : NotFree x (qfDen q) := by
  intro s h v
  constructor
  · intro hp
    refine qfDen_congr (s := s) ?_ hp
    intro y hy
    have hne : y ≠ x := fun heq => hx (heq ▸ hy)
    exact Function.update_of_ne hne v s
  · intro hp
    refine qfDen_congr (s := Function.update s x v) ?_ hp
    intro y hy
    have hne : y ≠ x := fun heq => hx (heq ▸ hy)
    exact (Function.update_of_ne hne v s).symm

private theorem notFree_exQ {x z : ℕ} {F : Pred} (hF : NotFree x F) : NotFree x (exQ z F) := by
  intro s h v
  simp only [exQ, Set.mem_setOf_eq]
  refine exists_congr (fun w => ?_)
  by_cases hzx : z = x
  · subst hzx
    rw [Function.update_idem]
  · rw [Function.update_comm (Ne.symm hzx)]
    exact hF (Function.update s z w) h v

private theorem notFree_foldr_exQ {x : ℕ} {Y : List ℕ} {F : Pred} (hF : NotFree x F) :
    NotFree x (Y.foldr exQ F) := by
  induction Y with
  | nil => exact hF
  | cons z zs ih => exact notFree_exQ ih

private theorem subP_foldr_exQ (X : List ℕ) (F G : Pred) (hG : ∀ x ∈ X, NotFree x G) :
    subP (X.foldr exQ F) G = X.foldr exQ (subP F G) := by
  induction X with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rw [lemma_3_23.2.2.1 x (xs.foldr exQ F) G (hG x (List.mem_cons.mpr (Or.inl rfl))),
      ih (fun y hy => hG y (List.mem_cons.mpr (Or.inr hy)))]

private theorem subP_shDen_tr_eq_false (F : Pred) (Y : List ℕ) (pi' : List PureAtom)
    (sig' : List PtsTo) (tr' : Bool) :
    subP F (shDen (Y, (pi', sig', tr'))) = subP F (shDen (Y, (pi', sig', false))) := by
  cases tr' with
  | false => rfl
  | true =>
    ext ⟨s, h⟩
    simp only [mem_subP_iff_no_proper, shDen]
    refine and_congr Iff.rfl (not_congr ?_)
    constructor
    · rintro ⟨h', hsub, hne, hp⟩
      obtain ⟨s', hs', hpur, hspat⟩ := mem_foldr_exQ_of_mem hp
      obtain ⟨h'', hsub'', hspat''⟩ := spatialDen_exists_sub_false hspat
      have hsub_full : Heap.Subheap h'' h := subheap_trans hsub'' hsub
      have hne'' : h'' ≠ h := by
        intro heq
        subst heq
        exact hne (subheap_antisymm hsub hsub'')
      refine ⟨h'', hsub_full, hne'', mem_foldr_exQ_of_stack hs' ⟨hpur, hspat''⟩⟩
    · rintro ⟨h', hsub, hne, hp⟩
      obtain ⟨s', hs', hpur, hspat⟩ := mem_foldr_exQ_of_mem hp
      exact ⟨h', hsub, hne,
        mem_foldr_exQ_of_stack hs' ⟨hpur, spatialDen_false_sub_true sig' hspat⟩⟩

/-! ## Characterization of `injMaps`, `activeMaps`, `matchAtoms`, and `negChoices` -/

private theorem mem_extendInjMaps_iff {n : ℕ} {acc : List (List ℕ)} {l : List ℕ} :
    l ∈ extendInjMaps n acc ↔ ∃ t ∈ acc, ∃ j < n, j ∉ t ∧ l = j :: t := by
  unfold extendInjMaps
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨t, ht, j, hj, hif⟩
    by_cases hmem : j ∈ t
    · simp [hmem] at hif
    · simp only [if_neg hmem, List.mem_singleton] at hif
      exact ⟨t, ht, j, hj, hmem, hif⟩
  · rintro ⟨t, ht, j, hj, hmem, rfl⟩
    refine ⟨t, ht, j, hj, ?_⟩
    simp [hmem]

private theorem mem_injMaps_iff (n m : ℕ) (l : List ℕ) :
    l ∈ injMaps n m ↔ l.length = m ∧ l.Nodup ∧ ∀ j ∈ l, j < n := by
  induction m generalizing l with
  | zero =>
    simp only [injMaps, Function.iterate_zero_apply, List.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨hlen, _, _⟩
      exact List.eq_nil_of_length_eq_zero hlen
  | succ m ih =>
    have hiter : injMaps n (m + 1) = extendInjMaps n (injMaps n m) :=
      Function.iterate_succ_apply' (extendInjMaps n) m [[]]
    rw [hiter, mem_extendInjMaps_iff]
    constructor
    · rintro ⟨t, ht, j, hj, hj_not_mem, rfl⟩
      obtain ⟨ht_len, ht_nodup, ht_lt⟩ := (ih t).mp ht
      refine ⟨by simp [ht_len], List.nodup_cons.mpr ⟨hj_not_mem, ht_nodup⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hj
      · exact ht_lt x hx'
    · rintro ⟨hlen, hnodup, hlt⟩
      cases l with
      | nil => simp at hlen
      | cons j t =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        obtain ⟨hj_not_mem, ht_nodup⟩ := List.nodup_cons.mp hnodup
        have hj_lt : j < n := hlt j (List.mem_cons.mpr (Or.inl rfl))
        have ht_lt : ∀ x ∈ t, x < n := fun x hx => hlt x (List.mem_cons.mpr (Or.inr hx))
        exact ⟨t, (ih t).mpr ⟨hlen, ht_nodup, ht_lt⟩, j, hj_lt, hj_not_mem, rfl⟩

private theorem pureDen_matchAtoms_iff {sig' sig : List PtsTo} {l : List ℕ} {s' : Stack} {h : Heap} :
    (s', h) ∈ pureDen (matchAtoms sig' sig l) ↔
      ∀ k : Fin sig'.length,
        evalE s' (sig'.get k).1 = evalE s' (sig.getD (l.getD k.1 0) defaultPts).1 ∧
        evalE s' (sig'.get k).2 = evalE s' (sig.getD (l.getD k.1 0) defaultPts).2 := by
  simp only [pureDen, matchAtoms, Set.mem_setOf_eq, List.mem_flatMap, List.mem_range]
  constructor
  · intro hall k
    have h1 := hall (true, (sig'.getD k.1 defaultPts).1, (sig.getD (l.getD k.1 0) defaultPts).1)
      ⟨k.1, k.isLt, by simp [matchAtomsOne]⟩
    have h2 := hall (true, (sig'.getD k.1 defaultPts).2, (sig.getD (l.getD k.1 0) defaultPts).2)
      ⟨k.1, k.isLt, by simp [matchAtomsOne]⟩
    rw [getD_eq_get sig' defaultPts k] at h1 h2
    exact ⟨by simpa [atomHolds] using h1, by simpa [atomHolds] using h2⟩
  · rintro hall a ⟨k, hk, ha⟩
    let k' : Fin sig'.length := ⟨k, hk⟩
    have hk' := hall k'
    simp only [matchAtomsOne, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rw [getD_eq_get sig' defaultPts k']
      simpa [atomHolds] using hk'.1
    · rw [getD_eq_get sig' defaultPts k']
      simpa [atomHolds] using hk'.2

private theorem evalE_pts_get_eq {sig : List PtsTo} {s s' : Stack}
    (hagree : ∀ x ∈ ptsVars sig, s' x = s x) (j : Fin sig.length) :
    evalE s' (sig.get j).1 = evalE s (sig.get j).1 ∧
      evalE s' (sig.get j).2 = evalE s (sig.get j).2 := by
  have hmem : sig.get j ∈ sig := List.get_mem sig j
  refine ⟨evalE_congr (fun x hx => hagree x
      (List.mem_flatMap.mpr ⟨sig.get j, hmem, List.mem_append.mpr (Or.inl hx)⟩)),
    evalE_congr (fun x hx => hagree x
      (List.mem_flatMap.mpr ⟨sig.get j, hmem, List.mem_append.mpr (Or.inr hx)⟩))⟩

private theorem proper_subheap_iff_activeMaps {sig' sig : List PtsTo} {s s' : Stack} {h : Heap}
    (hspat : (s, h) ∈ spatialDen sig false)
    (hagree : ∀ x ∈ ptsVars sig, s' x = s x) :
    (∃ h' : Heap, Heap.Subheap h' h ∧ h' ≠ h ∧ (s', h') ∈ spatialDen sig' false) ↔
      ∃ l ∈ activeMaps sig' sig, (s', h) ∈ pureDen (matchAtoms sig' sig l) := by
  constructor
  · rintro ⟨h', hsub, hne, hspat'⟩
    have hex : ∀ k : Fin sig'.length, ∃ j : Fin sig.length,
        evalE s' (sig'.get k).1 = evalE s (sig.get j).1 ∧
        evalE s' (sig'.get k).2 = evalE s (sig.get j).2 := by
      intro k
      have hc := hsub _ _ (spatialDen_cell hspat' k)
      exact spatialDen_dom sig hspat hc
    choose f hf1 hf2 using hex
    have hfinj : Function.Injective f := by
      intro k₁ k₂ hfk
      apply spatialDen_inj hspat' k₁ k₂
      rw [hf1 k₁, hf1 k₂, hfk]
    have hle : sig'.length ≤ sig.length := by
      simpa using Fintype.card_le_of_injective f hfinj
    have hlt : sig'.length < sig.length := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      apply hne
      apply subheap_antisymm hsub
      have hbij : Function.Bijective f :=
        (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, by simp [heq]⟩
      intro loc val hcell
      obtain ⟨j, rfl, rfl⟩ := spatialDen_dom sig hspat hcell
      obtain ⟨k, rfl⟩ := hbij.2 j
      rw [← hf1 k, ← hf2 k]
      exact spatialDen_cell hspat' k
    let l : List ℕ := List.ofFn (fun k : Fin sig'.length => (f k).1)
    have hl_len : l.length = sig'.length := List.length_ofFn
    have hl_nodup : l.Nodup := by
      rw [List.nodup_ofFn]
      intro i j hij
      exact hfinj (Fin.ext hij)
    have hl_lt : ∀ x ∈ l, x < sig.length := by
      intro x hx
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
      exact (f k).isLt
    have hl_mem : l ∈ activeMaps sig' sig := by
      unfold activeMaps
      rw [if_pos hlt]
      exact (mem_injMaps_iff sig.length sig'.length l).mpr ⟨hl_len, hl_nodup, hl_lt⟩
    refine ⟨l, hl_mem, pureDen_matchAtoms_iff.mpr ?_⟩
    intro k
    have hlk : l.getD k.1 0 = (f k).1 := by
      have hk_len : k.1 < l.length := by rw [hl_len]; exact k.isLt
      rw [getD_eq_get l 0 ⟨k.1, hk_len⟩]
      simp [l]
    rw [hlk, getD_eq_get sig defaultPts (f k)]
    obtain ⟨he1, he2⟩ := evalE_pts_get_eq hagree (f k)
    rw [he1, he2]
    exact ⟨hf1 k, hf2 k⟩
  · rintro ⟨l, hl_act, hmatch⟩
    unfold activeMaps at hl_act
    split_ifs at hl_act with hlt
    · obtain ⟨hl_len, hl_nodup, hl_lt⟩ :=
        (mem_injMaps_iff sig.length sig'.length l).mp hl_act
      let f (k : Fin sig'.length) : Fin sig.length :=
        ⟨l.get (k.cast hl_len.symm), hl_lt _ (List.get_mem l (k.cast hl_len.symm))⟩
      have hfinj : Function.Injective f := by
        intro k₁ k₂ hfk
        have hget : l.get (k₁.cast hl_len.symm) = l.get (k₂.cast hl_len.symm) :=
          congrArg Fin.val hfk
        have hcast := (List.nodup_iff_injective_get.mp hl_nodup) hget
        exact Fin.ext (by simpa using congrArg Fin.val hcast)
      have hmatch' := pureDen_matchAtoms_iff.mp hmatch
      have hf_eq : ∀ k : Fin sig'.length,
          evalE s' (sig'.get k).1 = evalE s (sig.get (f k)).1 ∧
          evalE s' (sig'.get k).2 = evalE s (sig.get (f k)).2 := by
        intro k
        have hk := hmatch' k
        have hlk : l.getD k.1 0 = (f k).1 := getD_eq_get l 0 (k.cast hl_len.symm)
        rw [hlk, getD_eq_get sig defaultPts (f k)] at hk
        obtain ⟨he1, he2⟩ := evalE_pts_get_eq hagree (f k)
        rw [he1, he2] at hk
        exact hk
      have hne0 : ∀ k : Fin sig'.length, evalE s' (sig'.get k).1 ≠ 0 := by
        intro k h0
        rw [(hf_eq k).1] at h0
        have hc := spatialDen_cell hspat (f k)
        rw [h0, h.nil_unalloc] at hc
        cases hc
      have hinj' : ∀ i j : Fin sig'.length, i ≠ j →
          evalE s' (sig'.get i).1 ≠ evalE s' (sig'.get j).1 := by
        intro i j hij heq
        rw [(hf_eq i).1, (hf_eq j).1] at heq
        exact hij (hfinj (spatialDen_inj hspat (f i) (f j) heq))
      have hspat' := mkHeap_spec s' sig' hne0 hinj'
      have hsub : Heap.Subheap (mkHeap s' sig') h := by
        intro loc val hcell
        obtain ⟨k, rfl, rfl⟩ := spatialDen_dom sig' hspat' hcell
        rw [(hf_eq k).1, (hf_eq k).2]
        exact spatialDen_cell hspat (f k)
      have hne : mkHeap s' sig' ≠ h := by
        intro heq
        have hsurj : Function.Surjective f := by
          intro j
          have hc : (mkHeap s' sig').cell (evalE s (sig.get j).1) =
              some (evalE s (sig.get j).2) := by
            rw [heq]
            exact spatialDen_cell hspat j
          obtain ⟨k, hk1, _⟩ := spatialDen_dom sig' hspat' hc
          rw [(hf_eq k).1] at hk1
          exact ⟨k, spatialDen_inj hspat (f k) j hk1.symm⟩
        have hcard := Fintype.card_le_of_surjective f hsurj
        simp only [Fintype.card_fin] at hcard
        omega
      exact ⟨mkHeap s' sig', hsub, hne, hspat'⟩
    · simp at hl_act

/-! ## Quantifier elimination on lists and `negChoices` -/

private theorem pureDen_elimList {qe : ℕ → List PureAtom → List PureAtom}
    (hqe_spec : ∀ (X : ℕ) (pi : List PureAtom),
      X ∉ pureVars (qe X pi) ∧ exQ X (pureDen pi) = pureDen (qe X pi))
    (Y : List ℕ) (pi : List PureAtom) :
    Y.foldr exQ (pureDen pi) = pureDen (elimList qe Y pi) := by
  unfold elimList
  induction Y with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldr_cons]
    rw [ih, (hqe_spec y (ys.foldr qe pi)).2]

private theorem atomHolds_negAtom (s : Stack) (a : PureAtom) :
    atomHolds s (negAtom a) ↔ ¬ atomHolds s a := by
  rcases a with ⟨f, e, e'⟩
  cases f <;> simp [atomHolds, negAtom]

private theorem exists_mem_negChoices_iff (L : List (List PureAtom)) (s : Stack) (h : Heap) :
    (∃ extra ∈ negChoices L, (s, h) ∈ pureDen extra) ↔
      ∀ as ∈ L, (s, h) ∉ pureDen as := by
  unfold negChoices
  induction L with
  | nil =>
    simp [pureDen]
  | cons as rest ih =>
    simp only [List.foldr_cons, negChoicesStep, List.mem_flatMap, List.mem_map,
      List.forall_mem_cons]
    constructor
    · rintro ⟨_, ⟨a, ha, c, hc, rfl⟩, hpur⟩
      have ha' : atomHolds s (negAtom a) := hpur (negAtom a) (List.mem_cons.mpr (Or.inl rfl))
      have hc' : (s, h) ∈ pureDen c :=
        fun b hb => hpur b (List.mem_cons.mpr (Or.inr hb))
      refine ⟨fun hall => (atomHolds_negAtom s a).mp ha' (hall a ha),
        ih.mp ⟨c, hc, hc'⟩⟩
    · rintro ⟨hnot_as, hrest⟩
      simp only [pureDen, Set.mem_setOf_eq, not_forall] at hnot_as
      obtain ⟨a, ha, hna⟩ := hnot_as
      obtain ⟨c, hc, hc_pur⟩ := ih.mpr hrest
      refine ⟨negAtom a :: c, ⟨a, ha, c, hc, rfl⟩, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact (atomHolds_negAtom s a).mpr hna
      · exact hc_pur b hb'

private theorem mem_foldr_exQ_disj (X : List ℕ) (S : List (List PureAtom))
    (pi : List PureAtom) (sig : List PtsTo) (p : State) :
    (∃ extra ∈ S, p ∈ X.foldr exQ (qfDen (extra ++ pi, sig, false))) ↔
      p ∈ X.foldr exQ {q | ∃ extra ∈ S, q ∈ qfDen (extra ++ pi, sig, false)} := by
  induction X generalizing p with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldr_cons, exQ, Set.mem_setOf_eq]
    constructor
    · rintro ⟨extra, hextra, v, hv⟩
      exact ⟨v, (ih (Function.update p.1 x v, p.2)).mp ⟨extra, hextra, hv⟩⟩
    · rintro ⟨v, hv⟩
      obtain ⟨extra, hextra, hv'⟩ := (ih (Function.update p.1 x v, p.2)).mpr hv
      exact ⟨extra, hextra, v, hv'⟩

/-! ## Semantic correctness of `subSH` and `minDisj` -/

private theorem subSH_spec {qe : ℕ → List PureAtom → List PureAtom}
    (hqe_spec : ∀ (X : ℕ) (pi : List PureAtom),
      X ∉ pureVars (qe X pi) ∧ exQ X (pureDen pi) = pureDen (qe X pi))
    (H H' : SH) (hH : H.2.2.2 = false) :
    disjDen (subSH qe H H') = subP (shDen H) (shDen H') := by
  let b1 := base₁ H H'
  let b2 := base₂ H H'
  have hb2_eq : b2 = 2 * b1 := rfl
  let H₁ := shiftSH b1 H
  let H'₁ := shiftSH b2 H'
  have hb1_H : ∀ x ∈ qVars H.2, x < b1 :=
    fun x hx => lt_base₁_left (List.mem_append.mpr (Or.inr hx))
  have hb2_H' : ∀ x ∈ qVars H'.2, x < b2 := by
    intro x hx
    have hlt1 : x < b1 := lt_base₁_right (List.mem_append.mpr (Or.inr hx))
    show x < 2 * b1
    omega
  have hshH₁ : shDen H₁ = shDen H := shDen_shiftSH hb1_H
  have hshH'₁ : shDen H'₁ = shDen H' := shDen_shiftSH hb2_H'
  have hH₁_bounds : ∀ x' ∈ H₁.1, b1 ≤ x' ∧ x' < b2 := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hx'
    have hlt : x < b1 := lt_base₁_left (List.mem_append.mpr (Or.inl hx))
    show b1 ≤ x + b1 ∧ x + b1 < 2 * b1
    omega
  have hH₁_qVars : ∀ z ∈ qVars H₁.2, z < b2 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_qVars_shiftQF hz
    have hlt : x < b1 := hb1_H x hx
    by_cases hxX : x ∈ H.1
    · rw [shiftVar, if_pos hxX]
      show x + b1 < 2 * b1
      omega
    · rw [shiftVar, if_neg hxX]
      show x < 2 * b1
      omega
  have hH'₁_qVars_disj : ∀ x' ∈ H₁.1, x' ∉ qVars H'₁.2 := by
    intro x' hx' hmem
    obtain ⟨hb1, hb2⟩ := hH₁_bounds x' hx'
    obtain ⟨y, hy, heq⟩ := mem_qVars_shiftQF hmem
    have hlt : y < b1 := lt_base₁_right (List.mem_append.mpr (Or.inr hy))
    by_cases hyY : y ∈ H'.1
    · rw [shiftVar, if_pos hyY] at heq
      change x' = y + 2 * b1 at heq
      omega
    · rw [shiftVar, if_neg hyY] at heq
      omega
  have hH'₁_notFree : ∀ x' ∈ H₁.1, NotFree x' (shDen (H'₁.1, (H'₁.2.1, H'₁.2.2.1, false))) := by
    intro x' hx'
    have hq : x' ∉ qVars (H'₁.2.1, H'₁.2.2.1, false) := hH'₁_qVars_disj x' hx'
    exact notFree_foldr_exQ (notFree_qfDen hq)
  have hY₁_disj_sig₁ : ∀ x ∈ ptsVars H₁.2.2.1, x ∉ H'₁.1 := by
    intro x hx hmem
    have hlt : x < b2 := hH₁_qVars x (List.mem_append.mpr (Or.inr hx))
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hmem
    omega
  rw [← hshH₁, ← hshH'₁]
  have htr₁ : H₁.2.2.2 = false := hH
  have hH₁_eq : shDen H₁ = H₁.1.foldr exQ (qfDen (H₁.2.1, H₁.2.2.1, false)) := by
    rcases H₁ with ⟨X₁, pi₁, sig₁, tr₁⟩
    dsimp [shDen] at htr₁ ⊢
    rw [htr₁]
  have hH'₁_sub : subP (shDen H₁) (shDen H'₁) =
      subP (shDen H₁) (shDen (H'₁.1, (H'₁.2.1, H'₁.2.2.1, false))) := by
    rcases H'₁ with ⟨Y₁, pi'₁, sig'₁, tr'₁⟩
    exact subP_shDen_tr_eq_false (shDen H₁) Y₁ pi'₁ sig'₁ tr'₁
  rw [hH'₁_sub, hH₁_eq, subP_foldr_exQ H₁.1 _ _ hH'₁_notFree]
  let L := (activeMaps H'₁.2.2.1 H₁.2.2.1).map (fun l =>
    elimList qe H'₁.1 (H'₁.2.1 ++ matchAtoms H'₁.2.2.1 H₁.2.2.1 l))
  have hdisj : disjDen (subSH qe H H') =
      H₁.1.foldr exQ {q | ∃ extra ∈ negChoices L, q ∈ qfDen (extra ++ H₁.2.1, H₁.2.2.1, false)} := by
    ext p
    simp only [disjDen, subSH, subSHCore, mkSubDisj, Set.mem_setOf_eq, List.mem_map]
    calc
      (∃ K, (∃ extra ∈ negChoices L, (H₁.1, (extra ++ H₁.2.1, H₁.2.2.1, false)) = K) ∧
          p ∈ shDen K)
        ↔ ∃ extra ∈ negChoices L,
            p ∈ H₁.1.foldr exQ (qfDen (extra ++ H₁.2.1, H₁.2.2.1, false)) := by
          constructor
          · rintro ⟨_, ⟨extra, hextra, rfl⟩, hp⟩
            exact ⟨extra, hextra, hp⟩
          · rintro ⟨extra, hextra, hp⟩
            exact ⟨_, ⟨extra, hextra, rfl⟩, hp⟩
      _ ↔ p ∈ H₁.1.foldr exQ
            {q | ∃ extra ∈ negChoices L, q ∈ qfDen (extra ++ H₁.2.1, H₁.2.2.1, false)} :=
          mem_foldr_exQ_disj H₁.1 (negChoices L) H₁.2.1 H₁.2.2.1 p
  rw [hdisj]
  congr 1
  ext ⟨s, h⟩
  simp only [Set.mem_setOf_eq, mem_subP_iff_no_proper]
  have hqf_split : (∃ extra ∈ negChoices L, (s, h) ∈ qfDen (extra ++ H₁.2.1, H₁.2.2.1, false)) ↔
      (s, h) ∈ qfDen (H₁.2.1, H₁.2.2.1, false) ∧
        (∃ extra ∈ negChoices L, (s, h) ∈ pureDen extra) := by
    constructor
    · rintro ⟨extra, hextra, hpur, hspat⟩
      refine ⟨⟨fun a ha => hpur a (List.mem_append.mpr (Or.inr ha)), hspat⟩,
        ⟨extra, hextra, fun a ha => hpur a (List.mem_append.mpr (Or.inl ha))⟩⟩
    · rintro ⟨⟨hpur₁, hspat⟩, ⟨extra, hextra, hpur_ex⟩⟩
      refine ⟨extra, hextra, ?_, hspat⟩
      intro a ha
      rcases List.mem_append.mp ha with ha1 | ha2
      · exact hpur_ex a ha1
      · exact hpur₁ a ha2
  rw [hqf_split, exists_mem_negChoices_iff]
  refine and_congr_right (fun hqf => ?_)
  obtain ⟨_, hspat₁⟩ := hqf
  simp only [L, List.forall_mem_map, ← pureDen_elimList hqe_spec]
  have hnot_ex : (∀ l ∈ activeMaps H'₁.2.2.1 H₁.2.2.1,
      (s, h) ∉ H'₁.1.foldr exQ (pureDen (H'₁.2.1 ++ matchAtoms H'₁.2.2.1 H₁.2.2.1 l))) ↔
      ¬ (∃ l ∈ activeMaps H'₁.2.2.1 H₁.2.2.1,
        (s, h) ∈ H'₁.1.foldr exQ (pureDen (H'₁.2.1 ++ matchAtoms H'₁.2.2.1 H₁.2.2.1 l))) := by
    simp
  rw [hnot_ex]
  refine not_congr ?_
  constructor
  · rintro ⟨l, hl_act, hmem_ex⟩
    obtain ⟨s', hs', hpur_all⟩ := mem_foldr_exQ_of_mem hmem_ex
    have hpur' : (s', h) ∈ pureDen H'₁.2.1 :=
      fun a ha => hpur_all a (List.mem_append.mpr (Or.inl ha))
    have hmatch : (s', h) ∈ pureDen (matchAtoms H'₁.2.2.1 H₁.2.2.1 l) :=
      fun a ha => hpur_all a (List.mem_append.mpr (Or.inr ha))
    have hagree : ∀ x ∈ ptsVars H₁.2.2.1, s' x = s x :=
      fun x hx => hs' x (hY₁_disj_sig₁ x hx)
    obtain ⟨h', hsub, hne, hspat'⟩ :=
      (proper_subheap_iff_activeMaps hspat₁ hagree).mpr ⟨l, hl_act, hmatch⟩
    exact ⟨h', hsub, hne, mem_foldr_exQ_of_stack hs' ⟨hpur', hspat'⟩⟩
  · rintro ⟨h', hsub, hne, hp'⟩
    obtain ⟨s', hs', hpur', hspat'⟩ := mem_foldr_exQ_of_mem hp'
    have hagree : ∀ x ∈ ptsVars H₁.2.2.1, s' x = s x :=
      fun x hx => hs' x (hY₁_disj_sig₁ x hx)
    obtain ⟨l, hl_act, hmatch⟩ :=
      (proper_subheap_iff_activeMaps hspat₁ hagree).mp ⟨h', hsub, hne, hspat'⟩
    refine ⟨l, hl_act, ?_⟩
    refine mem_foldr_exQ_of_stack hs' ?_
    intro a ha
    rcases List.mem_append.mp ha with ha1 | ha2
    · exact hpur' a ha1
    · exact hmatch a ha2

private theorem subSH_false (qe : ℕ → List PureAtom → List PureAtom) (H H' : SH) :
    ∀ J ∈ subSH qe H H', J.2.2.2 = false := by
  intro J hJ
  simp only [subSH, subSHCore, mkSubDisj, List.mem_map] at hJ
  rcases hJ with ⟨_, _, rfl⟩
  rfl

private theorem subDisjBySH_false (qe : ℕ → List PureAtom → List PureAtom) (acc : Disj) (H' : SH) :
    ∀ J ∈ subDisjBySH qe acc H', J.2.2.2 = false := by
  intro J hJ
  obtain ⟨K, _, hJK⟩ := List.mem_flatMap.mp hJ
  exact subSH_false qe K H' J hJK

private theorem disjDen_subDisjBySH {qe : ℕ → List PureAtom → List PureAtom}
    (hqe_spec : ∀ (X : ℕ) (pi : List PureAtom),
      X ∉ pureVars (qe X pi) ∧ exQ X (pureDen pi) = pureDen (qe X pi))
    {acc : Disj} (hacc : ∀ K ∈ acc, K.2.2.2 = false) (H' : SH) :
    disjDen (subDisjBySH qe acc H') = subP (disjDen acc) (shDen H') := by
  ext p
  simp only [disjDen, subDisjBySH, subP, Set.mem_setOf_eq, Set.mem_inter_iff, List.mem_flatMap]
  constructor
  · rintro ⟨J, ⟨K, hK, hJK⟩, hpJ⟩
    have hp_sub : p ∈ subP (shDen K) (shDen H') := by
      rw [← subSH_spec hqe_spec K H' (hacc K hK)]
      exact ⟨J, hJK, hpJ⟩
    exact ⟨⟨K, hK, hp_sub.1⟩, hp_sub.2⟩
  · rintro ⟨⟨K, hK, hpK⟩, hno⟩
    have hp_sub : p ∈ disjDen (subSH qe K H') := by
      rw [subSH_spec hqe_spec K H' (hacc K hK)]
      exact ⟨hpK, hno⟩
    obtain ⟨J, hJK, hpJ⟩ := hp_sub
    exact ⟨J, ⟨K, hK, hJK⟩, hpJ⟩

private theorem disjDen_foldl_subDisjBySH {qe : ℕ → List PureAtom → List PureAtom}
    (hqe_spec : ∀ (X : ℕ) (pi : List PureAtom),
      X ∉ pureVars (qe X pi) ∧ exQ X (pureDen pi) = pureDen (qe X pi))
    (Gs : List SH) :
    ∀ {acc : Disj}, (∀ K ∈ acc, K.2.2.2 = false) →
      disjDen (Gs.foldl (subDisjBySH qe) acc) = (Gs.map shDen).foldl subP (disjDen acc) := by
  induction Gs with
  | nil =>
    intro acc _
    rfl
  | cons G rest ih =>
    intro acc hacc
    simp only [List.foldl_cons, List.map_cons]
    rw [ih (subDisjBySH_false qe acc G), disjDen_subDisjBySH hqe_spec hacc G]

private theorem disjDen_singleton (K : SH) : disjDen [K] = shDen K := by
  ext p
  simp [disjDen]

private theorem disjDen_eq_iUnion_map (D : Disj) :
    disjDen D = ⋃ i : Fin (D.map shDen).length, (D.map shDen).get i := by
  ext p
  simp only [disjDen, Set.mem_setOf_eq, Set.mem_iUnion, List.get_eq_getElem, List.getElem_map]
  constructor
  · rintro ⟨K, hK, hpK⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hK
    exact ⟨⟨i.1, by simp [i.isLt]⟩, hpK⟩
  · rintro ⟨⟨i, hi⟩, hp⟩
    have hi' : i < D.length := by simpa using hi
    exact ⟨D[i], List.getElem_mem hi', hp⟩

private theorem disjDen_minDisj {qe : ℕ → List PureAtom → List PureAtom}
    (hqe_spec : ∀ (X : ℕ) (pi : List PureAtom),
      X ∉ pureVars (qe X pi) ∧ exQ X (pureDen pi) = pureDen (qe X pi))
    {D₁ : Disj} (hD₁ : ∀ K ∈ D₁, K.2.2.2 = false) :
    disjDen (minDisj qe D₁) = minSet (disjDen D₁) := by
  rw [disjDen_eq_iUnion_map D₁, lemma_3_23.2.2.2.2.2 (D₁.map shDen)]
  ext p
  simp only [disjDen, minDisj, Set.mem_setOf_eq, List.mem_flatMap, Set.mem_iUnion,
    List.get_eq_getElem, List.getElem_map]
  constructor
  · rintro ⟨J, ⟨K, hK, hJK⟩, hpJ⟩
    have hK_false : ∀ M ∈ ([K] : Disj), M.2.2.2 = false := by
      intro M hM
      rw [List.mem_singleton.mp hM]
      exact hD₁ K hK
    have hp_fold : p ∈ (D₁.map shDen).foldl subP (shDen K) := by
      rw [← disjDen_singleton K, ← disjDen_foldl_subDisjBySH hqe_spec D₁ hK_false]
      exact ⟨J, hJK, hpJ⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hK
    exact ⟨⟨i.1, by simp [i.isLt]⟩, hp_fold⟩
  · rintro ⟨⟨i, hi⟩, hp_fold⟩
    have hi' : i < D₁.length := by simpa using hi
    let K := D₁[i]
    have hK : K ∈ D₁ := List.getElem_mem hi'
    have hK_false : ∀ M ∈ ([K] : Disj), M.2.2.2 = false := by
      intro M hM
      rw [List.mem_singleton.mp hM]
      exact hD₁ K hK
    have hp_disj : p ∈ disjDen (subSHByList qe K D₁) := by
      unfold subSHByList
      rw [disjDen_foldl_subDisjBySH hqe_spec D₁ hK_false, disjDen_singleton K]
      exact hp_fold
    obtain ⟨J, hJK, hpJ⟩ := hp_disj
    exact ⟨J, ⟨K, hK, hJK⟩, hpJ⟩

/-! ## `stripTrue` and `minSet` invariance -/

private theorem shDen_stripTrue_sub (K : SH) : shDen (stripTrue K) ⊆ shDen K := by
  intro ⟨s, h⟩ hp
  obtain ⟨s', hs', hpur, hspat⟩ := mem_foldr_exQ_of_mem hp
  rcases K with ⟨X, pi, sig, tr⟩
  cases tr with
  | false => exact mem_foldr_exQ_of_stack hs' ⟨hpur, hspat⟩
  | true => exact mem_foldr_exQ_of_stack hs' ⟨hpur, spatialDen_false_sub_true sig hspat⟩

private theorem shDen_exists_sub_stripTrue {K : SH} {s : Stack} {h : Heap}
    (hp : (s, h) ∈ shDen K) :
    ∃ h' : Heap, Heap.Subheap h' h ∧ (s, h') ∈ shDen (stripTrue K) := by
  obtain ⟨s', hs', hpur, hspat⟩ := mem_foldr_exQ_of_mem hp
  obtain ⟨h', hsub, hspat'⟩ := spatialDen_exists_sub_false hspat
  exact ⟨h', hsub, mem_foldr_exQ_of_stack hs' ⟨hpur, hspat'⟩⟩

private theorem minSet_eq_of_sub_and_exists_sub {A B : Pred}
    (hAB : A ⊆ B)
    (hex : ∀ p ∈ B, ∃ h' : Heap, Heap.Subheap h' p.2 ∧ (p.1, h') ∈ A) :
    minSet A = minSet B := by
  ext ⟨s, h⟩
  simp only [minSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hpA, hminA⟩
    refine ⟨hAB hpA, ?_⟩
    intro h' hsub hpB'
    obtain ⟨h'', hsub'', hpA''⟩ := hex (s, h') hpB'
    have h_eq : h'' = h := hminA h'' (subheap_trans hsub'' hsub) hpA''
    subst h_eq
    exact subheap_antisymm hsub hsub''
  · rintro ⟨hpB, hminB⟩
    obtain ⟨h', hsub, hpA'⟩ := hex (s, h) hpB
    have h_eq : h' = h := hminB h' hsub (hAB hpA')
    subst h_eq
    refine ⟨hpA', ?_⟩
    intro h'' hsub'' hpA''
    exact hminB h'' hsub'' (hAB hpA'')

private theorem minSet_disjDen_map_stripTrue (D : Disj) :
    minSet (disjDen (D.map stripTrue)) = minSet (disjDen D) := by
  apply minSet_eq_of_sub_and_exists_sub
  · rintro p ⟨_, hmem, hp⟩
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hmem
    exact ⟨K, hK, shDen_stripTrue_sub K hp⟩
  · rintro ⟨s, h⟩ ⟨K, hK, hpK⟩
    obtain ⟨h', hsub, hp'⟩ := shDen_exists_sub_stripTrue hpK
    exact ⟨h', hsub, stripTrue K, List.mem_map.mpr ⟨K, hK, rfl⟩, hp'⟩

private theorem disjDen_append (D₁ D₂ : Disj) :
    disjDen (D₁ ++ D₂) = disjDen D₁ ∪ disjDen D₂ := by
  ext p
  simp only [disjDen, Set.mem_setOf_eq, Set.mem_union, List.mem_append]
  constructor
  · rintro ⟨K, h1 | h2, hp⟩
    · exact Or.inl ⟨K, h1, hp⟩
    · exact Or.inr ⟨K, h2, hp⟩
  · rintro (⟨K, h1, hp⟩ | ⟨K, h2, hp⟩)
    · exact ⟨K, Or.inl h1, hp⟩
    · exact ⟨K, Or.inr h2, hp⟩

/-! ## Soundness of `solveAbduction` -/

private theorem solveAbduction_spec {qe : ℕ → List PureAtom → List PureAtom}
    {search : LHS → SH → Disj}
    (hqe_spec : ∀ (X : ℕ) (pi : List PureAtom),
      X ∉ pureVars (qe X pi) ∧ exQ X (pureDen pi) = pureDen (qe X pi))
    (hsearch_spec : ∀ (Δ : LHS) (H : SH), Derives Δ (search Δ H) H)
    (Δ : LHS) (H : SH) :
    IsLeastSolution (lhsDen Δ) (shDen H) (disjDen (solveAbduction qe search Δ H)) := by
  let b0 := convBase Δ H
  let H₀ := shiftSH b0 H
  have hb0_H : ∀ x ∈ qVars H.2, x < b0 := by
    intro x hx
    have hmem : x ∈ lhsVars Δ ++ shVars H :=
      List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hx)))
    have hle := le_listMax hmem
    unfold b0 convBase
    omega
  have hshH₀ : shDen H₀ = shDen H := shDen_shiftSH hb0_H
  have hconv : Conv Δ H₀ := by
    intro x' hx' hmemΔ
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hx'
    have hle := le_listMax (l := lhsVars Δ ++ shVars H) (List.mem_append.mpr (Or.inl hmemΔ))
    unfold b0 convBase at *
    omega
  let D₀ := search Δ H₀
  have hder : Derives Δ D₀ H₀ := hsearch_spec Δ H₀
  have hsol : IsSolution (lhsDen Δ) (shDen H) (disjDen D₀) := by
    rw [← hshH₀]
    exact BiAbduction.Systematic.derives_sound Δ D₀ H₀ hconv hder
  have hcompat : IsCompatMinSolution (lhsDen Δ) (shDen H) (disjDen D₀) := by
    refine ⟨hsol, ?_⟩
    intro F hF
    rw [← hshH₀] at hF
    exact BiAbduction.Systematic.lemma_3_19 Δ D₀ H₀ hconv hder F hF
  have hleast := BiAbduction.Systematic.lemma_3_16 (lhsDen Δ) (shDen H) (disjDen D₀) hcompat
  rw [← BiAbduction.Systematic.lemma_3_20 Δ, ← disjDen_append] at hleast
  let D₁ := (D₀ ++ incompat Δ).map stripTrue
  have hD₁_false : ∀ K ∈ D₁, K.2.2.2 = false := by
    intro K hK
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hK
    rfl
  have heq : disjDen (solveAbduction qe search Δ H) = minSet (disjDen (D₀ ++ incompat Δ)) := by
    show disjDen (minDisj qe D₁) = minSet (disjDen (D₀ ++ incompat Δ))
    rw [disjDen_minDisj hqe_spec hD₁_false, minSet_disjDen_map_stripTrue]
  rwa [heq]

end SolBiAbductionTheorem325

open SolBiAbductionTheorem325

theorem solution :
    ∃ f : LHS → SH → Disj, Computable₂ f ∧
      ∀ (Δ : LHS) (H : SH), IsLeastSolution (lhsDen Δ) (shDen H) (disjDen (f Δ H)) := by
  obtain ⟨qe, hqe_comp, hqe_spec⟩ := BiAbduction.Systematic.pure_qe
  obtain ⟨search, hsearch_comp, hsearch_spec⟩ := BiAbduction.Systematic.lemma_3_18
  exact ⟨solveAbduction qe search,
    computable_solveAbduction hqe_comp hsearch_comp,
    solveAbduction_spec hqe_spec hsearch_spec⟩
