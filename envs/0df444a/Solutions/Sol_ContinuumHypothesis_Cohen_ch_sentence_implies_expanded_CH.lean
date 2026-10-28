-- Prove2me | solution 1 for ContinuumHypothesis.Cohen.ch_sentence_implies_expanded_CH
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-27T00:21:11.217898+00:00
-- url     : https://prove2.me/submissions/f56d4776-3cb0-4625-9e38-ac7013fb4a3a

import Definitions.Def_CH_Cohen_Reduct
import Mathlib.ModelTheory.Definability

/-!
The mission's CH sentence implies Flypitch's expanded CH sentence.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

Reused native syntax, axioms, and semantic proof patterns:
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the original LICENSE.
Authors: Jesse Han, Floris van Doorn.
Lean 4 port: Ian Klatzco, Claude.

The additional internal graph, cardinal-comparison and omega arguments
connect the exact two first-order sentences.
Reference: Han and van Doorn, CPP 2020, section 2.2 and Figure 1.
https://florisvandoorn.com/papers/flypitch-cpp-2020.pdf
-/

set_option Elab.async false

-- Development module: CohenTransferSyntax
section

/-!
Membership-language transfer from the Flypitch presentation of ZFC.

The native syntax and axioms are due to Jesse Han and Floris van Doorn;
the reused Lean 4 port is due to Ian Klatzco, with Claude.
This file supplies the additional conservative-language transfer.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/

set_option autoImplicit true
set_option maxRecDepth 4000
set_option maxHeartbeats 200000

open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis.Cohen.CHFoundation

open Fol

universe u

def vecOfFn {A : Type u} : {n : ℕ} → (Fin n → A) → DVec A n
  | 0, _ => .nil
  | n + 1, f => .cons (f 0) (vecOfFn (fun i => f i.succ))

@[simp] theorem nth_vecOfFn {A : Type u} {n : ℕ} (f : Fin n → A) (i : Fin n) :
    (vecOfFn f).nth i.val i.isLt = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih (fun j => f j.succ) j

def termVar {α : Type u} : setLang.Term α → α
  | .var a => a
  | .func f _ => Empty.elim f

@[simp] theorem termVar_realize {A : Type*} [setLang.Structure A]
    {α : Type u} (t : setLang.Term α) (v : α → A) :
    t.realize v = v (termVar t) := by
  cases t with
  | var a => rfl
  | func f ts => exact Empty.elim f

def bindMap {n m : ℕ} (ρ : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.lastCases 0 (fun i => (ρ i).succ)

def translate {α : Type u} : {n : ℕ} → setLang.BoundedFormula α n →
    {m : ℕ} → (α → Fin m) → (Fin n → Fin m) → bounded_formula L_ZFC m
  | _, .falsum, _, _, _ => bd_falsum
  | _, .equal t s, _, ρ, τ =>
      bd_equal (bd_var (Sum.elim ρ τ (termVar t)))
        (bd_var (Sum.elim ρ τ (termVar s)))
  | _, .rel .mem ts, _, ρ, τ =>
      mem' (bd_var (Sum.elim ρ τ (termVar (ts 0))))
        (bd_var (Sum.elim ρ τ (termVar (ts 1))))
  | _, .imp φ ψ, _, ρ, τ => bd_imp (translate φ ρ τ) (translate ψ ρ τ)
  | _, .all φ, _, ρ, τ => bd_all (translate φ (fun a => (ρ a).succ) (bindMap τ))

theorem translate_realize (M : Fol.Structure L_ZFC)
    {α : Type u} {n : ℕ} (φ : setLang.BoundedFormula α n)
    {m : ℕ} (ρ : α → Fin m) (τ : Fin n → Fin m)
    (vs : DVec M.carrier m) (v : α → M.carrier) (xs : Fin n → M.carrier)
    (hv : ∀ a, vs.nth (ρ a).val (ρ a).isLt = v a)
    (hx : ∀ i, vs.nth (τ i).val (τ i).isLt = xs i) :
    letI := membershipReduct M
    Fol.realize_bounded_formula vs (translate φ ρ τ) .nil ↔ φ.Realize v xs := by
  letI := membershipReduct M
  induction φ generalizing m with
  | falsum => rfl
  | @equal n t s =>
    change (vs.nth _ _ = vs.nth _ _) ↔ _
    have ht (t : setLang.Term (α ⊕ Fin n)) :
        vs.nth (Sum.elim ρ τ (termVar t)).val (Sum.elim ρ τ (termVar t)).isLt = t.realize (Sum.elim v xs) := by
      rw [termVar_realize]
      cases termVar t with
      | inl a => exact hv a
      | inr i => exact hx i
    rw [ht, ht]
    rfl
  | @rel n k R ts =>
    cases R
    change M.rel_map ZFC_rel.ε (.cons (vs.nth _ _) (.cons (vs.nth _ _) .nil)) ↔
      M.rel_map ZFC_rel.ε (.cons _ (.cons _ .nil))
    have ht (t : setLang.Term (α ⊕ Fin n)) :
        vs.nth (Sum.elim ρ τ (termVar t)).val (Sum.elim ρ τ (termVar t)).isLt = t.realize (Sum.elim v xs) := by
      rw [termVar_realize]
      cases termVar t with
      | inl a => exact hv a
      | inr i => exact hx i
    rw [ht, ht]
  | imp φ ψ ihφ ihψ =>
    exact Iff.imp (ihφ ρ τ vs xs hv hx) (ihψ ρ τ vs xs hv hx)
  | @all n φ ih =>
    change (∀ z, Fol.realize_bounded_formula (.cons z vs)
      (translate φ (fun a => (ρ a).succ) (bindMap τ)) .nil) ↔
      ∀ z, φ.Realize v (Fin.snoc xs z)
    apply forall_congr'
    intro z
    apply ih
    · intro a; exact hv a
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [bindMap, Fin.lastCases_last, Fin.snoc_last]; rfl
      · simp only [bindMap, Fin.lastCases_castSucc, Fin.snoc_castSucc, Fin.val_succ, DVec.nth, hx]

end ContinuumHypothesis.Cohen.CHFoundation
end

-- Development module: CohenTransferDefinable
section

/-!
First-order definability with finitely many occurring parameters.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4000
set_option maxHeartbeats 400000

open FirstOrder FirstOrder.Language
namespace ContinuumHypothesis.Cohen.CHFoundation

noncomputable section
variable {A : Type*} [setLang.Structure A]

abbrev ParamFormula (A : Type*) := setLang[[A]].Formula ℕ

def PDef (P : (ℕ → A) → Prop) : Prop :=
  ∃ φ : ParamFormula A, ∀ v, φ.Realize v ↔ P v

def D1 (P : A → Prop) : Prop := PDef (fun v => P (v 0))
def D2 (R : A → A → Prop) : Prop := PDef (fun v => R (v 0) (v 1))

def namedAll {L : FirstOrder.Language} (i : ℕ) (φ : L.Formula ℕ) : L.Formula ℕ :=
  Formula.iAlls Unit (φ.relabel (fun j => if j = i then Sum.inr () else Sum.inl j))

def namedEx {L : FirstOrder.Language} (i : ℕ) (φ : L.Formula ℕ) : L.Formula ℕ :=
  Formula.iExs Unit (φ.relabel (fun j => if j = i then Sum.inr () else Sum.inl j))

theorem namedAll_realize {L : FirstOrder.Language} [L.Structure A]
    (φ : L.Formula ℕ) (i : ℕ) (v : ℕ → A) :
    (namedAll i φ).Realize v ↔ ∀ z, φ.Realize (Function.update v i z) := by
  rw [namedAll, Formula.realize_iAlls]
  simp only [Formula.realize_relabel]
  have heq (u : Unit → A) :
      (Sum.elim v u) ∘ (fun j => if j = i then Sum.inr () else Sum.inl j) =
        Function.update v i (u ()) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  simp only [heq]
  exact ⟨fun h z => h (fun _ => z), fun h u => h (u ())⟩

theorem namedEx_realize {L : FirstOrder.Language} [L.Structure A]
    (φ : L.Formula ℕ) (i : ℕ) (v : ℕ → A) :
    (namedEx i φ).Realize v ↔ ∃ z, φ.Realize (Function.update v i z) := by
  rw [namedEx, Formula.realize_iExs]
  simp only [Formula.realize_relabel]
  have heq (u : Unit → A) :
      (Sum.elim v u) ∘ (fun j => if j = i then Sum.inr () else Sum.inl j) =
        Function.update v i (u ()) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  simp only [heq]
  exact ⟨fun ⟨u, h⟩ => ⟨u (), h⟩, fun ⟨z, h⟩ => ⟨fun _ => z, h⟩⟩

theorem PDef.congr {P Q : (ℕ → A) → Prop} (hP : PDef P)
    (h : ∀ v, P v ↔ Q v) : PDef Q := by
  obtain ⟨φ, hφ⟩ := hP
  exact ⟨φ, fun v => (hφ v).trans (h v)⟩

theorem PDef.and {P Q : (ℕ → A) → Prop} (hP : PDef P) (hQ : PDef Q) :
    PDef (fun v => P v ∧ Q v) := by
  obtain ⟨φ, hφ⟩ := hP
  obtain ⟨ψ, hψ⟩ := hQ
  exact ⟨φ ⊓ ψ, fun v => by simp only [Formula.realize_inf, hφ, hψ]⟩

theorem PDef.or {P Q : (ℕ → A) → Prop} (hP : PDef P) (hQ : PDef Q) :
    PDef (fun v => P v ∨ Q v) := by
  obtain ⟨φ, hφ⟩ := hP
  obtain ⟨ψ, hψ⟩ := hQ
  exact ⟨φ ⊔ ψ, fun v => by simp only [Formula.realize_sup, hφ, hψ]⟩

theorem PDef.imp {P Q : (ℕ → A) → Prop} (hP : PDef P) (hQ : PDef Q) :
    PDef (fun v => P v → Q v) := by
  obtain ⟨φ, hφ⟩ := hP
  obtain ⟨ψ, hψ⟩ := hQ
  exact ⟨φ.imp ψ, fun v => by simp only [Formula.realize_imp, hφ, hψ]⟩

theorem PDef.not {P : (ℕ → A) → Prop} (hP : PDef P) : PDef (fun v => ¬P v) := by
  obtain ⟨φ, hφ⟩ := hP
  exact ⟨φ.not, fun v => by simp only [Formula.realize_not, hφ]⟩

theorem PDef.iff {P Q : (ℕ → A) → Prop} (hP : PDef P) (hQ : PDef Q) :
    PDef (fun v => P v ↔ Q v) := by
  exact ((hP.imp hQ).and (hQ.imp hP)).congr (fun _ => Iff.symm iff_iff_implies_and_implies)

theorem PDef.all {P : (ℕ → A) → Prop} (i : ℕ) (hP : PDef P) :
    PDef (fun v => ∀ z, P (Function.update v i z)) := by
  obtain ⟨φ, hφ⟩ := hP
  exact ⟨namedAll i φ, fun v => by simp only [namedAll_realize, hφ]⟩

theorem PDef.ex {P : (ℕ → A) → Prop} (i : ℕ) (hP : PDef P) :
    PDef (fun v => ∃ z, P (Function.update v i z)) := by
  obtain ⟨φ, hφ⟩ := hP
  exact ⟨namedEx i φ, fun v => by simp only [namedEx_realize, hφ]⟩

theorem PDef.relabel {P : (ℕ → A) → Prop} (hP : PDef P) (f : ℕ → ℕ) :
    PDef (fun v => P (v ∘ f)) := by
  obtain ⟨φ, hφ⟩ := hP
  exact ⟨φ.relabel f, fun v => by rw [Formula.realize_relabel, hφ]⟩

def pvar (i : ℕ) : setLang[[A]].Term ℕ := .var i
def pconst (a : A) : setLang[[A]].Term ℕ := (setLang.con a).term

@[simp] theorem pconst_realize (a : A) (v : ℕ → A) : (pconst a).realize v = a := rfl
@[simp] theorem pvar_realize (i : ℕ) (v : ℕ → A) : (pvar (A := A) i).realize v = v i := rfl

def DTerm (t : (ℕ → A) → A) : Prop := ∃ s : setLang[[A]].Term ℕ, ∀ v, s.realize v = t v

theorem DTerm.var (i : ℕ) : DTerm (fun v : ℕ → A => v i) := ⟨pvar i, fun _ => rfl⟩
theorem DTerm.const (a : A) : DTerm (fun _ : ℕ → A => a) := ⟨pconst a, fun _ => rfl⟩

theorem DTerm.eq {t s : (ℕ → A) → A} (ht : DTerm t) (hs : DTerm s) :
    PDef (fun v => t v = s v) := by
  obtain ⟨t', ht'⟩ := ht
  obtain ⟨s', hs'⟩ := hs
  exact ⟨t'.equal s', fun v => by simp only [Formula.realize_equal, ht', hs']⟩

def memRel (a b : A) : Prop :=
  FirstOrder.Language.Structure.RelMap (L := setLang) SetRel.mem ![a,b]

theorem DTerm.mem {t s : (ℕ → A) → A} (ht : DTerm t) (hs : DTerm s) :
    PDef (fun v => memRel (t v) (s v)) := by
  obtain ⟨t', ht'⟩ := ht
  obtain ⟨s', hs'⟩ := hs
  refine ⟨Relations.formula₂ (Sum.inl SetRel.mem : setLang[[A]].Relations 2) t' s', ?_⟩
  intro v
  simp only [Formula.realize_rel₂, ht', hs']
  rfl

theorem D1.slot {P : A → Prop} (hP : D1 P) (i : ℕ) : PDef (fun v => P (v i)) := by
  exact (hP.relabel (fun _ => i)).congr (fun _ => Iff.rfl)

theorem D2.slots {R : A → A → Prop} (hR : D2 R) (i j : ℕ) :
    PDef (fun v => R (v i) (v j)) := by
  exact (hR.relabel (fun n => if n = 0 then i else j)).congr (fun _ => by simp)

end
end ContinuumHypothesis.Cohen.CHFoundation
end

-- Development module: CohenTransferNative
section

/-!
Ordinary-model semantics of the native Flypitch ZFC axioms.
Adapted from the Boolean semantics by Jesse Han and Floris van Doorn,
Lean 4 port by Ian Klatzco, with Claude.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4000
set_option maxHeartbeats 400000

open FirstOrder FirstOrder.Language Fol

namespace ContinuumHypothesis.Cohen.CHFoundation

variable {L : Fol.Language} {S : Fol.Structure L}

lemma eval_formula_subst_zero {S : Structure L} {l} (v : ℕ → S) (f : @preformula L l)
    (s : term L) (xs : DVec S l) :
    realize_formula (subst_realize v (realize_term v s DVec.nil) 0) f xs ↔
    realize_formula v (subst_formula f s 0) xs := by
  have h := realize_formula_subst v 0 f s
  simp only [lift_term_zero] at h
  exact h xs

lemma eval_formula_insert_lift {S : Structure L} :
    ∀ {l} (v : ℕ → S) (x : S) (m : ℕ) (f : @preformula L l) (xs : DVec S l),
    realize_formula (subst_realize v x m) (lift_formula_at f 1 m) xs = realize_formula v f xs
  | _, _, _, _, preformula.falsum, _ => rfl
  | _, v, x, m, preformula.equal t₁ t₂, _ => by
      simp [realize_formula, realize_term_subst_lift]
  | _, _, _, _, preformula.rel _, _ => rfl
  | _, v, x, m, preformula.apprel f t, xs => by
      simp only [realize_formula, lift_formula_at, realize_term_subst_lift]
      exact eval_formula_insert_lift v x m f _
  | _, v, x, m, preformula.imp f₁ f₂, xs => by
      simp only [realize_formula, lift_formula_at]
      exact propext (Iff.imp
        (Iff.of_eq (eval_formula_insert_lift v x m f₁ xs))
        (Iff.of_eq (eval_formula_insert_lift v x m f₂ xs)))
  | _, v, x, m, preformula.all f, _ => by
      simp only [realize_formula, lift_formula_at]
      apply propext
      apply forall_congr'
      intro x'
      rw [propext (realize_formula_congr (fun k => subst_realize2_0 v x' x m k) (lift_formula_at f 1 (m + 1)) DVec.nil)]
      exact Iff.of_eq (eval_formula_insert_lift (subst_realize v x' 0) x (m + 1) f DVec.nil)


theorem realize_bounded_formula_eq' {n l : ℕ} (d : S.carrier)
    {v₁ : DVec S.carrier n} (f : Fol.bounded_preformula L n l) (xs : DVec S.carrier l) :
    Fol.realize_bounded_formula v₁ f xs =
      Fol.realize_formula (fun k => if h : k < n then v₁.nth k h else d) f.fst xs := by
  apply propext
  apply Fol.realize_bounded_formula_iff
  intro k hk
  simp only [dif_pos hk]

theorem realize_bounded_term_eq' {n l : ℕ} (d : S.carrier)
    {v₁ : DVec S.carrier n} (t : Fol.bounded_preterm L n l) (xs : DVec S.carrier l) :
    Fol.realize_bounded_term v₁ t xs =
      Fol.realize_term (fun k => if h : k < n then v₁.nth k h else d) t.fst xs := by
  apply Fol.realize_bounded_term_eq
  intro k hk
  simp only [dif_pos hk]

lemma realize_bounded_formula_insert_lift {n l} (v : DVec S n) (x : S) (m : ℕ) (hm : m ≤ n)
    (f : bounded_preformula L n l) (xs : DVec S l) :
    realize_bounded_formula (v.insert x m) (f ↑ᶠᵇ' 1 # m) xs =
    realize_bounded_formula v f xs := by
  -- Reduce to unbounded formula semantics
  rw [realize_bounded_formula_eq' (v₁ := v.insert x m) x,
      realize_bounded_formula_eq' (v₁ := v) x]
  simp only [lift_bounded_formula_fst]
  -- Now use eval_formula_insert_lift
  rw [show (fun k => if h : k < n + 1 then (v.insert x m).nth k h else x) =
          subst_realize (fun k => if h : k < n then v.nth k h else x) x m from by
        funext k
        simp only [subst_realize]
        by_cases hkm : k < m
        · simp only [hkm, if_true]
          have hkn : k < n := Nat.lt_of_lt_of_le hkm hm
          have hkn1 : k < n + 1 := Nat.lt_succ_of_le (Nat.le_of_lt hkn)
          simp only [dif_pos hkn1, dif_pos hkn]
          simp [DVec.insert_nth_lt x v (by exact hkn) hkn1 (by exact hkm)]
        · by_cases hkm' : k = m
          · subst hkm'
            simp [hkm, DVec.insert_nth]
          · have hkm2 : m < k := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hkm) (Ne.symm hkm')
            simp only [Nat.lt_asymm hkm2, hkm2, if_false, if_true]
            by_cases hkn1 : k < n + 1
            · have hk1 : k - 1 < n := by omega
              simp only [dif_pos hkn1, dif_pos hk1]
              rw [DVec.insert_nth_gt_simp x v hkn1 hkm2]
            · have hk1 : ¬(k - 1 < n) := by omega
              simp only [dif_neg hkn1, dif_neg hk1] ]
  exact eval_formula_insert_lift _ _ _ _ _

/-! ## realize_formula_insert_lift2 — src/bfol.lean:874-879 -/

@[simp] lemma realize_formula_insert_lift2 {n} (v : DVec S n) (x y z : S)
    (f : bounded_formula L (n + 2)) :
    realize_bounded_formula (DVec.cons x (DVec.cons y (DVec.cons z v)))
      (f ↑ᶠᵇ' 1 # 2) DVec.nil =
    realize_bounded_formula (DVec.cons x (DVec.cons y v)) f DVec.nil := by
  -- Use realize_bounded_formula_insert_lift with m=2, v=(x::y::v), x=z
  convert realize_bounded_formula_insert_lift (DVec.cons x (DVec.cons y v)) z 2
    (by omega) f DVec.nil using 2
  rfl

/-! ## realize_subst_formula0 — src/bfol.lean:881-897 -/

lemma eval_subst0 {n} (S : Structure L) [Nonempty S]
    (f : bounded_formula L (n + 1)) (t : bounded_term L n) (v : DVec S n) :
    realize_bounded_formula v (subst0_bounded_formula f t) DVec.nil =
    realize_bounded_formula
      (DVec.cons (realize_bounded_term v t DVec.nil) v) f DVec.nil := by
  obtain ⟨y⟩ := ‹Nonempty S›
  -- Reduce both sides to formula semantics via bounded_formula_eq'
  rw [realize_bounded_formula_eq' (v₁ := v) y,
      realize_bounded_formula_eq' (v₁ := DVec.cons _ v) y]
  simp only [subst0_bounded_formula_fst]
  -- LHS: realize_formula (fun k => if h : k < n then v.nth k h else y) (f.fst[t.fst//0]) []
  -- RHS: realize_formula (fun k => if h : k < n+1 then (brt_v_t :: v).nth k h else y) f.fst []
  -- Use ← eval_formula_subst_zero on LHS:
  -- = realize_formula (subst_realize φ (brt_v φ t.fst []) 0) f.fst []
  -- where φ = (fun k => if h : k < n then v.nth k h else y)
  -- and brt_v φ t.fst [] = realize_bounded_term_eq' ... = brt v t []
  rw [← propext (eval_formula_subst_zero _ _ _ _)]
  -- Now LHS = realize_formula (subst_realize φ (brt φ t.fst []) 0) f.fst []
  -- RHS = realize_formula (fun k => if h : k < n+1 then (brt_v_t :: v).nth k h else y) f.fst []
  apply propext; apply realize_formula_congr
  intro k
  simp only [subst_realize, realize_term, DVec.nth]
  -- The bounded term realization
  rw [← realize_bounded_term_eq' y]
  by_cases hk : k < n + 1
  · simp only [dif_pos hk, DVec.nth]
    cases k with
    | zero => simp [subst_realize, realize_bounded_term]
    | succ k =>
      have h2k : k < n := Nat.lt_of_succ_lt_succ hk
      simp only [subst_realize, Nat.zero_lt_succ, if_false, Nat.lt_irrefl, if_false]
      simp [dif_pos h2k, DVec.nth]
  · simp only [dif_neg hk, subst_realize]
    have h2k : 0 < k := Nat.pos_of_ne_zero (by omega)
    have h3k : ¬(k - 1 < n) := by omega
    simp [Nat.not_lt.mp hk, h2k, h3k, dif_neg h3k]

lemma formula_lift_combine : ∀ {l} (f : @preformula L l) (n n') {m m'}, m ≤ m' → m' ≤ m + n →
    lift_formula_at (lift_formula_at f n m) n' m' = lift_formula_at f (n + n') m
  | _, preformula.falsum, _, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, n, n', m, m', H₁, H₂ => by
      simp [lift_formula_at, lift_term_at2_medium, H₁, H₂]
  | _, preformula.rel R, _, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, n, n', m, m', H₁, H₂ => by
      simp only [lift_formula_at, lift_term_at2_medium t n' H₁ H₂]
      exact congrArg₂ preformula.apprel (formula_lift_combine f n n' H₁ H₂) rfl
  | _, preformula.imp f₁ f₂, n, n', m, m', H₁, H₂ => by
      simp only [lift_formula_at]
      exact congrArg₂ preformula.imp
        (formula_lift_combine f₁ n n' H₁ H₂)
        (formula_lift_combine f₂ n n' H₁ H₂)
  | _, preformula.all f, n, n', m, m', H₁, H₂ => by
      simp only [lift_formula_at]
      exact congrArg preformula.all
        (formula_lift_combine f n n' (Nat.add_le_add_right H₁ 1)
          (by omega))


lemma lift_twice_fst {n l k : ℕ} (f : bounded_preformula L_ZFC n l) (m : ℕ) :
    (lift_bounded_formula_at f (k+2) m).fst =
      (lift_bounded_formula_at (lift_bounded_formula_at f (k+1) m) 1 m).fst := by
  simp only [lift_bounded_formula_fst]
  rw [formula_lift_combine] <;> omega

lemma realize_lift2_at2 {M : Fol.Structure L_ZFC} {n} (ϕ : bounded_formula L_ZFC (n + 2))
    (v : DVec M.carrier n) (x y z₁ z₂ : M.carrier) :
    realize_bounded_formula
      (DVec.cons x (DVec.cons y (DVec.cons z₁ (DVec.cons z₂ v)))) (ϕ ↑ᶠᵇ' 2 # 2) DVec.nil =
    realize_bounded_formula (DVec.cons x (DVec.cons y v)) ϕ DVec.nil := by
  rw [bounded_preformula.eq (lift_twice_fst ϕ (k := 0) 2)]
  rw [realize_formula_insert_lift2 (DVec.cons z₂ v) x y z₁ (ϕ ↑ᶠᵇ' 1 # 2)]
  exact realize_formula_insert_lift2 v x y z₂ ϕ

lemma realize_lift3_at2 {M : Fol.Structure L_ZFC} {n} (ϕ : bounded_formula L_ZFC (n + 2))
    (v : DVec M.carrier n) (x y z₁ z₂ z₃ : M.carrier) :
    realize_bounded_formula
      (DVec.cons x (DVec.cons y (DVec.cons z₁ (DVec.cons z₂ (DVec.cons z₃ v))))) (ϕ ↑ᶠᵇ' 3 # 2) DVec.nil =
    realize_bounded_formula (DVec.cons x (DVec.cons y v)) ϕ DVec.nil := by
  rw [bounded_preformula.eq (lift_twice_fst ϕ (k := 1) 2)]
  rw [realize_formula_insert_lift2 (DVec.cons z₂ (DVec.cons z₃ v)) x y z₁ (ϕ ↑ᶠᵇ' 2 # 2)]
  exact realize_lift2_at2 ϕ v x y z₂ z₃


def Mem (M : Fol.Structure L_ZFC) (a b : M.carrier) : Prop :=
  M.rel_map ZFC_rel.ε (.cons a (.cons b .nil))

def EmptySet (M : Fol.Structure L_ZFC) : M.carrier := M.fun_map ZFC_func.emptyset .nil
def Omega (M : Fol.Structure L_ZFC) : M.carrier := M.fun_map ZFC_func.ω .nil
def Union (M : Fol.Structure L_ZFC) (a : M.carrier) : M.carrier :=
  M.fun_map ZFC_func.Union (.cons a .nil)
def Power (M : Fol.Structure L_ZFC) (a : M.carrier) : M.carrier :=
  M.fun_map ZFC_func.P (.cons a .nil)
def Sub (M : Fol.Structure L_ZFC) (a b : M.carrier) : Prop := ∀ z, Mem M z a → Mem M z b

@[simp] theorem eval_mem {M : Fol.Structure L_ZFC} {n} (v : DVec M.carrier n)
    (a b : bounded_term L_ZFC n) :
    realize_bounded_formula (S := M) v (mem' a b) .nil ↔
      Mem M (realize_bounded_term v a .nil) (realize_bounded_term v b .nil) := Iff.rfl

@[simp] theorem eval_empty {M : Fol.Structure L_ZFC} {n} (v : DVec M.carrier n) :
    realize_bounded_term (S := M) v (emptyset' : bounded_term L_ZFC n) .nil = EmptySet M := rfl

@[simp] theorem eval_omega {M : Fol.Structure L_ZFC} {n} (v : DVec M.carrier n) :
    realize_bounded_term (S := M) v (_root_.omega' : bounded_term L_ZFC n) .nil = Omega M := rfl

@[simp] theorem eval_union {M : Fol.Structure L_ZFC} {n} (v : DVec M.carrier n)
    (a : bounded_term L_ZFC n) :
    realize_bounded_term (S := M) v (union' a) .nil = Union M (realize_bounded_term v a .nil) := rfl

@[simp] theorem eval_power {M : Fol.Structure L_ZFC} {n} (v : DVec M.carrier n)
    (a : bounded_term L_ZFC n) :
    realize_bounded_term (S := M) v (Powerset a) .nil = Power M (realize_bounded_term v a .nil) := rfl

theorem eval_lift_term_zero {n l} (v : DVec S n) (x : S)
    (t : bounded_preterm L n l) (args : DVec S l) :
    realize_bounded_term (.cons x v) (lift_bounded_term_at t 1 0) args =
      realize_bounded_term v t args := by
  induction t with
  | bd_var k =>
    simp only [lift_bounded_term_at, Nat.zero_le, ↓reduceIte, realize_bounded_term, DVec.nth]
  | bd_func f => rfl
  | bd_app t s ih ihs =>
    simp only [lift_bounded_term_at, realize_bounded_term, ihs, ih]

@[simp] theorem eval_subset {M : Fol.Structure L_ZFC} {n} (v : DVec M.carrier n)
    (a b : bounded_term L_ZFC n) :
    realize_bounded_formula (S := M) v (subset'' a b) .nil ↔
      Sub M (realize_bounded_term v a .nil) (realize_bounded_term v b .nil) := by
  simp only [subset'', realize_bounded_formula, eval_mem, eval_lift_term_zero,
    realize_bounded_term, DVec.nth, Sub]

theorem eval_or {n} (v : DVec S n) (φ ψ : bounded_formula L n) :
    realize_bounded_formula v (bd_or φ ψ) .nil ↔
      realize_bounded_formula v φ .nil ∨ realize_bounded_formula v ψ .nil := by
  simp only [bd_or, bd_not, realize_bounded_formula]
  tauto

variable (M : Fol.Structure L_ZFC) (hZFC : Fol.all_realize_sentence M _root_.ZFC)
include hZFC

theorem collection_spec {n : ℕ} (φ : bounded_formula L_ZFC (n+2))
    (ps : DVec M.carrier n) (a : M.carrier)
    (ht : ∀ x, Mem M x a → ∃ y,
      realize_bounded_formula (.cons y (.cons x ps)) φ .nil) :
    ∃ b, (∀ x, Mem M x a → ∃ y, Mem M y b ∧
      realize_bounded_formula (.cons y (.cons x ps)) φ .nil) ∧
      (∀ y, Mem M y b → ∃ x, Mem M x a ∧
      realize_bounded_formula (.cons y (.cons x ps)) φ .nil) := by
  letI : Nonempty M.carrier := ⟨EmptySet M⟩
  have h := hZFC (show axiom_of_collection φ ∈ _root_.ZFC by
    apply Set.mem_union_right
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_image_of_mem _ (Set.mem_univ φ)⟩)
  rw [axiom_of_collection, realize_sentence_bd_alls] at h
  have hh := h (.cons a ps)
  simp only [realize_bounded_formula, realize_bounded_formula_and,
    realize_bounded_formula_ex, eval_mem, realize_bounded_term, DVec.nth,
    realize_formula_insert_lift2, realize_lift2_at2, realize_lift3_at2,
    eval_subst0] at hh
  exact hh ht

theorem empty_spec : ∀ x, ¬Mem M x (EmptySet M) := by
  have h := hZFC (show axiom_of_emptyset ∈ _root_.ZFC by simp only [_root_.ZFC,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_or])
  simpa only [axiom_of_emptyset, realize_sentence, realize_bounded_formula_not,
    realize_bounded_formula, eval_mem, eval_empty, realize_bounded_term, DVec.nth] using h

theorem ext_spec (a b : M.carrier) (h : ∀ z, Mem M z a ↔ Mem M z b) : a = b := by
  have hh := hZFC (show axiom_of_extensionality ∈ _root_.ZFC by simp only [_root_.ZFC,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_or])
  have hh' : ∀ a b : M.carrier, (∀ z, Mem M z a ↔ Mem M z b) → a = b := by
    simpa only [axiom_of_extensionality, realize_sentence, realize_bounded_formula,
      realize_bounded_formula_biimp, eval_mem, realize_bounded_term, DVec.nth] using hh
  exact hh' a b h

theorem union_spec (a x : M.carrier) :
    Mem M x (Union M a) ↔ ∃ y, Mem M y a ∧ Mem M x y := by
  have h := hZFC (show axiom_of_union ∈ _root_.ZFC by simp only [_root_.ZFC,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_or])
  have hh : ∀ a x, Mem M x (Union M a) ↔ ∃ y, Mem M y a ∧ Mem M x y := by
    simpa only [axiom_of_union, realize_sentence, realize_bounded_formula,
      realize_bounded_formula_biimp, realize_bounded_formula_and, realize_bounded_formula_ex,
      eval_mem, eval_union, realize_bounded_term, DVec.nth] using h
  exact hh a x

theorem power_spec (a y : M.carrier) : Mem M y (Power M a) ↔ Sub M y a := by
  have h := hZFC (show axiom_of_powerset ∈ _root_.ZFC by simp only [_root_.ZFC,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_or])
  have hh : ∀ a y, Mem M y (Power M a) ↔ Sub M y a := by
    simpa only [axiom_of_powerset, realize_sentence, realize_bounded_formula,
      realize_bounded_formula_biimp, eval_mem, eval_power, realize_bounded_term, DVec.nth, Sub] using h
  exact hh a y

theorem regularity_spec (a : M.carrier) (ha : a ≠ EmptySet M) :
    ∃ y, Mem M y a ∧ ∀ z, Mem M z a → ¬Mem M z y := by
  have h := hZFC (show axiom_of_regularity ∈ _root_.ZFC by simp only [_root_.ZFC,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_or])
  have hh : ∀ a, a ≠ EmptySet M → ∃ y, Mem M y a ∧ ∀ z, Mem M z a → ¬Mem M z y := by
    simpa only [axiom_of_regularity, realize_sentence, realize_bounded_formula,
      realize_bounded_formula_not, realize_bounded_formula_and, realize_bounded_formula_ex,
      eval_mem, eval_empty, realize_bounded_term, DVec.nth] using h
  exact hh a ha

def NOrd (a : M.carrier) : Prop :=
  ((∀ x, Mem M x a → ∀ y, Mem M y a → (x = y ∨ Mem M x y) ∨ Mem M y x) ∧
    (∀ b, Sub M b a → b ≠ EmptySet M →
      ∃ y, Mem M y b ∧ ∀ z, Mem M z b → ¬Mem M z y)) ∧
    ∀ x, Mem M x a → Sub M x a

omit hZFC in
theorem eval_ord (a : M.carrier) :
    realize_bounded_formula (.cons a .nil) Ord_f .nil ↔ NOrd M a := by
  simp only [Ord_f, ewo_f, epsilon_trichotomy_f, epsilon_well_founded_f, is_transitive_f,
    realize_bounded_formula_and, realize_bounded_formula_not, realize_bounded_formula_ex,
    eval_or, eval_subset, realize_bounded_formula, eval_mem, eval_empty, realize_bounded_term,
    DVec.nth, NOrd]

theorem infinity_spec :
    (Mem M (EmptySet M) (Omega M) ∧
      ∀ x, Mem M x (Omega M) → ∃ y, Mem M y (Omega M) ∧ Mem M x y) ∧ NOrd M (Omega M) := by
  have h := hZFC (show axiom_of_infinity ∈ _root_.ZFC by simp only [_root_.ZFC,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_or])
  rw [axiom_of_infinity, realize_sentence_and] at h
  have hh := h.1
  have hh' : (Mem M (EmptySet M) (Omega M) ∧
      ∀ x, Mem M x (Omega M) → ∃ y, Mem M y (Omega M) ∧ Mem M x y) ∧
      ∃ a, NOrd M a ∧ Omega M = a := by
    simpa only [realize_sentence, realize_bounded_formula_and, realize_bounded_formula_ex,
      eval_mem, eval_empty, eval_omega, eval_ord, realize_bounded_formula,
      realize_bounded_term, DVec.nth] using hh
  obtain ⟨a, ha, heq⟩ := hh'.2
  exact ⟨hh'.1, heq.symm ▸ ha⟩

theorem zorn_spec (a : M.carrier) (ha : a ≠ EmptySet M)
    (hc : ∀ c, Sub M c a →
      (∀ x, Mem M x c → ∀ y, Mem M y c → Sub M x y ∨ Sub M y x) →
      Mem M (Union M c) a) :
    ∃ m, Mem M m a ∧ ∀ z, Mem M z a → Sub M m z → m = z := by
  have h := hZFC (show zorns_lemma ∈ _root_.ZFC by simp only [_root_.ZFC,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_or])
  have hh : ∀ a, a ≠ EmptySet M →
      (∀ c, (Sub M c a ∧
        ∀ x y, Mem M x c ∧ Mem M y c → Sub M x y ∨ Sub M y x) →
        Mem M (Union M c) a) →
      ∃ m, Mem M m a ∧ ∀ z, Mem M z a → Sub M m z → m = z := by
    simpa only [zorns_lemma, realize_sentence, realize_bounded_formula_not,
      realize_bounded_formula_and, realize_bounded_formula_ex, eval_or, eval_subset,
      realize_bounded_formula, eval_mem, eval_empty, eval_union, realize_bounded_term,
      DVec.nth] using h
  exact hh a ha (fun c h => hc c h.1 (fun x hx y hy => h.2 x y ⟨hx,hy⟩))

end ContinuumHypothesis.Cohen.CHFoundation
end

-- Development module: CohenTransferCollection
section

/-!
Strong Collection for membership-language definable relations.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
open FirstOrder FirstOrder.Language Fol
namespace ContinuumHypothesis.Cohen.CHFoundation
noncomputable section

variable (M : Fol.Structure L_ZFC)
local instance : setLang.Structure M.carrier := membershipReduct M

theorem native_code {R : M.carrier → M.carrier → Prop} (hR : D2 R) :
    ∃ (n : ℕ) (ps : DVec M.carrier n) (ψ : bounded_formula L_ZFC (n+2)),
      ∀ x y, realize_bounded_formula (.cons y (.cons x ps)) ψ .nil ↔ R x y := by
  classical
  obtain ⟨φ, hφ⟩ := hR
  let φ₀ : setLang.Formula (M.carrier ⊕ ℕ) := BoundedFormula.constantsVarsEquiv φ
  let s := φ₀.freeVarFinset
  let n := Fintype.card s
  let e : s ≃ Fin n := Fintype.equivFin s
  let base : M.carrier ⊕ ℕ → M.carrier := Sum.elim id (fun _ => EmptySet M)
  let ps : DVec M.carrier n := vecOfFn (fun i => base (e.symm i).val)
  let ρ : s → Fin (n+2) := fun a =>
    if a.val = Sum.inr 0 then ⟨1, by omega⟩
    else if a.val = Sum.inr 1 then ⟨0, by omega⟩
    else ⟨(e a).val + 2, by have h := (e a).isLt; omega⟩
  let ψ := translate (φ₀.restrictFreeVar id) ρ Fin.elim0
  refine ⟨n, ps, ψ, ?_⟩
  intro x y
  let v : ℕ → M.carrier := fun i => if i = 0 then x else if i = 1 then y else EmptySet M
  let w : M.carrier ⊕ ℕ → M.carrier := Sum.elim id v
  have hps (a : s) : ps.nth (e a).val (e a).isLt = base a.val := by
    change (vecOfFn (fun i => base (e.symm i).val)).nth (e a).val _ = _
    rw [nth_vecOfFn, e.symm_apply_apply]
  have hv (a : s) :
      (DVec.cons y (.cons x ps)).nth (ρ a).val (ρ a).isLt = w a.val := by
    dsimp only [ρ]
    split_ifs with h0 h1
    · simp only [DVec.nth, h0, w, Sum.elim_inr, v, ↓reduceIte]
    · simp only [DVec.nth, h1, w, Sum.elim_inr, v, Nat.one_ne_zero, ↓reduceIte]
    · change ps.nth (e a).val _ = w a.val
      rw [hps]
      cases ha : a.val with
      | inl z => rfl
      | inr i =>
        have hi0 : i ≠ 0 := fun hi => h0 (ha.trans (congrArg Sum.inr hi))
        have hi1 : i ≠ 1 := fun hi => h1 (ha.trans (congrArg Sum.inr hi))
        simp only [base, w, ha, Sum.elim_inr, v, hi0, hi1, ↓reduceIte]
  have ht := translate_realize M (φ₀.restrictFreeVar id) ρ Fin.elim0
    (.cons y (.cons x ps)) (fun a => w a.val) Fin.elim0 hv (fun i => Fin.elim0 i)
  have hr : (φ₀.restrictFreeVar id).Realize (fun a => w a.val) Fin.elim0 ↔
      BoundedFormula.Realize φ₀ w Fin.elim0 :=
    BoundedFormula.realize_restrictFreeVar w (fun _ => rfl)
  have hc : BoundedFormula.Realize φ₀ w Fin.elim0 ↔ φ.Realize v := by
    exact BoundedFormula.realize_constantsVarsEquiv
  have hf : φ.Realize v ↔ R x y := by
    simpa only [v, ↓reduceIte, Nat.one_ne_zero] using hφ v
  exact ht.trans (hr.trans (hc.trans hf))

theorem definable_collection (hZFC : Fol.all_realize_sentence M _root_.ZFC)
    {R : M.carrier → M.carrier → Prop} (hR : D2 R) (a : M.carrier)
    (ht : ∀ x, Mem M x a → ∃ y, R x y) :
    ∃ b, (∀ x, Mem M x a → ∃ y, Mem M y b ∧ R x y) ∧
      (∀ y, Mem M y b → ∃ x, Mem M x a ∧ R x y) := by
  obtain ⟨n, ps, ψ, hψ⟩ := native_code M hR
  have h := collection_spec M hZFC ψ ps a (by
    intro x hx
    obtain ⟨y, hy⟩ := ht x hx
    exact ⟨y, (hψ x y).mpr hy⟩)
  obtain ⟨b, hb₁, hb₂⟩ := h
  refine ⟨b, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hyb, hy⟩ := hb₁ x hx
    exact ⟨y, hyb, (hψ x y).mp hy⟩
  · intro y hy
    obtain ⟨x, hxa, hxy⟩ := hb₂ y hy
    exact ⟨x, hxa, (hψ x y).mp hxy⟩

end
end ContinuumHypothesis.Cohen.CHFoundation
end

-- Development module: CohenTransferSets
section

/-!
Deriving pure membership axioms from native strong Collection.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
open FirstOrder FirstOrder.Language Fol
namespace ContinuumHypothesis.Cohen.CHFoundation
noncomputable section

variable (M : Fol.Structure L_ZFC) (hZFC : Fol.all_realize_sentence M _root_.ZFC)
include hZFC
local instance : setLang.Structure M.carrier := membershipReduct M

theorem pairing_exists (a b : M.carrier) :
    ∃ c, ∀ z, Mem M z c ↔ z = a ∨ z = b := by
  have hI := (infinity_spec M hZFC).1
  obtain ⟨t, htW, hEt⟩ := hI.2 (EmptySet M) hI.1
  have htE : t ≠ EmptySet M := by
    intro h; rw [h] at hEt; exact empty_spec M hZFC _ hEt
  let R := fun x y : M.carrier =>
    (x = EmptySet M ∧ y = a) ∨ (x ≠ EmptySet M ∧ y = b)
  have hR : D2 R :=
    (((DTerm.var 0).eq (DTerm.const (EmptySet M))).and
      ((DTerm.var 1).eq (DTerm.const a))).or
      ((((DTerm.var 0).eq (DTerm.const (EmptySet M))).not).and
        ((DTerm.var 1).eq (DTerm.const b)))
  obtain ⟨c, hc₁, hc₂⟩ := definable_collection M hZFC hR (Omega M) (by
    intro x _
    by_cases hx : x = EmptySet M
    · exact ⟨a, Or.inl ⟨hx, rfl⟩⟩
    · exact ⟨b, Or.inr ⟨hx, rfl⟩⟩)
  refine ⟨c, fun z => ⟨?_, ?_⟩⟩
  · intro hz
    obtain ⟨x, _, hxy⟩ := hc₂ z hz
    exact hxy.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  · rintro (rfl | rfl)
    · obtain ⟨y, hy, hr⟩ := hc₁ (EmptySet M) hI.1
      rcases hr with h | h
      · exact h.2 ▸ hy
      · exact (h.1 rfl).elim
    · obtain ⟨y, hy, hr⟩ := hc₁ t htW
      rcases hr with h | h
      · exact (htE h.1).elim
      · exact h.2 ▸ hy

def PairSet (a b : M.carrier) : M.carrier := (pairing_exists M hZFC a b).choose

theorem pair_spec (a b z : M.carrier) :
    Mem M z (PairSet M hZFC a b) ↔ z = a ∨ z = b :=
  (pairing_exists M hZFC a b).choose_spec z

def Insert (x a : M.carrier) : M.carrier :=
  Union M (PairSet M hZFC a (PairSet M hZFC x x))

theorem insert_spec (x a z : M.carrier) :
    Mem M z (Insert M hZFC x a) ↔ Mem M z a ∨ z = x := by
  rw [Insert, union_spec M hZFC]
  constructor
  · rintro ⟨b, hb, hz⟩
    rcases (pair_spec M hZFC _ _ b).mp hb with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr (((pair_spec M hZFC _ _ z).mp hz).elim id id)
  · rintro (h | heq)
    · exact ⟨a, (pair_spec M hZFC _ _ a).mpr (Or.inl rfl), h⟩
    · subst z
      exact ⟨PairSet M hZFC x x,
        (pair_spec M hZFC _ _ _).mpr (Or.inr rfl),
        (pair_spec M hZFC _ _ _).mpr (Or.inl rfl)⟩

theorem definable_separation {P : M.carrier → Prop} (hP : D1 P) (a : M.carrier) :
    ∃ b, ∀ x, Mem M x b ↔ Mem M x a ∧ P x := by
  have hs : PDef (fun v : ℕ → M.carrier => ∀ z, Mem M z (v 1) ↔ z = v 0) := by
    apply ((((DTerm.var 2).mem (DTerm.var 1)).iff
      ((DTerm.var 2).eq (DTerm.var 0))).all 2).congr
    intro v
    simp only [Function.update_self, Function.update_of_ne (show (1:ℕ) ≠ 2 by decide),
      Function.update_of_ne (show (0:ℕ) ≠ 2 by decide)]
    rfl
  let R := fun x y : M.carrier =>
    (P x ∧ ∀ z, Mem M z y ↔ z = x) ∨ (¬P x ∧ y = EmptySet M)
  have hR : D2 R := ((hP.slot 0).and hs).or
    (((hP.slot 0).not).and ((DTerm.var 1).eq (DTerm.const (EmptySet M))))
  obtain ⟨b, hb₁, hb₂⟩ := definable_collection M hZFC hR a (by
    intro x _
    by_cases hx : P x
    · exact ⟨PairSet M hZFC x x, Or.inl ⟨hx, fun z =>
        (pair_spec M hZFC x x z).trans ⟨fun h => h.elim id id, Or.inl⟩⟩⟩
    · exact ⟨EmptySet M, Or.inr ⟨hx, rfl⟩⟩)
  refine ⟨Union M b, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    obtain ⟨s, hsb, hxs⟩ := (union_spec M hZFC b x).mp hx
    obtain ⟨z, hza, hz⟩ := hb₂ s hsb
    rcases hz with h | h
    · have heq := (h.2 x).mp hxs
      exact heq ▸ ⟨hza, h.1⟩
    · rw [h.2] at hxs
      exact (empty_spec M hZFC _ hxs).elim
  · rintro ⟨hxa, hx⟩
    obtain ⟨s, hsb, hs⟩ := hb₁ x hxa
    rcases hs with h | h
    · exact (union_spec M hZFC b x).mpr ⟨s, hsb, (h.2 x).mpr rfl⟩
    · exact (h.1 hx).elim

theorem nonempty_ne_empty {a x : M.carrier} (hx : Mem M x a) : a ≠ EmptySet M := by
  intro h; rw [h] at hx; exact empty_spec M hZFC x hx

theorem no_self (x : M.carrier) : ¬Mem M x x := by
  intro hxx
  let s := PairSet M hZFC x x
  have hxs : Mem M x s := (pair_spec M hZFC x x x).mpr (Or.inl rfl)
  obtain ⟨y, hys, hy⟩ := regularity_spec M hZFC s (nonempty_ne_empty M hZFC hxs)
  have hyx : y = x := ((pair_spec M hZFC x x y).mp hys).elim id id
  exact hy x hxs (hyx.symm ▸ hxx)

theorem no_two_cycle {x y : M.carrier} (hxy : Mem M x y) : ¬Mem M y x := by
  intro hyx
  let s := PairSet M hZFC x y
  have hxs : Mem M x s := (pair_spec M hZFC x y x).mpr (Or.inl rfl)
  have hys : Mem M y s := (pair_spec M hZFC x y y).mpr (Or.inr rfl)
  obtain ⟨z, hzs, hz⟩ := regularity_spec M hZFC s (nonempty_ne_empty M hZFC hxs)
  rcases (pair_spec M hZFC x y z).mp hzs with rfl | rfl
  · exact hz y hys hyx
  · exact hz x hxs hxy

theorem no_three_cycle {x y z : M.carrier} (hxy : Mem M x y) (hyz : Mem M y z) :
    ¬Mem M z x := by
  intro hzx
  let s := Insert M hZFC x (PairSet M hZFC y z)
  have hxs : Mem M x s := (insert_spec M hZFC _ _ _).mpr (Or.inr rfl)
  have hys : Mem M y s := (insert_spec M hZFC _ _ _).mpr
    (Or.inl ((pair_spec M hZFC _ _ _).mpr (Or.inl rfl)))
  have hzs : Mem M z s := (insert_spec M hZFC _ _ _).mpr
    (Or.inl ((pair_spec M hZFC _ _ _).mpr (Or.inr rfl)))
  obtain ⟨w, hws, hw⟩ := regularity_spec M hZFC s (nonempty_ne_empty M hZFC hxs)
  rcases (insert_spec M hZFC _ _ _).mp hws with h | rfl
  · rcases (pair_spec M hZFC _ _ _).mp h with rfl | rfl
    · exact hw x hxs hxy
    · exact hw y hys hyz
  · exact hw z hzs hzx

theorem omega_mem_trans {x y z : M.carrier}
    (hx : Mem M x (Omega M)) (hz : Mem M z (Omega M))
    (hxy : Mem M x y) (hyz : Mem M y z) : Mem M x z := by
  have hO := (infinity_spec M hZFC).2
  rcases hO.1.1 x hx z hz with (heq | hxz) | hzx
  · exact (no_two_cycle M hZFC hxy (heq.symm ▸ hyz)).elim
  · exact hxz
  · exact (no_three_cycle M hZFC hxy hyz hzx).elim

theorem omega_successor (x : M.carrier) (hx : Mem M x (Omega M)) :
    ∃ s, (∀ z, Mem M z s ↔ Mem M z x ∨ z = x) ∧ Mem M s (Omega M) := by
  have hI := infinity_spec M hZFC
  have hP : D1 (fun z : M.carrier => Mem M x z) :=
    (DTerm.const x).mem (DTerm.var 0)
  obtain ⟨d, hd⟩ := definable_separation M hZFC hP (Omega M)
  obtain ⟨y, hyW, hxy⟩ := hI.1.2 x hx
  have hyd : Mem M y d := (hd y).mpr ⟨hyW,hxy⟩
  obtain ⟨s, hsd, hmin⟩ := hI.2.1.2 d
    (fun z hz => ((hd z).mp hz).1) (nonempty_ne_empty M hZFC hyd)
  have hs := (hd s).mp hsd
  refine ⟨s, fun z => ⟨?_, ?_⟩, hs.1⟩
  · intro hzs
    have hzW := hI.2.2 s hs.1 z hzs
    rcases hI.2.1.1 z hzW x hx with (heq | hzx) | hxz
    · exact Or.inr heq
    · exact Or.inl hzx
    · exact (hmin z ((hd z).mpr ⟨hzW,hxz⟩) hzs).elim
  · rintro (hzx | rfl)
    · exact omega_mem_trans M hZFC (hI.2.2 x hx z hzx) hs.1 hzx hs.2
    · exact hs.2

end
end ContinuumHypothesis.Cohen.CHFoundation
end

-- Development module: CohenCHLanguage
section

/-!
Definable Kuratowski graphs for the CH sentence comparison.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

The native foundation is due to Jesse Han and Floris van Doorn;
the reused Lean 4 port is by Ian Klatzco, with Claude, under Apache-2.0.
-/
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis.Cohen.CHFoundation
noncomputable section
variable {A : Type*} [setLang.Structure A]

def D3 (R : A → A → A → Prop) : Prop := PDef (fun v => R (v 0) (v 1) (v 2))

theorem PDef.substitute {P : (ℕ → A) → Prop} (hP : PDef P)
    (f : ℕ → setLang[[A]].Term ℕ) : PDef (fun v : ℕ → A => P (fun i => (f i).realize v)) := by
  obtain ⟨φ,hφ⟩ := hP
  refine ⟨φ.subst f, fun v => ?_⟩
  change BoundedFormula.Realize _ v Fin.elim0 ↔ _
  rw [BoundedFormula.realize_subst]
  exact hφ _

theorem D1.apply {P : A → Prop} {t : (ℕ → A) → A} (hP : D1 P) (ht : DTerm t) :
    PDef (fun v => P (t v)) := by
  obtain ⟨s,hs⟩ := ht
  exact (hP.substitute (fun _ => s)).congr (fun v => by dsimp; rw [hs])

theorem D2.apply {R : A → A → Prop} {t u : (ℕ → A) → A}
    (hR : D2 R) (ht : DTerm t) (hu : DTerm u) : PDef (fun v => R (t v) (u v)) := by
  obtain ⟨s,hs⟩ := ht
  obtain ⟨r,hr⟩ := hu
  apply (hR.substitute (fun i => if i = 0 then s else r)).congr
  intro v
  simp only [↓reduceIte, show (1:ℕ) ≠ 0 by decide, hs,hr]

theorem D3.apply {R : A → A → A → Prop} {t u w : (ℕ → A) → A}
    (hR : D3 R) (ht : DTerm t) (hu : DTerm u) (hw : DTerm w) :
    PDef (fun v => R (t v) (u v) (w v)) := by
  obtain ⟨s,hs⟩ := ht
  obtain ⟨r,hr⟩ := hu
  obtain ⟨q,hq⟩ := hw
  apply (hR.substitute (fun i => if i = 0 then s else if i = 1 then r else q)).congr
  intro v
  simp only [↓reduceIte, show (1:ℕ) ≠ 0 by decide, show (2:ℕ) ≠ 0 by decide,
    show (2:ℕ) ≠ 1 by decide, hs,hr,hq]

theorem formula_definable (φ : SFormula) :
    PDef (fun v : ℕ → A => Formula.Realize φ v) :=
  ⟨(setLang.lhomWithConstants A).onFormula φ,
    fun _ => (setLang.lhomWithConstants A).realize_onFormula φ⟩

theorem realize_all (v : ℕ → A) (i : ℕ) (φ : SFormula) :
    Formula.Realize (SFormula.all i φ) v ↔ ∀ z, Formula.Realize φ (Function.update v i z) :=
  namedAll_realize φ i v

theorem realize_ex (v : ℕ → A) (i : ℕ) (φ : SFormula) :
    Formula.Realize (SFormula.ex i φ) v ↔ ∃ z, Formula.Realize φ (Function.update v i z) :=
  namedEx_realize φ i v

end
end ContinuumHypothesis.Cohen.CHFoundation

namespace ContinuumHypothesis.Cohen.CHTransfer
open CHFoundation
noncomputable section
variable (M : Fol.Structure L_ZFC)
local instance : setLang.Structure M.carrier := membershipReduct M

def IsEmpty (e : M.carrier) : Prop := ∀ z, ¬Mem M z e
def IsSingle (s x : M.carrier) : Prop := ∀ z, Mem M z s ↔ z = x
def IsDouble (s x y : M.carrier) : Prop := ∀ z, Mem M z s ↔ z = x ∨ z = y
def IsKPair (p x y : M.carrier) : Prop :=
  ∀ z, Mem M z p ↔ IsSingle M z x ∨ IsDouble M z x y
def KRel (f x y : M.carrier) : Prop := ∃ p, IsKPair M p x y ∧ Mem M p f
def IsSucc (s x : M.carrier) : Prop := ∀ z, Mem M z s ↔ Mem M z x ∨ z = x
def PureInd (I : M.carrier) : Prop :=
  (∃ e, IsEmpty M e ∧ Mem M e I) ∧
    ∀ x, Mem M x I → ∃ s, IsSucc M s x ∧ Mem M s I

theorem realize_mem (v : ℕ → M.carrier) (i j : ℕ) :
    Formula.Realize (SFormula.mem i j) v ↔ Mem M (v i) (v j) := Iff.rfl

theorem realize_eq (v : ℕ → M.carrier) (i j : ℕ) :
    Formula.Realize (SFormula.eq i j) v ↔ v i = v j := Iff.rfl

theorem kpair_definable : D3 (IsKPair M) := by
  apply (formula_definable (A := M.carrier) (SFormula.isPair 0 1 2)).congr
  intro v
  simp only [SFormula.isPair, SFormula.isSingleton, SFormula.isDoubleton,
    realize_all, Formula.realize_iff, Formula.realize_sup, realize_mem, realize_eq,
    Function.update_apply, IsKPair, IsSingle, IsDouble]
  norm_num only
  simp only [ite_true,ite_false]

theorem krel_definable : D3 (KRel M) := by
  apply ((kpair_definable M).apply (DTerm.var 3) (DTerm.var 1) (DTerm.var 2)
    |>.and ((DTerm.var 3).mem (DTerm.var 0)) |>.ex 3).congr
  intro v
  simp only [Function.update_self,
    Function.update_of_ne (show (0:ℕ) ≠ 3 by decide),
    Function.update_of_ne (show (1:ℕ) ≠ 3 by decide),
    Function.update_of_ne (show (2:ℕ) ≠ 3 by decide)]
  rfl

theorem succ_definable : D2 (IsSucc M) := by
  apply (formula_definable (A := M.carrier) (SFormula.isSucc 0 1)).congr
  intro v
  simp only [SFormula.isSucc, realize_all, Formula.realize_iff, Formula.realize_sup,
    realize_mem, realize_eq, Function.update_apply, IsSucc]
  norm_num only
  simp only [ite_true,ite_false]

theorem pureInd_definable : D1 (PureInd M) := by
  apply (formula_definable (A := M.carrier) (SFormula.isInductive 0)).congr
  intro v
  simp only [SFormula.isInductive, SFormula.isEmpty, SFormula.isSucc,
    realize_all, realize_ex, Formula.realize_inf, Formula.realize_iff, Formula.realize_imp,
    Formula.realize_sup, Formula.realize_not, realize_mem, realize_eq,
    Function.update_apply, PureInd, IsEmpty, IsSucc]
  norm_num only
  simp only [ite_true,ite_false]

theorem sub_definable (a : M.carrier) : D1 (fun x => Sub M x a) := by
  apply (((DTerm.var 1).mem (DTerm.var 0)).imp ((DTerm.var 1).mem (DTerm.const a))
    |>.all 1).congr
  intro v
  simp only [Function.update_self, Function.update_of_ne (show (0:ℕ) ≠ 1 by decide)]
  rfl

end
end ContinuumHypothesis.Cohen.CHTransfer
end

-- Development module: CohenCHPairs
section

/-!
Internal Kuratowski pairs, graph membership, and Cartesian products.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000
open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis.Cohen.CHTransfer
open CHFoundation
noncomputable section
variable (M : Fol.Structure L_ZFC) (hZFC : Fol.all_realize_sentence M _root_.ZFC)
local instance : setLang.Structure M.carrier := membershipReduct M
include hZFC

theorem single_iff (s x : M.carrier) : IsSingle M s x ↔ s = PairSet M hZFC x x := by
  constructor
  · intro h
    apply ext_spec M hZFC
    intro z
    rw [h z, pair_spec M hZFC]
    tauto
  · rintro rfl z
    rw [pair_spec M hZFC]
    tauto

theorem double_iff (s x y : M.carrier) : IsDouble M s x y ↔ s = PairSet M hZFC x y := by
  constructor
  · intro h
    exact ext_spec M hZFC _ _ (fun z => (h z).trans (pair_spec M hZFC x y z).symm)
  · rintro rfl
    exact pair_spec M hZFC x y

def KPair (x y : M.carrier) : M.carrier :=
  PairSet M hZFC (PairSet M hZFC x x) (PairSet M hZFC x y)

theorem kpair_iff (p x y : M.carrier) : IsKPair M p x y ↔ p = KPair M hZFC x y := by
  constructor
  · intro hp
    apply ext_spec M hZFC
    intro z
    rw [hp z, KPair, pair_spec M hZFC, single_iff M hZFC, double_iff M hZFC]
  · rintro rfl z
    rw [KPair, pair_spec M hZFC, single_iff M hZFC, double_iff M hZFC]

theorem kpair_spec (x y z : M.carrier) :
    Mem M z (KPair M hZFC x y) ↔ IsSingle M z x ∨ IsDouble M z x y :=
  (kpair_iff M hZFC _ x y).mpr rfl z

theorem union_kpair_spec (x y z : M.carrier) :
    Mem M z (Union M (KPair M hZFC x y)) ↔ z = x ∨ z = y := by
  rw [union_spec M hZFC]
  constructor
  · rintro ⟨s,hs,hzs⟩
    rcases (kpair_spec M hZFC x y s).mp hs with hs | hs
    · exact Or.inl ((hs z).mp hzs)
    · exact (hs z).mp hzs
  · intro hz
    refine ⟨PairSet M hZFC x y, ?_, (pair_spec M hZFC x y z).mpr hz⟩
    exact (kpair_spec M hZFC x y _).mpr (Or.inr (pair_spec M hZFC x y))

theorem kpair_inj (x y u v : M.carrier) :
    KPair M hZFC x y = KPair M hZFC u v ↔ x = u ∧ y = v := by
  constructor
  · intro h
    have hs : Mem M (PairSet M hZFC x x) (KPair M hZFC x y) :=
      (kpair_spec M hZFC x y _).mpr (Or.inl ((single_iff M hZFC _ x).mpr rfl))
    rw [h] at hs
    have hux : u = x := by
      have humem : Mem M u (PairSet M hZFC x x) := by
        rcases (kpair_spec M hZFC u v _).mp hs with hh | hh
        · exact (hh u).mpr rfl
        · exact (hh u).mpr (Or.inl rfl)
      exact ((pair_spec M hZFC x x u).mp humem).elim id id
    subst u
    refine ⟨rfl, ?_⟩
    by_cases hyx : y = x
    · have hv : Mem M v (Union M (KPair M hZFC x y)) := by
        rw [h]
        exact (union_kpair_spec M hZFC x v v).mpr (Or.inr rfl)
      rcases (union_kpair_spec M hZFC x y v).mp hv with hv | hv
      · exact hyx.trans hv.symm
      · exact hv.symm
    · have hy : Mem M y (Union M (KPair M hZFC x v)) := by
        rw [←h]
        exact (union_kpair_spec M hZFC x y y).mpr (Or.inr rfl)
      exact ((union_kpair_spec M hZFC x v y).mp hy).resolve_left hyx
  · rintro ⟨rfl,rfl⟩
    rfl

theorem krel_iff (f x y : M.carrier) : KRel M f x y ↔ Mem M (KPair M hZFC x y) f := by
  constructor
  · rintro ⟨p,hp,hpf⟩
    rw [(kpair_iff M hZFC p x y).mp hp] at hpf
    exact hpf
  · intro h
    exact ⟨KPair M hZFC x y,(kpair_iff M hZFC _ x y).mpr rfl,h⟩

theorem krel_mono {f g x y : M.carrier} (hfg : Sub M f g) (h : KRel M f x y) :
    KRel M g x y := by
  obtain ⟨p,hp,hpf⟩ := h
  exact ⟨p,hp,hfg p hpf⟩

theorem krel_empty (x y : M.carrier) : ¬KRel M (EmptySet M) x y := by
  rintro ⟨p,_,hp⟩
  exact empty_spec M hZFC p hp

theorem krel_union (C x y : M.carrier) :
    KRel M (Union M C) x y ↔ ∃ f, Mem M f C ∧ KRel M f x y := by
  simp only [krel_iff M hZFC, union_spec M hZFC]

theorem krel_insert (f a b x y : M.carrier) :
    KRel M (Insert M hZFC (KPair M hZFC a b) f) x y ↔
      KRel M f x y ∨ (x = a ∧ y = b) := by
  rw [krel_iff M hZFC, insert_spec M hZFC, kpair_inj M hZFC, krel_iff M hZFC]

def Join (a b : M.carrier) : M.carrier := Union M (PairSet M hZFC a b)

theorem join_spec (a b z : M.carrier) : Mem M z (Join M hZFC a b) ↔ Mem M z a ∨ Mem M z b := by
  rw [Join, union_spec M hZFC]
  constructor
  · rintro ⟨s,hs,hzs⟩
    rcases (pair_spec M hZFC a b s).mp hs with rfl | rfl
    · exact Or.inl hzs
    · exact Or.inr hzs
  · rintro (hz | hz)
    · exact ⟨a,(pair_spec M hZFC a b a).mpr (Or.inl rfl),hz⟩
    · exact ⟨b,(pair_spec M hZFC a b b).mpr (Or.inr rfl),hz⟩

theorem kpair_power_bound {U p x y : M.carrier}
    (hx : Mem M x U) (hy : Mem M y U) (hp : IsKPair M p x y) :
    Mem M p (Power M (Power M U)) := by
  apply (power_spec M hZFC _ _).mpr
  intro s hs
  apply (power_spec M hZFC _ _).mpr
  intro z hz
  rcases (hp s).mp hs with h | h
  · have he := (h z).mp hz
    exact he ▸ hx
  · rcases (h z).mp hz with he | he
    · exact he ▸ hx
    · exact he ▸ hy

theorem product_exists (A B : M.carrier) :
    ∃ P, ∀ p, Mem M p P ↔ ∃ x, Mem M x A ∧ ∃ y, Mem M y B ∧ IsKPair M p x y := by
  have hd : D1 (fun p : M.carrier =>
      ∃ x, Mem M x A ∧ ∃ y, Mem M y B ∧ IsKPair M p x y) := by
    have h := ((DTerm.var 1).mem (DTerm.const A)).and
      ((((DTerm.var 2).mem (DTerm.const B)).and
        ((kpair_definable M).apply (DTerm.var 0) (DTerm.var 1) (DTerm.var 2))).ex 2)
    apply (h.ex 1).congr
    intro v
    simp only [Function.update_self,
      Function.update_of_ne (show (0:ℕ) ≠ 1 by decide),
      Function.update_of_ne (show (0:ℕ) ≠ 2 by decide),
      Function.update_of_ne (show (1:ℕ) ≠ 2 by decide)]
    rfl
  obtain ⟨P,hP⟩ := definable_separation M hZFC hd (Power M (Power M (Join M hZFC A B)))
  refine ⟨P,fun p => (hP p).trans ?_⟩
  constructor
  · exact And.right
  · rintro ⟨x,hx,y,hy,hp⟩
    exact ⟨kpair_power_bound M hZFC ((join_spec M hZFC _ _ _).mpr (Or.inl hx))
      ((join_spec M hZFC _ _ _).mpr (Or.inr hy)) hp,x,hx,y,hy,hp⟩

def Product (A B : M.carrier) : M.carrier := (product_exists M hZFC A B).choose

theorem product_spec (A B p : M.carrier) :
    Mem M p (Product M hZFC A B) ↔
      ∃ x, Mem M x A ∧ ∃ y, Mem M y B ∧ IsKPair M p x y :=
  (product_exists M hZFC A B).choose_spec p

theorem pair_mem_product (A B x y : M.carrier) :
    Mem M (KPair M hZFC x y) (Product M hZFC A B) ↔ Mem M x A ∧ Mem M y B := by
  rw [product_spec M hZFC]
  constructor
  · rintro ⟨u,hu,v,hv,hp⟩
    have heq := (kpair_inj M hZFC x y u v).mp ((kpair_iff M hZFC _ u v).mp hp)
    exact ⟨heq.1.symm ▸ hu,heq.2.symm ▸ hv⟩
  · rintro ⟨hx,hy⟩
    exact ⟨x,hx,y,hy,(kpair_iff M hZFC _ x y).mpr rfl⟩

theorem krel_bounds {A B f x y : M.carrier}
    (hf : Sub M f (Product M hZFC A B)) (hxy : KRel M f x y) :
    Mem M x A ∧ Mem M y B :=
  (pair_mem_product M hZFC A B x y).mp (hf _ ((krel_iff M hZFC f x y).mp hxy))

end
end ContinuumHypothesis.Cohen.CHTransfer
end

-- Development module: CohenCHNative
section

/-!
Primitive graph coding and ordinary semantics of Flypitch's CH sentence.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

Native syntax and axioms: Jesse Han and Floris van Doorn; Lean 4 port:
Ian Klatzco, with Claude. Original Apache-2.0 notices are preserved.
-/
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000
open FirstOrder FirstOrder.Language Fol

namespace ContinuumHypothesis.Cohen.CHTransfer
open CHFoundation
noncomputable section
variable (M : Fol.Structure L_ZFC)
local instance chNativeStructure : setLang.Structure M.carrier := membershipReduct M

def NPair (x y : M.carrier) : M.carrier := M.fun_map ZFC_func.pr (.cons x (.cons y .nil))
def NFunc (f : M.carrier) : Prop := ∀ x u y v,
  (Mem M (NPair M x y) f ∧ Mem M (NPair M u v) f) → x = u → y = v
def NTotal (A B f : M.carrier) : Prop :=
  ∀ x, Mem M x A → ∃ y, Mem M y B ∧ Mem M (NPair M x y) f
def NLe (A B : M.carrier) : Prop := ∃ d f,
  (Sub M d B ∧ (NFunc M f ∧ NTotal M d A f)) ∧
    ∀ y, Mem M y A → ∃ x, Mem M x d ∧ Mem M (NPair M x y) f

@[simp] theorem eval_pair {n} (vs : DVec M.carrier n) (x y : bounded_term L_ZFC n) :
    realize_bounded_term (S := M) vs (pair' x y) .nil =
      NPair M (realize_bounded_term vs x .nil) (realize_bounded_term vs y .nil) := rfl

theorem eval_atMost (A B : M.carrier) :
    realize_bounded_formula (.cons A (.cons B .nil)) at_most_f .nil ↔ NLe M A B := by
  simp only [at_most_f, is_func'_f₂, is_func_f, is_total'_f₂,
    realize_bounded_formula_ex, realize_bounded_formula_and, eval_subset,
    realize_cast_bounded_formula, DVec.trunc, realize_bounded_formula,
    eval_mem, eval_pair, realize_bounded_term, DVec.nth, NLe,NFunc,NTotal]

theorem native_CH_iff : realize_sentence M CH_f ↔
    ∀ a, NOrd M a → NLe M a (Omega M) ∨ NLe M (Power M (Omega M)) a := by
  have h1 (a : M.carrier) :
      realize_bounded_formula (.cons a .nil) (substmax_bounded_formula at_most_f omega') .nil =
        realize_bounded_formula (.cons a (.cons (Omega M) .nil)) at_most_f .nil := by rfl
  have h2 (a : M.carrier) :
      realize_bounded_formula (.cons a .nil) (subst0_bounded_formula at_most_f (Powerset omega')) .nil =
        realize_bounded_formula (.cons (Power M (Omega M)) (.cons a .nil)) at_most_f .nil := by rfl
  simp only [CH_f, realize_sentence_all, realize_bounded_formula, eval_or,
    eval_ord, h1,h2,eval_atMost]

variable (hZFC : Fol.all_realize_sentence M _root_.ZFC)
include hZFC

theorem npair_inj (x y u v : M.carrier) : NPair M x y = NPair M u v ↔ x = u ∧ y = v := by
  have h := hZFC (show axiom_of_ordered_pairs ∈ _root_.ZFC by
    simp only [_root_.ZFC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,or_true,true_or])
  have hh : ∀ x y u v, NPair M x y = NPair M u v ↔ x = u ∧ y = v := by
    simpa only [axiom_of_ordered_pairs, realize_sentence, realize_bounded_formula,
      realize_bounded_formula_biimp,realize_bounded_formula_and,eval_pair,
      realize_bounded_term,DVec.nth] using h
  exact hh x y u v

omit hZFC in
theorem eval_lift_one {n} (φ : bounded_formula L_ZFC (n+2))
    (ps : DVec M.carrier n) (y x p : M.carrier) :
    realize_bounded_formula (.cons y (.cons p (.cons x ps))) (lift_bounded_formula_at φ 1 1) .nil =
      realize_bounded_formula (.cons y (.cons x ps)) φ .nil := by
  convert realize_bounded_formula_insert_lift (.cons y (.cons x ps)) p 1 (by omega) φ .nil using 2
  rfl

theorem native_pair_graph {R : M.carrier → M.carrier → Prop} (hR : D2 R)
    (A : M.carrier) (ht : ∀ x, Mem M x A → ∃ y, R x y)
    (hu : ∀ x, Mem M x A → ∀ y z, R x y → R x z → y = z) :
    ∃ f, ∀ x y, Mem M (NPair M x y) f ↔ Mem M x A ∧ R x y := by
  obtain ⟨n,ps,φ,hφ⟩ := native_code M hR
  let ψ : bounded_formula L_ZFC (n+2) := bd_ex (bd_and (lift_bounded_formula_at φ 1 1)
    (bd_equal (bd_var ⟨1,by omega⟩) (pair' (bd_var ⟨2,by omega⟩) (bd_var ⟨0,by omega⟩))))
  have hψ (p x : M.carrier) : realize_bounded_formula (.cons p (.cons x ps)) ψ .nil ↔
      ∃ y, R x y ∧ p = NPair M x y := by
    simp only [ψ,realize_bounded_formula_ex,realize_bounded_formula_and,
      eval_lift_one,hφ,realize_bounded_formula,eval_pair,realize_bounded_term,DVec.nth]
  obtain ⟨f,hf₁,hf₂⟩ := collection_spec M hZFC ψ ps A (by
    intro x hx
    obtain ⟨y,hy⟩ := ht x hx
    exact ⟨NPair M x y,(hψ _ _).mpr ⟨y,hy,rfl⟩⟩)
  refine ⟨f,fun x y => ⟨?_,?_⟩⟩
  · intro hxy
    obtain ⟨u,huA,hpu⟩ := hf₂ (NPair M x y) hxy
    obtain ⟨v,huv,heq⟩ := (hψ _ _).mp hpu
    have he := (npair_inj M hZFC x y u v).mp heq
    exact ⟨he.1.symm ▸ huA,he.1.symm ▸ he.2.symm ▸ huv⟩
  · rintro ⟨hxA,hxy⟩
    obtain ⟨p,hpf,hp⟩ := hf₁ x hxA
    obtain ⟨z,hxz,hpz⟩ := (hψ _ _).mp hp
    have hzy := hu x hxA z y hxz hxy
    rw [hzy] at hpz
    rw [hpz] at hpf
    exact hpf

theorem nle_of_definable_surjection {R : M.carrier → M.carrier → Prop} (hR : D2 R)
    (A B d : M.carrier) (hd : Sub M d B)
    (ht : ∀ x, Mem M x d → ∃ y, Mem M y A ∧ R x y)
    (hu : ∀ x, Mem M x d → ∀ y z, R x y → R x z → y = z)
    (hs : ∀ y, Mem M y A → ∃ x, Mem M x d ∧ R x y) : NLe M A B := by
  let R' := fun x y : M.carrier => Mem M y A ∧ R x y
  have hR' : D2 R' := ((DTerm.var 1).mem (DTerm.const A)).and hR
  obtain ⟨f,hf⟩ := native_pair_graph M hZFC hR' d ht
    (fun x hx y z hy hz => hu x hx y z hy.2 hz.2)
  refine ⟨d,f,⟨hd,?_,?_⟩,?_⟩
  · intro x u y v hxu he
    obtain ⟨hx,hy⟩ := (hf x y).mp hxu.1
    obtain ⟨_,hv⟩ := (hf u v).mp hxu.2
    subst u
    exact hu x hx y v hy.2 hv.2
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := ht x hx
    exact ⟨y,hy,(hf x y).mpr ⟨hx,hy,hxy⟩⟩
  · intro y hy
    obtain ⟨x,hx,hxy⟩ := hs y hy
    exact ⟨x,hx,(hf x y).mpr ⟨hx,hy,hxy⟩⟩

structure InjectionOn (R : M.carrier → M.carrier → Prop) (A B : M.carrier) : Prop where
  total : ∀ x, Mem M x A → ∃ y, Mem M y B ∧ R x y
  functional : ∀ x, Mem M x A → ∀ y z, R x y → R x z → y = z
  injective : ∀ x u, Mem M x A → Mem M u A → ∀ y, R x y → R u y → x = u

theorem nle_of_definable_injection {R : M.carrier → M.carrier → Prop}
    (hR : D2 R) (A B : M.carrier) (hI : InjectionOn M R A B) : NLe M A B := by
  have hp : D1 (fun y : M.carrier => ∃ x, Mem M x A ∧ R x y) := by
    apply ((((DTerm.var 2).mem (DTerm.const A)).and
      (hR.apply (DTerm.var 2) (DTerm.var 0))).ex 2).congr
    intro v
    simp only [Function.update_self,Function.update_of_ne (show (0:ℕ) ≠ 2 by decide)]
    rfl
  obtain ⟨d,hd⟩ := definable_separation M hZFC hp B
  let S := fun y x : M.carrier => Mem M x A ∧ R x y
  have hS : D2 S := ((DTerm.var 1).mem (DTerm.const A)).and
    (hR.apply (DTerm.var 1) (DTerm.var 0))
  apply nle_of_definable_surjection M hZFC hS A B d (fun y hy => ((hd y).mp hy).1)
  · intro y hy
    obtain ⟨x,hx,hxy⟩ := ((hd y).mp hy).2
    exact ⟨x,hx,hx,hxy⟩
  · intro y hy x u hx hu
    exact hI.injective x u hx.1 hu.1 y hx.2 hu.2
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := hI.total x hx
    exact ⟨y,(hd y).mpr ⟨hy,x,hx,hxy⟩,hx,hxy⟩

end
end ContinuumHypothesis.Cohen.CHTransfer
end

-- Development module: CohenCHOmega
section

/-!
The designated native omega is the least inductive set in the reduct.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000
open FirstOrder FirstOrder.Language Fol

namespace ContinuumHypothesis.Cohen.CHTransfer
open CHFoundation
noncomputable section
variable (M : Fol.Structure L_ZFC) (hZFC : Fol.all_realize_sentence M _root_.ZFC)
local instance chOmegaStructure : setLang.Structure M.carrier := membershipReduct M
include hZFC

def Ind (I : M.carrier) : Prop := Mem M (EmptySet M) I ∧
  ∀ x, Mem M x I → Mem M (Insert M hZFC x x) I

theorem empty_iff (e : M.carrier) : IsEmpty M e ↔ e = EmptySet M := by
  constructor
  · intro h
    apply ext_spec M hZFC
    intro z
    exact ⟨fun hz => (h z hz).elim,fun hz => (empty_spec M hZFC z hz).elim⟩
  · rintro rfl
    exact empty_spec M hZFC

theorem succ_iff (s x : M.carrier) : IsSucc M s x ↔ s = Insert M hZFC x x := by
  constructor
  · intro h
    exact ext_spec M hZFC _ _ (fun z => (h z).trans (insert_spec M hZFC x x z).symm)
  · rintro rfl
    exact insert_spec M hZFC x x

theorem pure_ind_iff (I : M.carrier) : PureInd M I ↔ Ind M hZFC I := by
  constructor
  · rintro ⟨⟨e,he,heI⟩,hs⟩
    have heq := (empty_iff M hZFC e).mp he
    refine ⟨heq ▸ heI,?_⟩
    intro x hx
    obtain ⟨s,hsx,hsI⟩ := hs x hx
    have heq := (succ_iff M hZFC s x).mp hsx
    exact heq ▸ hsI
  · rintro ⟨he,hs⟩
    exact ⟨⟨EmptySet M,empty_spec M hZFC,he⟩,
      fun x hx => ⟨Insert M hZFC x x,insert_spec M hZFC x x,hs x hx⟩⟩

theorem ind_definable : D1 (Ind M hZFC) :=
  (pureInd_definable M).congr (fun v => pure_ind_iff M hZFC (v 0))

theorem omega_ind : Ind M hZFC (Omega M) := by
  refine ⟨(infinity_spec M hZFC).1.1,?_⟩
  intro x hx
  obtain ⟨s,hs,hsW⟩ := omega_successor M hZFC x hx
  have heq := (succ_iff M hZFC s x).mp hs
  exact heq ▸ hsW

theorem infinity_least_limit (a : M.carrier) (ha : NOrd M a)
    (hlim : Mem M (EmptySet M) a ∧
      ∀ x, Mem M x a → ∃ y, Mem M y a ∧ Mem M x y) : Sub M (Omega M) a := by
  have h := hZFC (show axiom_of_infinity ∈ _root_.ZFC by
    simp only [_root_.ZFC,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,or_true,true_or])
  rw [axiom_of_infinity,realize_sentence_and] at h
  have hh : ∀ a, NOrd M a → (Mem M (EmptySet M) a ∧
      ∀ x, Mem M x a → ∃ y, Mem M y a ∧ Mem M x y) → Sub M (Omega M) a := by
    simpa only [realize_sentence,realize_bounded_formula_and,realize_bounded_formula_ex,
      eval_ord,eval_mem,eval_empty,eval_omega,eval_subset,realize_bounded_formula,
      realize_bounded_term,DVec.nth] using h.2
  exact hh a ha hlim

theorem omega_least_ind (I : M.carrier) (hI : Ind M hZFC I) : Sub M (Omega M) I := by
  have hp : D1 (fun z : M.carrier => ∀ J, Ind M hZFC J → Mem M z J) := by
    apply (((ind_definable M hZFC).slot 1).imp ((DTerm.var 0).mem (DTerm.var 1))
      |>.all 1).congr
    intro v
    simp only [Function.update_self,Function.update_of_ne (show (0:ℕ) ≠ 1 by decide)]
    rfl
  obtain ⟨O,hO⟩ := definable_separation M hZFC hp (Omega M)
  have hOW : Sub M O (Omega M) := fun z hz => ((hO z).mp hz).1
  have hleast (J : M.carrier) (hJ : Ind M hZFC J) : Sub M O J :=
    fun z hz => ((hO z).mp hz).2 J hJ
  have hOE : Mem M (EmptySet M) O := (hO _).mpr
    ⟨(omega_ind M hZFC).1,fun J hJ => hJ.1⟩
  have hOI : Ind M hZFC O := by
    refine ⟨hOE,?_⟩
    intro x hx
    apply (hO _).mpr
    exact ⟨(omega_ind M hZFC).2 x (hOW x hx),
      fun J hJ => hJ.2 x (hleast J hJ x hx)⟩
  obtain ⟨T,hT⟩ := definable_separation M hZFC (sub_definable M O) O
  have hTI : Ind M hZFC T := by
    refine ⟨(hT _).mpr ⟨hOE,fun z hz => (empty_spec M hZFC z hz).elim⟩,?_⟩
    intro x hx
    have hxx := (hT x).mp hx
    apply (hT _).mpr
    refine ⟨hOI.2 x hxx.1,?_⟩
    intro z hz
    rcases (insert_spec M hZFC x x z).mp hz with hzx | heq
    · exact hxx.2 z hzx
    · rw [heq]
      exact hxx.1
  have hOT : Sub M O T := hleast T hTI
  have htrans : ∀ x, Mem M x O → Sub M x O := fun x hx => ((hT x).mp (hOT x hx)).2
  have hOrd : NOrd M O := by
    refine ⟨⟨?_,?_⟩,htrans⟩
    · intro x hx y hy
      exact (infinity_spec M hZFC).2.1.1 x (hOW x hx) y (hOW y hy)
    · intro b hb hne
      exact (infinity_spec M hZFC).2.1.2 b (fun z hz => hOW z (hb z hz)) hne
  have hWO : Sub M (Omega M) O := infinity_least_limit M hZFC O hOrd
    ⟨hOE,fun x hx => ⟨Insert M hZFC x x,hOI.2 x hx,
      (insert_spec M hZFC x x x).mpr (Or.inr rfl)⟩⟩
  exact fun z hz => hleast I hI z (hWO z hz)

end
end ContinuumHypothesis.Cohen.CHTransfer
end

-- Development module: CohenCHComparison
section

/-!
Internal cardinal comparison by maximal partial bijections.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000
open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis.Cohen.CHTransfer
open CHFoundation
noncomputable section
variable (M : Fol.Structure L_ZFC) (hZFC : Fol.all_realize_sentence M _root_.ZFC)
local instance : setLang.Structure M.carrier := membershipReduct M
include hZFC

def Matching (f : M.carrier) : Prop := ∀ x y u v,
  KRel M f x y → KRel M f u v → (x = u ↔ y = v)

theorem matching_definable : D1 (Matching M) := by
  have h := ((krel_definable M).apply (DTerm.var 0) (DTerm.var 1) (DTerm.var 2)).imp
    (((krel_definable M).apply (DTerm.var 0) (DTerm.var 3) (DTerm.var 4)).imp
      (((DTerm.var 1).eq (DTerm.var 3)).iff ((DTerm.var 2).eq (DTerm.var 4))))
  apply ((((h.all 4).all 3).all 2).all 1).congr
  intro v
  simp only [Function.update_apply,Matching]
  norm_num only
  simp only [ite_true,ite_false]

theorem matching_functional {f x y z : M.carrier} (hf : Matching M f)
    (hxy : KRel M f x y) (hxz : KRel M f x z) : y = z :=
  (hf x y x z hxy hxz).mp rfl

theorem matching_injective {f x u y : M.carrier} (hf : Matching M f)
    (hxy : KRel M f x y) (huy : KRel M f u y) : x = u :=
  (hf x y u y hxy huy).mpr rfl

theorem partial_bijection_comparison (A B : M.carrier) :
    ∃ f, Sub M f (Product M hZFC A B) ∧ Matching M f ∧
      ((∀ x, Mem M x A → ∃ y, Mem M y B ∧ KRel M f x y) ∨
       (∀ y, Mem M y B → ∃ x, Mem M x A ∧ KRel M f x y)) := by
  classical
  obtain ⟨Q,hQ⟩ := definable_separation M hZFC (matching_definable M hZFC)
    (Power M (Product M hZFC A B))
  have hQ' (f : M.carrier) : Mem M f Q ↔ Sub M f (Product M hZFC A B) ∧ Matching M f :=
    (hQ f).trans (and_congr (power_spec M hZFC _ _) Iff.rfl)
  have hEQ : Mem M (EmptySet M) Q := (hQ' _).mpr
    ⟨fun p hp => (empty_spec M hZFC p hp).elim,
      fun x y u v hxy => (krel_empty M hZFC x y hxy).elim⟩
  have hchain (C : M.carrier) (hCQ : Sub M C Q)
      (hC : ∀ c, Mem M c C → ∀ d, Mem M d C → Sub M c d ∨ Sub M d c) :
      Mem M (Union M C) Q := by
    apply (hQ' _).mpr
    constructor
    · intro p hp
      obtain ⟨f,hf,hpf⟩ := (union_spec M hZFC C p).mp hp
      exact ((hQ' f).mp (hCQ f hf)).1 p hpf
    · intro x y u v hxy huv
      obtain ⟨f,hf,hxy⟩ := (krel_union M hZFC C x y).mp hxy
      obtain ⟨g,hg,huv⟩ := (krel_union M hZFC C u v).mp huv
      rcases hC f hf g hg with hfg | hgf
      · exact ((hQ' g).mp (hCQ g hg)).2 x y u v (krel_mono M hZFC hfg hxy) huv
      · exact ((hQ' f).mp (hCQ f hf)).2 x y u v hxy (krel_mono M hZFC hgf huv)
  obtain ⟨f,hfQ,hmax⟩ := zorn_spec M hZFC Q (nonempty_ne_empty M hZFC hEQ) hchain
  have hf := (hQ' f).mp hfQ
  refine ⟨f,hf.1,hf.2,?_⟩
  by_cases ht : ∀ x, Mem M x A → ∃ y, Mem M y B ∧ KRel M f x y
  · exact Or.inl ht
  · apply Or.inr
    intro b hbB
    by_cases hb : ∃ x, Mem M x A ∧ KRel M f x b
    · exact hb
    · have ha : ∃ a, Mem M a A ∧ ¬∃ y, Mem M y B ∧ KRel M f a y := by
        by_contra hn
        apply ht
        intro a haA
        by_contra hmiss
        exact hn ⟨a,haA,hmiss⟩
      obtain ⟨a,haA,hmiss⟩ := ha
      have hfresh (x y : M.carrier) (hxy : KRel M f x y) : x ≠ a ∧ y ≠ b := by
        have hbounds := krel_bounds M hZFC hf.1 hxy
        constructor
        · intro hx
          subst x
          exact hmiss ⟨y,hbounds.2,hxy⟩
        · intro hy
          subst y
          exact hb ⟨x,hbounds.1,hxy⟩
      let d := Insert M hZFC (KPair M hZFC a b) f
      have hdQ : Mem M d Q := by
        apply (hQ' d).mpr
        constructor
        · intro p hp
          rcases (insert_spec M hZFC _ _ p).mp hp with hpf | heq
          · exact hf.1 p hpf
          · rw [heq]
            exact (pair_mem_product M hZFC A B a b).mpr ⟨haA,hbB⟩
        · intro x y u v hxy huv
          rcases (krel_insert M hZFC f a b x y).mp hxy with hxy | hxy
          · rcases (krel_insert M hZFC f a b u v).mp huv with huv | huv
            · exact hf.2 x y u v hxy huv
            · obtain ⟨hu,hv⟩ := huv
              subst u; subst v
              exact ⟨fun h => ((hfresh x y hxy).1 h).elim,
                fun h => ((hfresh x y hxy).2 h).elim⟩
          · obtain ⟨hx,hy⟩ := hxy
            subst x; subst y
            rcases (krel_insert M hZFC f a b u v).mp huv with huv | huv
            · exact ⟨fun h => ((hfresh u v huv).1 h.symm).elim,
                fun h => ((hfresh u v huv).2 h.symm).elim⟩
            · obtain ⟨hu,hv⟩ := huv
              subst u; subst v
              exact ⟨fun _ => rfl,fun _ => rfl⟩
      have hfd : Sub M f d := fun p hp => (insert_spec M hZFC _ _ p).mpr (Or.inl hp)
      have hfdEq := hmax d hdQ hfd
      have hpair : Mem M (KPair M hZFC a b) d :=
        (insert_spec M hZFC _ _ _).mpr (Or.inr rfl)
      rw [←hfdEq] at hpair
      exact (hmiss ⟨b,hbB,(krel_iff M hZFC f a b).mpr hpair⟩).elim

end
end ContinuumHypothesis.Cohen.CHTransfer
end

-- Development module: CohenCHSemantics
section

/-!
Reading the exact mission CH sentence as internal graph witnesses.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis.Cohen.CHTransfer
open CHFoundation
noncomputable section
variable (M : Fol.Structure L_ZFC)
local instance chSemanticsStructure : setLang.Structure M.carrier := membershipReduct M

def RawInjection (R : M.carrier → M.carrier → Prop) (A B : M.carrier) : Prop :=
  ((∀ x, Mem M x A → ∃ y, Mem M y B ∧ R x y) ∧
    (∀ x y z, ((Mem M x A ∧ R x y) ∧ R x z) → y = z)) ∧
    ∀ x u y, (((Mem M x A ∧ Mem M u A) ∧ R x y) ∧ R u y) → x = u

theorem raw_injection_iff (R : M.carrier → M.carrier → Prop) (A B : M.carrier) :
    RawInjection M R A B ↔ InjectionOn M R A B := by
  constructor
  · rintro ⟨⟨ht,hf⟩,hi⟩
    exact ⟨ht,fun x hx y z hxy hxz => hf x y z ⟨⟨hx,hxy⟩,hxz⟩,
      fun x u hx hu y hxy huy => hi x u y ⟨⟨⟨hx,hu⟩,hxy⟩,huy⟩⟩
  · intro h
    exact ⟨⟨h.total,fun x y z hh => h.functional x hh.1.1 y z hh.1.2 hh.2⟩,
      fun x u y hh => h.injective x u hh.1.1.1 hh.1.1.2 y hh.1.2 hh.2⟩

theorem realize_injects20 (v : ℕ → M.carrier) :
    Formula.Realize (SFormula.injects 2 0) v ↔
      ∃ f, InjectionOn M (KRel M f) (v 2) (v 0) := by
  have h : Formula.Realize (SFormula.injects 2 0) v ↔
      ∃ f, RawInjection M (KRel M f) (v 2) (v 0) := by
    simp only [SFormula.injects,SFormula.isInjection,SFormula.pairIn,SFormula.isPair,
      SFormula.isSingleton,SFormula.isDoubleton,realize_all,realize_ex,
      Formula.realize_inf,Formula.realize_imp,Formula.realize_iff,Formula.realize_sup,
      realize_mem,realize_eq,Function.update_apply,RawInjection,KRel,IsKPair,IsSingle,IsDouble]
    norm_num only
    simp only [ite_true,ite_false]
  exact h.trans (exists_congr (fun f => raw_injection_iff M _ _ _))

theorem realize_injects12 (v : ℕ → M.carrier) :
    Formula.Realize (SFormula.injects 1 2) v ↔
      ∃ f, InjectionOn M (KRel M f) (v 1) (v 2) := by
  have h : Formula.Realize (SFormula.injects 1 2) v ↔
      ∃ f, RawInjection M (KRel M f) (v 1) (v 2) := by
    simp only [SFormula.injects,SFormula.isInjection,SFormula.pairIn,SFormula.isPair,
      SFormula.isSingleton,SFormula.isDoubleton,realize_all,realize_ex,
      Formula.realize_inf,Formula.realize_imp,Formula.realize_iff,Formula.realize_sup,
      realize_mem,realize_eq,Function.update_apply,RawInjection,KRel,IsKPair,IsSingle,IsDouble]
    norm_num only
    simp only [ite_true,ite_false]
  exact h.trans (exists_congr (fun f => raw_injection_iff M _ _ _))

theorem close_at_const (φ : SFormula) (a : M.carrier) (h : M.carrier ⊨ SFormula.close φ) :
    Formula.Realize φ (fun _ => a) := by
  change Formula.Realize (SFormula.close φ) (default : Empty → M.carrier) at h
  rw [SFormula.close,Formula.realize_iAlls] at h
  have hh := Formula.realize_relabel.mp (h (fun _ => a))
  exact hh

variable (hZFC : Fol.all_realize_sentence M _root_.ZFC)
include hZFC

theorem omega_formula (v : ℕ → M.carrier) :
    Formula.Realize (SFormula.isOmega 0) (Function.update v 0 (Omega M)) := by
  simp only [SFormula.isOmega,SFormula.isInductive,SFormula.isEmpty,SFormula.isSucc,SFormula.subset,
    realize_all,realize_ex,Formula.realize_inf,Formula.realize_imp,Formula.realize_iff,
    Formula.realize_sup,Formula.realize_not,realize_mem,realize_eq,Function.update_apply]
  norm_num only
  simp only [ite_true,ite_false]
  change PureInd M (Omega M) ∧ ∀ I, PureInd M I → Sub M (Omega M) I
  exact ⟨(pure_ind_iff M hZFC _).mpr (omega_ind M hZFC),
    fun I hI => omega_least_ind M hZFC I ((pure_ind_iff M hZFC I).mp hI)⟩

theorem internal_CH (hCH : M.carrier ⊨ chSentence) (X : M.carrier)
    (hX : Sub M X (Power M (Omega M))) :
    (∃ f, InjectionOn M (KRel M f) X (Omega M)) ∨
      ∃ g, InjectionOn M (KRel M g) (Power M (Omega M)) X := by
  let v : ℕ → M.carrier := fun _ => EmptySet M
  have h := close_at_const M SFormula.ch (EmptySet M) hCH
  rw [SFormula.ch,realize_all] at h
  have hω := (Formula.realize_imp.mp (h (Omega M))) (omega_formula M hZFC v)
  rw [realize_all] at hω
  have hp : Formula.Realize (SFormula.isPowerset 1 0)
      (Function.update (Function.update v 0 (Omega M)) 1 (Power M (Omega M))) := by
    simp only [SFormula.isPowerset,SFormula.subset,realize_all,Formula.realize_iff,
      Formula.realize_imp,realize_mem,Function.update_apply]
    norm_num only
    simp only [ite_true,ite_false]
    exact power_spec M hZFC (Omega M)
  have hP := (Formula.realize_imp.mp (hω (Power M (Omega M)))) hp
  rw [realize_all] at hP
  have hsub : Formula.Realize (SFormula.subset 2 1)
      (Function.update (Function.update (Function.update v 0 (Omega M))
        1 (Power M (Omega M))) 2 X) := by
    simp only [SFormula.subset,realize_all,Formula.realize_imp,realize_mem,Function.update_apply]
    norm_num only
    simp only [ite_true,ite_false]
    exact hX
  have hc := (Formula.realize_imp.mp (hP X)) hsub
  rw [Formula.realize_sup,realize_injects20,realize_injects12] at hc
  simpa only [Function.update_self,
    Function.update_of_ne (show (0:ℕ) ≠ 1 by decide),
    Function.update_of_ne (show (0:ℕ) ≠ 2 by decide),
    Function.update_of_ne (show (1:ℕ) ≠ 2 by decide)] using hc

end
end ContinuumHypothesis.Cohen.CHTransfer
end

-- Development module: CohenCHBridge
section

/-!
The mission's CH sentence implies the native Flypitch CH sentence.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000
open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis.Cohen.CHTransfer
open CHFoundation
noncomputable section
variable (M : Fol.Structure L_ZFC) (hZFC : Fol.all_realize_sentence M _root_.ZFC)
local instance chBridgeStructure : setLang.Structure M.carrier := membershipReduct M
include hZFC

theorem comparison_CH_all (hCH : M.carrier ⊨ chSentence) (A : M.carrier) :
    NLe M A (Omega M) ∨ NLe M (Power M (Omega M)) A := by
  let B := Power M (Omega M)
  obtain ⟨f,hfsub,hfm,hcomp⟩ := partial_bijection_comparison M hZFC A B
  rcases hcomp with hft | hfs
  · have hp : D1 (fun y : M.carrier => ∃ x, Mem M x A ∧ KRel M f x y) := by
      apply ((((DTerm.var 2).mem (DTerm.const A)).and
        ((krel_definable M).apply (DTerm.const f) (DTerm.var 2) (DTerm.var 0))).ex 2).congr
      intro v
      simp only [Function.update_self,Function.update_of_ne (show (0:ℕ) ≠ 2 by decide)]
      rfl
    obtain ⟨X,hX⟩ := definable_separation M hZFC hp B
    have hXB : Sub M X B := fun y hy => ((hX y).mp hy).1
    rcases internal_CH M hZFC hCH X hXB with ⟨g,hg⟩ | ⟨g,hg⟩
    · apply Or.inl
      let R := fun x y : M.carrier => ∃ z, Mem M z X ∧ KRel M f x z ∧ KRel M g z y
      have hR : D2 R := by
        apply ((((DTerm.var 2).mem (DTerm.const X)).and
          (((krel_definable M).apply (DTerm.const f) (DTerm.var 0) (DTerm.var 2)).and
            ((krel_definable M).apply (DTerm.const g) (DTerm.var 2) (DTerm.var 1)))).ex 2).congr
        intro v
        simp only [Function.update_self,
          Function.update_of_ne (show (0:ℕ) ≠ 2 by decide),
          Function.update_of_ne (show (1:ℕ) ≠ 2 by decide)]
        rfl
      apply nle_of_definable_injection M hZFC hR A (Omega M)
      constructor
      · intro x hx
        obtain ⟨z,hzB,hxz⟩ := hft x hx
        have hzX := (hX z).mpr ⟨hzB,x,hx,hxz⟩
        obtain ⟨y,hyW,hzy⟩ := hg.total z hzX
        exact ⟨y,hyW,z,hzX,hxz,hzy⟩
      · intro x hx y u hxy hxu
        obtain ⟨z,hz,hxz,hzy⟩ := hxy
        obtain ⟨w,hw,hxw,hwu⟩ := hxu
        have heq := matching_functional M hZFC hfm hxz hxw
        subst w
        exact hg.functional z hz y u hzy hwu
      · intro x u hx hu y hxy huy
        obtain ⟨z,hz,hxz,hzy⟩ := hxy
        obtain ⟨w,hw,huw,hwy⟩ := huy
        have heq := hg.injective z w hz hw y hzy hwy
        subst w
        exact matching_injective M hZFC hfm hxz huw
    · apply Or.inr
      let R := fun x y : M.carrier => ∃ z, Mem M z X ∧ KRel M g x z ∧ KRel M f y z
      have hR : D2 R := by
        apply ((((DTerm.var 2).mem (DTerm.const X)).and
          (((krel_definable M).apply (DTerm.const g) (DTerm.var 0) (DTerm.var 2)).and
            ((krel_definable M).apply (DTerm.const f) (DTerm.var 1) (DTerm.var 2)))).ex 2).congr
        intro v
        simp only [Function.update_self,
          Function.update_of_ne (show (0:ℕ) ≠ 2 by decide),
          Function.update_of_ne (show (1:ℕ) ≠ 2 by decide)]
        rfl
      apply nle_of_definable_injection M hZFC hR B A
      constructor
      · intro x hx
        obtain ⟨z,hz,hxz⟩ := hg.total x hx
        obtain ⟨y,hy,hyz⟩ := ((hX z).mp hz).2
        exact ⟨y,hy,z,hz,hxz,hyz⟩
      · intro x hx y u hxy hxu
        obtain ⟨z,hz,hxz,hyz⟩ := hxy
        obtain ⟨w,hw,hxw,huw⟩ := hxu
        have heq := hg.functional x hx z w hxz hxw
        subst w
        exact matching_injective M hZFC hfm hyz huw
      · intro x u hx hu y hxy huy
        obtain ⟨z,hz,hxz,hyz⟩ := hxy
        obtain ⟨w,hw,huw,hyw⟩ := huy
        have heq := matching_functional M hZFC hfm hyz hyw
        subst w
        exact hg.injective x u hx hu z hxz huw
  · apply Or.inr
    have hR : D2 (fun x y : M.carrier => KRel M f y x) :=
      (krel_definable M).apply (DTerm.const f) (DTerm.var 1) (DTerm.var 0)
    apply nle_of_definable_injection M hZFC hR B A
    exact ⟨hfs,
      fun x hx y z hy hz => matching_injective M hZFC hfm hy hz,
      fun x u hx hu y hy hz => matching_functional M hZFC hfm hy hz⟩

theorem bridge (hCH : M.carrier ⊨ chSentence) : Fol.realize_sentence M CH_f := by
  apply (native_CH_iff M).mpr
  intro A _
  exact comparison_CH_all M hZFC hCH A

end
end ContinuumHypothesis.Cohen.CHTransfer
end

open FirstOrder FirstOrder.Language

theorem solution
    (M : Fol.Structure _root_.L_ZFC) (hM : Nonempty M.carrier)
    (hZFC : Fol.all_realize_sentence M _root_.ZFC)
    (hCH : letI : ContinuumHypothesis.setLang.Structure M.carrier :=
        ContinuumHypothesis.Cohen.membershipReduct M
      M.carrier ⊨ ContinuumHypothesis.chSentence) :
    Fol.realize_sentence M _root_.CH_f := by
  exact ContinuumHypothesis.Cohen.CHTransfer.bridge M hZFC hCH
