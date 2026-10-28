-- Prove2me | solution 1 for ContinuumHypothesis.Cohen.membership_reduct_models_ZFC
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T03:52:15.559087+00:00
-- url     : https://prove2.me/submissions/807cff2a-6874-4efc-b54d-39c0047713ff

import Definitions.Def_CH_Cohen_Reduct
import Mathlib.ModelTheory.Definability

/-!
The membership reduct of every native Flypitch ZFC model satisfies the
mission's exact ZFC theory.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

Native syntax/axioms and reused semantic proof patterns:
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the original LICENSE.
Authors: Jesse Han, Floris van Doorn.
Lean 4 port: Ian Klatzco, Claude.

Reference: Han and van Doorn, CPP 2020, section 2.2, Figure 1, and section 7.
https://florisvandoorn.com/papers/flypitch-cpp-2020.pdf
The membership-language transfer below is an additional construction.
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

namespace ContinuumHypothesis.Cohen.Transfer

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

end ContinuumHypothesis.Cohen.Transfer
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
namespace ContinuumHypothesis.Cohen.Transfer

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
end ContinuumHypothesis.Cohen.Transfer
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

namespace ContinuumHypothesis.Cohen.Transfer

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

end ContinuumHypothesis.Cohen.Transfer
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
namespace ContinuumHypothesis.Cohen.Transfer
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
end ContinuumHypothesis.Cohen.Transfer
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
namespace ContinuumHypothesis.Cohen.Transfer
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
end ContinuumHypothesis.Cohen.Transfer
end

-- Development module: CohenTransferChoice
section

/-!
Choice sets from the native Zorn axiom, using partial choice sets.

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
namespace ContinuumHypothesis.Cohen.Transfer
noncomputable section

variable (M : Fol.Structure L_ZFC) (hZFC : Fol.all_realize_sentence M _root_.ZFC)
local instance : setLang.Structure M.carrier := membershipReduct M

def AtMost (X c : M.carrier) : Prop :=
  ∀ a, Mem M a X → ∀ y, Mem M y a → ∀ z, Mem M z a →
    Mem M y c → Mem M z c → y = z

theorem atMost_definable (X : M.carrier) : D1 (AtMost M X) := by
  have h :=
    ((DTerm.var 1).mem (DTerm.const X)).imp
      (((DTerm.var 2).mem (DTerm.var 1)).imp
        (((DTerm.var 3).mem (DTerm.var 1)).imp
          (((DTerm.var 2).mem (DTerm.var 0)).imp
            (((DTerm.var 3).mem (DTerm.var 0)).imp
              ((DTerm.var 2).eq (DTerm.var 3))))))
  apply (((h.all 3).all 2).all 1).congr
  intro v
  simp only [Function.update_self,
    Function.update_of_ne (show (0:ℕ) ≠ 1 by decide),
    Function.update_of_ne (show (0:ℕ) ≠ 2 by decide),
    Function.update_of_ne (show (0:ℕ) ≠ 3 by decide),
    Function.update_of_ne (show (1:ℕ) ≠ 2 by decide),
    Function.update_of_ne (show (1:ℕ) ≠ 3 by decide),
    Function.update_of_ne (show (2:ℕ) ≠ 3 by decide)]
  change (∀ a y z, Mem M a X → Mem M y a → Mem M z a →
    Mem M y (v 0) → Mem M z (v 0) → y = z) ↔ AtMost M X (v 0)
  unfold AtMost
  constructor
  · intro h a ha y hy z hz; exact h a y z ha hy hz
  · intro h a y z ha hy hz; exact h a ha y hy z hz

include hZFC

theorem choice_set (X : M.carrier)
    (hne : ∀ a, Mem M a X → ∃ y, Mem M y a)
    (hdisj : ∀ a, Mem M a X → ∀ b, Mem M b X → a ≠ b →
      ¬∃ y, Mem M y a ∧ Mem M y b) :
    ∃ c, ∀ a, Mem M a X →
      ∃ y, Mem M y a ∧ Mem M y c ∧ ∀ z, Mem M z a ∧ Mem M z c → z = y := by
  let U := Union M X
  obtain ⟨p, hp⟩ := definable_separation M hZFC (atMost_definable M X) (Power M U)
  have hp' (c : M.carrier) : Mem M c p ↔ Sub M c U ∧ AtMost M X c :=
    (hp c).trans (and_congr (power_spec M hZFC U c) Iff.rfl)
  have hEp : Mem M (EmptySet M) p := (hp' _).mpr ⟨
    fun z hz => (empty_spec M hZFC z hz).elim,
    fun _ _ _ _ _ _ hy => (empty_spec M hZFC _ hy).elim⟩
  have hpne : p ≠ EmptySet M := nonempty_ne_empty M hZFC hEp
  have hchains (C : M.carrier) (hCp : Sub M C p)
      (hchain : ∀ a, Mem M a C → ∀ b, Mem M b C → Sub M a b ∨ Sub M b a) :
      Mem M (Union M C) p := by
    apply (hp' _).mpr
    constructor
    · intro z hz
      obtain ⟨c, hcC, hzc⟩ := (union_spec M hZFC C z).mp hz
      exact ((hp' c).mp (hCp c hcC)).1 z hzc
    · intro a ha y hya z hza hyC hzC
      obtain ⟨c, hcC, hyc⟩ := (union_spec M hZFC C y).mp hyC
      obtain ⟨d, hdC, hzd⟩ := (union_spec M hZFC C z).mp hzC
      rcases hchain c hcC d hdC with hcd | hdc
      · exact ((hp' d).mp (hCp d hdC)).2 a ha y hya z hza (hcd y hyc) hzd
      · exact ((hp' c).mp (hCp c hcC)).2 a ha y hya z hza hyc (hdc z hzd)
  obtain ⟨c, hcp, hmax⟩ := zorn_spec M hZFC p hpne hchains
  have hc := (hp' c).mp hcp
  refine ⟨c, ?_⟩
  intro a ha
  by_cases he : ∃ y, Mem M y a ∧ Mem M y c
  · obtain ⟨y, hya, hyc⟩ := he
    exact ⟨y, hya, hyc, fun z hz => hc.2 a ha z hz.1 y hya hz.2 hyc⟩
  · obtain ⟨y, hya⟩ := hne a ha
    have hyn : ¬Mem M y c := fun hyc => he ⟨y,hya,hyc⟩
    have hyU : Mem M y U := (union_spec M hZFC X y).mpr ⟨a,ha,hya⟩
    let d := Insert M hZFC y c
    have hd : Mem M d p := by
      apply (hp' d).mpr
      constructor
      · intro z hz
        rcases (insert_spec M hZFC y c z).mp hz with hzc | rfl
        · exact hc.1 z hzc
        · exact hyU
      · intro b hb u hub v hvb hud hvd
        have hmiss (z : M.carrier) (hzb : Mem M z b) (hzc : Mem M z c)
            (hyb : Mem M y b) : False := by
          have hba : b = a := by
            by_contra hba
            exact hdisj b hb a ha hba ⟨y,hyb,hya⟩
          exact he ⟨z, hba ▸ hzb, hzc⟩
        rcases (insert_spec M hZFC y c u).mp hud with huc | huy
        · rcases (insert_spec M hZFC y c v).mp hvd with hvc | hvy
          · exact hc.2 b hb u hub v hvb huc hvc
          · subst v
            exact (hmiss u hub huc hvb).elim
        · subst u
          rcases (insert_spec M hZFC y c v).mp hvd with hvc | hvy
          · exact (hmiss v hvb hvc hub).elim
          · exact hvy.symm
    have hcd : Sub M c d := fun z hz => (insert_spec M hZFC y c z).mpr (Or.inl hz)
    have hcdEq := hmax d hd hcd
    have hyd : Mem M y d := (insert_spec M hZFC y c y).mpr (Or.inr rfl)
    rw [←hcdEq] at hyd
    exact (hyn hyd).elim

end
end ContinuumHypothesis.Cohen.Transfer
end

-- Development module: CohenTransferModel
section

/-!
The reduct satisfies the mission's exact ZFC sentences and schemas.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
open FirstOrder FirstOrder.Language
namespace ContinuumHypothesis.Cohen.Transfer
noncomputable section

section Generic
variable {A : Type*} [setLang.Structure A]

theorem formula_congr (φ : SFormula) {v w : ℕ → A}
    (h : ∀ i ∈ φ.freeVarFinset, v i = w i) : Formula.Realize φ v ↔ Formula.Realize φ w := by
  have he : (fun i : φ.freeVarFinset => v i.val) = (fun i : φ.freeVarFinset => w i.val) :=
    funext (fun i => h i.val i.property)
  have hv := BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id)
    (v := fun i : φ.freeVarFinset => v i.val) (xs := Fin.elim0) v (fun _ => rfl)
  have hw := BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id)
    (v := fun i : φ.freeVarFinset => w i.val) (xs := Fin.elim0) w (fun _ => rfl)
  rw [←he] at hw
  exact hv.symm.trans hw

theorem formula_subst_definable (φ : SFormula) (f : ℕ → setLang[[A]].Term ℕ) :
    PDef (fun v : ℕ → A => Formula.Realize φ (fun i => (f i).realize v)) := by
  refine ⟨((setLang.lhomWithConstants A).onFormula φ).subst f, ?_⟩
  intro v
  change BoundedFormula.Realize _ v Fin.elim0 ↔ _
  rw [BoundedFormula.realize_subst]
  exact (setLang.lhomWithConstants A).realize_onFormula φ

theorem formula_D1 (φ : SFormula) (v : ℕ → A) (x : ℕ) :
    D1 (fun z => Formula.Realize φ (Function.update v x z)) := by
  classical
  let f : ℕ → setLang[[A]].Term ℕ := fun i => if i = x then pvar 0 else pconst (v i)
  apply (formula_subst_definable φ f).congr
  intro w
  have he : (fun i => (f i).realize w) = Function.update v x (w 0) := by
    funext i
    by_cases hi : i = x
    · subst i; simp only [f, ↓reduceIte, pvar_realize, Function.update_self]
    · simp only [f, hi, ↓reduceIte, pconst_realize, Function.update_of_ne hi]
  rw [he]

theorem formula_D2 (φ : SFormula) (v : ℕ → A) (x y : ℕ) :
    D2 (fun z w => Formula.Realize φ (Function.update (Function.update v x z) y w)) := by
  classical
  let f : ℕ → setLang[[A]].Term ℕ := fun i =>
    if i = y then pvar 1 else if i = x then pvar 0 else pconst (v i)
  apply (formula_subst_definable φ f).congr
  intro w
  have he : (fun i => (f i).realize w) = Function.update (Function.update v x (w 0)) y (w 1) := by
    funext i
    by_cases hiy : i = y
    · subst i; simp only [f, ↓reduceIte, pvar_realize, Function.update_self]
    · by_cases hix : i = x
      · subst i
        simp only [f, hiy, ↓reduceIte, pvar_realize, Function.update_of_ne hiy, Function.update_self]
      · simp only [f, hiy, hix, ↓reduceIte, pconst_realize,
          Function.update_of_ne hiy, Function.update_of_ne hix]
  rw [he]

theorem sf_all (v : ℕ → A) (i : ℕ) (φ : SFormula) :
    Formula.Realize (SFormula.all i φ) v ↔ ∀ z, Formula.Realize φ (Function.update v i z) :=
  namedAll_realize φ i v

theorem sf_ex (v : ℕ → A) (i : ℕ) (φ : SFormula) :
    Formula.Realize (SFormula.ex i φ) v ↔ ∃ z, Formula.Realize φ (Function.update v i z) :=
  namedEx_realize φ i v

theorem close_of_all (φ : SFormula) (h : ∀ v : ℕ → A, Formula.Realize φ v) :
    A ⊨ SFormula.close φ := by
  change Formula.Realize (SFormula.close φ) (default : Empty → A)
  rw [SFormula.close, Formula.realize_iAlls]
  intro v
  exact Formula.realize_relabel.mpr (h _)

end Generic

variable (M : Fol.Structure L_ZFC) (hZFC : Fol.all_realize_sentence M _root_.ZFC)
local instance : setLang.Structure M.carrier := membershipReduct M
include hZFC

omit hZFC in
theorem sf_mem (v : ℕ → M.carrier) (i j : ℕ) :
    Formula.Realize (SFormula.mem i j) v ↔ Mem M (v i) (v j) := Iff.rfl

omit hZFC in
theorem sf_eq (v : ℕ → M.carrier) (i j : ℕ) :
    Formula.Realize (SFormula.eq i j) v ↔ v i = v j := Iff.rfl

theorem models_extensionality : M.carrier ⊨ SFormula.close SFormula.extensionality := by
  apply close_of_all
  intro v
  simp only [SFormula.extensionality, sf_all, Formula.realize_imp, Formula.realize_iff,
    sf_mem, sf_eq, Function.update_apply]
  norm_num only
  exact ext_spec M hZFC

theorem models_foundation : M.carrier ⊨ SFormula.close SFormula.foundation := by
  apply close_of_all
  intro v
  simp only [SFormula.foundation, sf_all, sf_ex, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_not, sf_mem, Function.update_apply]
  norm_num only
  intro a ⟨x,hxa⟩
  obtain ⟨y,hya,hy⟩ := regularity_spec M hZFC a (nonempty_ne_empty M hZFC hxa)
  exact ⟨y,hya,fun ⟨z,hzy,hza⟩ => hy z hza hzy⟩

theorem models_pairing : M.carrier ⊨ SFormula.close SFormula.pairing := by
  apply close_of_all
  intro v
  simp only [SFormula.pairing, SFormula.isDoubleton, sf_all, sf_ex, Formula.realize_iff,
    Formula.realize_sup, sf_mem, sf_eq, Function.update_apply]
  norm_num only
  exact pairing_exists M hZFC

theorem models_union : M.carrier ⊨ SFormula.close SFormula.union := by
  apply close_of_all
  intro v
  simp only [SFormula.union, sf_all, sf_ex, Formula.realize_iff, Formula.realize_inf,
    sf_mem, Function.update_apply]
  norm_num only
  intro a
  exact ⟨Union M a, union_spec M hZFC a⟩

theorem models_powerset : M.carrier ⊨ SFormula.close SFormula.powerset := by
  apply close_of_all
  intro v
  simp only [SFormula.powerset, SFormula.isPowerset, SFormula.subset,
    sf_all, sf_ex, Formula.realize_iff, Formula.realize_imp, sf_mem, Function.update_apply]
  norm_num only
  intro a
  exact ⟨Power M a, power_spec M hZFC a⟩

theorem models_infinity : M.carrier ⊨ SFormula.close SFormula.infinity := by
  apply close_of_all
  intro v
  simp only [SFormula.infinity, SFormula.isInductive, SFormula.isEmpty, SFormula.isSucc,
    sf_all, sf_ex, Formula.realize_inf, Formula.realize_imp, Formula.realize_iff,
    Formula.realize_sup, Formula.realize_not, sf_mem, sf_eq, Function.update_apply]
  norm_num only
  exact ⟨Omega M, ⟨EmptySet M, empty_spec M hZFC, (infinity_spec M hZFC).1.1⟩,
    omega_successor M hZFC⟩

theorem models_choice : M.carrier ⊨ acSentence := by
  apply close_of_all
  intro v
  simp only [SFormula.choice, sf_all, sf_ex, Formula.realize_inf, Formula.realize_imp,
    Formula.realize_not, sf_mem, sf_eq, Function.update_apply]
  norm_num only
  intro X hX
  obtain ⟨c,hc⟩ := choice_set M hZFC X hX.1
    (fun a ha b hb hab => hX.2 a b ⟨⟨ha,hb⟩,hab⟩)
  refine ⟨c, fun a ha => ?_⟩
  obtain ⟨y,hya,hyc,hy⟩ := hc a ha
  exact ⟨y,⟨hya,hyc⟩,hy⟩

theorem models_separation (σ : SFormula) (hσ : SFormula.IsSeparation σ) :
    M.carrier ⊨ SFormula.close σ := by
  classical
  obtain ⟨φ,x,a,b,hxa,hxb,hab,hb,rfl⟩ := hσ
  apply close_of_all
  intro v
  rw [sf_all]
  intro A
  let w := Function.update v a A
  obtain ⟨B,hB⟩ := definable_separation M hZFC (formula_D1 φ w x) A
  rw [sf_ex]
  refine ⟨B, ?_⟩
  rw [sf_all]
  intro X
  rw [Formula.realize_iff, sf_mem, Formula.realize_inf, sf_mem]
  have hf : Formula.Realize φ (Function.update (Function.update w b B) x X) ↔
      Formula.Realize φ (Function.update w x X) := by
    apply formula_congr
    intro i hi
    have hib : i ≠ b := fun h => hb (h ▸ hi)
    by_cases hix : i = x
    · subst i; simp only [Function.update_self]
    · simp only [Function.update_of_ne hix, Function.update_of_ne hib]
  simpa only [w, Function.update_self, Function.update_of_ne hxb, Function.update_of_ne hxb.symm,
    Function.update_of_ne hxa, Function.update_of_ne hxa.symm, Function.update_of_ne hab, hf] using hB X

theorem models_replacement (σ : SFormula) (hσ : SFormula.IsReplacement σ) :
    M.carrier ⊨ SFormula.close σ := by
  classical
  obtain ⟨φ,x,y,y',a,b,hnd,hb,hy',rfl⟩ := hσ
  have hxnot := (List.nodup_cons.mp hnd).1
  have hynot := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hxa : x ≠ a := fun h => hxnot (by simp only [List.mem_cons, List.mem_singleton]; tauto)
  have hxb : x ≠ b := fun h => hxnot (by simp only [List.mem_cons, List.mem_singleton]; tauto)
  have hyb : y ≠ b := fun h => hynot (by simp only [List.mem_cons, List.mem_singleton]; tauto)
  have hab : a ≠ b := by
    have h := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).2
    exact (List.pairwise_cons.mp h).1 b (by exact List.mem_singleton.mpr rfl)
  apply close_of_all
  intro v
  rw [sf_all]
  intro A
  rw [Formula.realize_imp]
  intro hfun
  let w := Function.update v a A
  let R := fun X Y : M.carrier => Formula.Realize φ (Function.update (Function.update w x X) y Y)
  have ht : ∀ X, Mem M X A → ∃ Y, R X Y := by
    intro X hXA
    have hh := (sf_all _ _ _).mp hfun X
    rw [Formula.realize_imp] at hh
    have hh' := hh (by simpa only [sf_mem, Function.update_self,
      Function.update_of_ne hxa.symm] using hXA)
    obtain ⟨Y,hY⟩ := (sf_ex _ _ _).mp hh'
    exact ⟨Y,(Formula.realize_inf.mp hY).1⟩
  obtain ⟨B,hB,_⟩ := definable_collection M hZFC (formula_D2 φ w x y) A ht
  rw [sf_ex]
  refine ⟨B, ?_⟩
  rw [sf_all]
  intro X
  rw [Formula.realize_imp, sf_mem]
  intro hX
  have hXA : Mem M X A := by
    simpa only [w, Function.update_self, Function.update_of_ne hxb,
      Function.update_of_ne hxa.symm, Function.update_of_ne hab] using hX
  obtain ⟨Y,hY,hφ⟩ := hB X hXA
  rw [sf_ex]
  refine ⟨Y, ?_⟩
  rw [Formula.realize_inf, sf_mem]
  constructor
  · simpa only [Function.update_self, Function.update_of_ne hyb.symm,
      Function.update_of_ne hxb.symm] using hY
  · apply (formula_congr φ (v := Function.update (Function.update (Function.update w b B) x X) y Y)
      (w := Function.update (Function.update w x X) y Y) ?_).mpr hφ
    intro i hi
    have hib : i ≠ b := fun h => hb (h ▸ hi)
    by_cases hiy : i = y
    · subst i; simp only [Function.update_self]
    · by_cases hix : i = x
      · subst i; simp only [Function.update_of_ne hiy, Function.update_self]
      · simp only [Function.update_of_ne hiy, Function.update_of_ne hix,
          Function.update_of_ne hib]

theorem models_ZF : M.carrier ⊨ ContinuumHypothesis.ZF := by
  constructor
  intro τ hτ
  change τ ∈ SFormula.close '' SFormula.ZFAxioms at hτ
  obtain ⟨σ,hσ,rfl⟩ := hτ
  rcases hσ with (hbase | hsep) | hrep
  · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hbase
    rcases hbase with rfl | rfl | rfl | rfl | rfl | rfl
    · exact models_extensionality M hZFC
    · exact models_foundation M hZFC
    · exact models_pairing M hZFC
    · exact models_union M hZFC
    · exact models_powerset M hZFC
    · exact models_infinity M hZFC
  · exact models_separation M hZFC σ hsep
  · exact models_replacement M hZFC σ hrep

theorem models_ZFC : M.carrier ⊨ ContinuumHypothesis.ZFC := by
  constructor
  intro σ hσ
  rcases hσ with hσ | hσ
  · exact (models_ZF M hZFC).realize_of_mem σ hσ
  · have hs : σ = acSentence := Set.mem_singleton_iff.mp hσ
    subst σ
    exact models_choice M hZFC

end
end ContinuumHypothesis.Cohen.Transfer
end

open FirstOrder FirstOrder.Language

theorem solution
    (M : Fol.Structure _root_.L_ZFC) (hM : Nonempty M.carrier)
    (hZFC : Fol.all_realize_sentence M _root_.ZFC) :
    letI : ContinuumHypothesis.setLang.Structure M.carrier :=
      ContinuumHypothesis.Cohen.membershipReduct M
    M.carrier ⊨ ContinuumHypothesis.ZFC := by
  exact ContinuumHypothesis.Cohen.Transfer.models_ZFC M hZFC
