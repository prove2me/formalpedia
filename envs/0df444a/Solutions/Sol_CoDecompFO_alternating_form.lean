-- Prove2me | solution 1 for CoDecompFO.alternating_form
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:04:04.663201+00:00
-- url     : https://prove2.me/submissions/3e02103a-53ef-4928-914c-44f0726b41f7

import Mathlib
import Definitions.Def_CoDecompFO_AltSat
import Definitions.Def_CoDecompFO_Codes

set_option autoImplicit false

namespace CoDecompFO
namespace AF

open FirstOrder FirstOrder.Language

variable {σ : Sig}

/-! ### The transform on formulas -/

/-- The number of quantifiers of a formula. -/
def nall : {n : ℕ} → σ.lang.BoundedFormula Empty n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp f g => nall f + nall g
  | _, .all f => nall f + 1

/-- The symbol `∘` of `σ` with `∘`. -/
def circRel (σ : Sig) : (sigmaEq σ).lang.Relations 2 := ⟨(0 : Fin (σ.r + 1)), rfl⟩

/-- A symbol of `σ`, as a symbol of `σ` with `∘`. -/
def liftRel {a : ℕ} (R : σ.lang.Relations a) : (sigmaEq σ).lang.Relations a := ⟨R.1.succ, R.2⟩

/-- Renaming the variable of a term through an environment. -/
def trTerm {n k : ℕ} (env : Fin n → Fin k) :
    σ.lang.Term (Empty ⊕ Fin n) → (sigmaEq σ).lang.Term (Empty ⊕ Fin k)
  | .var (.inl e) => e.elim
  | .var (.inr j) => .var (.inr (env j))
  | .func f _ => nomatch (show Empty from f)

/-- The matrix of the alternating form of `f`. The quantifiers of `f` are numbered in pre-order from
`q`; the quantifier number `p` binds position `2p` if it is universal in the prefix (`neg = false`) and
`2p + 1` if it is existential. -/
def tr (k : ℕ) : {n : ℕ} → (f : σ.lang.BoundedFormula Empty n) → (env : Fin n → Fin k) → (q : ℕ) →
    (neg : Bool) → (h : 2 * (q + nall f) ≤ k) → (sigmaEq σ).lang.BoundedFormula Empty k
  | _, .falsum, _, _, _, _ => .falsum
  | _, .equal t₁ t₂, env, _, _, _ => .rel (circRel σ) ![trTerm env t₁, trTerm env t₂]
  | _, .rel R ts, env, _, _, _ => .rel (liftRel R) (fun j => trTerm env (ts j))
  | _, .imp f g, env, q, neg, h =>
      .imp (tr k f env q (!neg) (by simp only [nall] at h; omega))
        (tr k g env (q + nall f) neg (by simp only [nall] at h; omega))
  | _, .all f, env, q, neg, h =>
      tr k f (Fin.snoc (α := fun _ => Fin k) env
        ⟨2 * q + neg.toNat, by have := neg.toNat_lt; simp only [nall] at h; omega⟩)
        (q + 1) neg (by simp only [nall] at h; omega)

theorem tr_isQF (k : ℕ) : ∀ {n : ℕ} (f : σ.lang.BoundedFormula Empty n) (env : Fin n → Fin k) (q : ℕ)
    (neg : Bool) (h : 2 * (q + nall f) ≤ k), (tr k f env q neg h).IsQF := by
  intro n f
  induction f with
  | falsum => intro env q neg h; exact BoundedFormula.IsQF.falsum
  | equal t₁ t₂ =>
      intro env q neg h
      exact BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.rel _ _)
  | rel R ts =>
      intro env q neg h
      exact BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.rel _ _)
  | imp f g ihf ihg =>
      intro env q neg h
      exact BoundedFormula.IsQF.imp (ihf _ _ _ _) (ihg _ _ _ _)
  | all f ih =>
      intro env q neg h
      exact ih _ _ _ _

theorem tr_eqFree (k : ℕ) : ∀ {n : ℕ} (f : σ.lang.BoundedFormula Empty n) (env : Fin n → Fin k)
    (q : ℕ) (neg : Bool) (h : 2 * (q + nall f) ≤ k), EqFree (tr k f env q neg h) := by
  intro n f
  induction f with
  | falsum => intro env q neg h; exact trivial
  | equal t₁ t₂ => intro env q neg h; exact trivial
  | rel R ts => intro env q neg h; exact trivial
  | imp f g ihf ihg =>
      intro env q neg h
      exact ⟨ihf _ _ _ _, ihg _ _ _ _⟩
  | all f ih =>
      intro env q neg h
      exact ih _ _ _ _

theorem nall_le : ∀ {n : ℕ} (f : σ.lang.BoundedFormula Empty n), nall f ≤ sentLen f := by
  intro n f
  induction f with
  | falsum => simp [nall]
  | equal t₁ t₂ => simp [nall]
  | rel R ts => simp [nall]
  | imp f g ihf ihg =>
      simp only [nall, sentLen, encF, List.length_cons, List.length_append] at *
      omega
  | all f ih =>
      simp only [nall, sentLen, encF, List.length_cons] at *
      omega

theorem tr_len (k : ℕ) : ∀ {n : ℕ} (f : σ.lang.BoundedFormula Empty n) (env : Fin n → Fin k)
    (q : ℕ) (neg : Bool) (h : 2 * (q + nall f) ≤ k),
    sentLen (tr k f env q neg h) ≤ 2 * sentLen f := by
  intro n f
  induction f with
  | falsum => intro env q neg h; simp [tr, sentLen, encF]
  | equal t₁ t₂ => intro env q neg h; simp [tr, sentLen, encF]
  | rel R ts => intro env q neg h; simp [tr, sentLen, encF]
  | imp f g ihf ihg =>
      intro env q neg h
      have h1 := ihf env q (!neg) (by simp only [nall] at h; omega)
      have h2 := ihg env (q + nall f) neg (by simp only [nall] at h; omega)
      simp only [tr, sentLen, encF, List.length_cons, List.length_append] at *
      omega
  | all f ih =>
      intro env q neg h
      have h1 := ih (Fin.snoc (α := fun _ => Fin k) env
        ⟨2 * q + neg.toNat, by have := neg.toNat_lt; simp only [nall] at h; omega⟩)
        (q + 1) neg (by simp only [nall] at h; omega)
      simp only [tr, sentLen, encF, List.length_cons] at *
      omega

/-! ### Alternating prefixes over lists -/

/-- `m` rounds of `∀∃` (`neg = false`) or `∃∀` (`neg = true`) over extensions of a list. -/
def AltB {M : Type} : Bool → (List M → Prop) → ℕ → List M → Prop
  | _, P, 0, l => P l
  | false, P, m + 1, l => ∀ x : M, ∃ y : M, AltB false P m (l ++ [x, y])
  | true, P, m + 1, l => ∃ x : M, ∀ y : M, AltB true P m (l ++ [x, y])

theorem AltB_zero {M : Type} (b : Bool) (P : List M → Prop) (l : List M) :
    AltB b P 0 l ↔ P l := by
  cases b <;> exact Iff.rfl

theorem AltB_congr {M : Type} (b : Bool) (P Q : List M → Prop) :
    ∀ (m : ℕ) (l : List M), (∀ e : List M, e.length = 2 * m → (P (l ++ e) ↔ Q (l ++ e))) →
      (AltB b P m l ↔ AltB b Q m l) := by
  intro m
  induction m with
  | zero =>
      intro l h
      rw [AltB_zero, AltB_zero]
      simpa using h [] rfl
  | succ m ih =>
      intro l h
      have key : ∀ x y : M, AltB b P m (l ++ [x, y]) ↔ AltB b Q m (l ++ [x, y]) := by
        intro x y
        apply ih
        intro e he
        have := h ([x, y] ++ e) (by simp [he]; omega)
        simpa [List.append_assoc] using this
      cases b
      · exact forall_congr' fun x => exists_congr fun y => key x y
      · exact exists_congr fun x => forall_congr' fun y => key x y

theorem AltB_add {M : Type} (b : Bool) (P : List M → Prop) (n₂ : ℕ) :
    ∀ (n₁ : ℕ) (l : List M),
      AltB b P (n₁ + n₂) l ↔ AltB b (fun l' => AltB b P n₂ l') n₁ l := by
  intro n₁
  induction n₁ with
  | zero =>
      intro l
      rw [Nat.zero_add, AltB_zero]
  | succ n₁ ih =>
      intro l
      rw [Nat.succ_add]
      cases b
      · exact forall_congr' fun x => exists_congr fun y => ih _
      · exact exists_congr fun x => forall_congr' fun y => ih _

theorem pull_left {M : Type} [Nonempty M] (b : Bool) (A : List M → Prop) (C : Prop) :
    ∀ (n : ℕ) (l : List M),
      (AltB (!b) A n l → C) ↔ AltB b (fun l' => A l' → C) n l := by
  intro n
  induction n with
  | zero =>
      intro l
      rw [AltB_zero, AltB_zero]
  | succ n ih =>
      intro l
      obtain ⟨d⟩ := ‹Nonempty M›
      cases b
      · show ((∃ x : M, ∀ y : M, AltB true A n (l ++ [x, y])) → C) ↔
          ∀ x : M, ∃ y : M, AltB false (fun l' => A l' → C) n (l ++ [x, y])
        constructor
        · intro h x
          by_cases hx : ∀ y : M, AltB true A n (l ++ [x, y])
          · exact ⟨d, (ih (l ++ [x, d])).1 (fun _ => h ⟨x, hx⟩)⟩
          · push Not at hx
            obtain ⟨y, hy⟩ := hx
            exact ⟨y, (ih (l ++ [x, y])).1 (fun hp => absurd hp hy)⟩
        · rintro h ⟨x, hx⟩
          obtain ⟨y, hy⟩ := h x
          exact (ih (l ++ [x, y])).2 hy (hx y)
      · show ((∀ x : M, ∃ y : M, AltB false A n (l ++ [x, y])) → C) ↔
          ∃ x : M, ∀ y : M, AltB true (fun l' => A l' → C) n (l ++ [x, y])
        constructor
        · intro h
          by_cases hC : C
          · exact ⟨d, fun y => (ih (l ++ [d, y])).1 (fun _ => hC)⟩
          · have hn : ¬ ∀ x : M, ∃ y : M, AltB false A n (l ++ [x, y]) := fun hh => hC (h hh)
            push Not at hn
            obtain ⟨x, hx⟩ := hn
            exact ⟨x, fun y => (ih (l ++ [x, y])).1 (fun hp => absurd hp (hx y))⟩
        · rintro ⟨x, hx⟩ h
          obtain ⟨y, hy⟩ := h x
          exact (ih (l ++ [x, y])).2 (hx y) hy

theorem pull_right {M : Type} [Nonempty M] (b : Bool) (A : Prop) (B : List M → Prop) :
    ∀ (n : ℕ) (l : List M),
      (A → AltB b B n l) ↔ AltB b (fun l' => A → B l') n l := by
  intro n
  induction n with
  | zero =>
      intro l
      rw [AltB_zero, AltB_zero]
  | succ n ih =>
      intro l
      obtain ⟨d⟩ := ‹Nonempty M›
      cases b
      · show (A → ∀ x : M, ∃ y : M, AltB false B n (l ++ [x, y])) ↔
          ∀ x : M, ∃ y : M, AltB false (fun l' => A → B l') n (l ++ [x, y])
        constructor
        · intro h x
          by_cases hA : A
          · obtain ⟨y, hy⟩ := h hA x
            exact ⟨y, (ih (l ++ [x, y])).1 (fun _ => hy)⟩
          · exact ⟨d, (ih (l ++ [x, d])).1 (fun a => absurd a hA)⟩
        · intro h hA x
          obtain ⟨y, hy⟩ := h x
          exact ⟨y, (ih (l ++ [x, y])).2 hy hA⟩
      · show (A → ∃ x : M, ∀ y : M, AltB true B n (l ++ [x, y])) ↔
          ∃ x : M, ∀ y : M, AltB true (fun l' => A → B l') n (l ++ [x, y])
        constructor
        · intro h
          by_cases hA : A
          · obtain ⟨x, hx⟩ := h hA
            exact ⟨x, fun y => (ih (l ++ [x, y])).1 (fun _ => hx y)⟩
          · exact ⟨d, fun y => (ih (l ++ [d, y])).1 (fun a => absurd a hA)⟩
        · rintro ⟨x, hx⟩ hA
          exact ⟨x, fun y => (ih (l ++ [x, y])).2 (hx y) hA⟩

/-! ### Semantics of the transform

The lemmas are stated for one type `G` carrying a `σ`-structure and a structure for `σ` with `∘` that
are compatible: `∘` is equality (`hc`) and the symbols of `σ` keep their meaning (`hl`). -/

section sem

variable (G : Type) [S₁ : σ.lang.Structure G] [S₂ : (sigmaEq σ).lang.Structure G]

theorem realize_trTerm {n k : ℕ} (env : Fin n → Fin k) (t : σ.lang.Term (Empty ⊕ Fin n))
    (v v' : Empty → G) (xs : Fin k → G) :
    (trTerm env t).realize (Sum.elim v' xs) = t.realize (Sum.elim v (fun j => xs (env j))) := by
  match t with
  | .var (.inl e) => exact e.elim
  | .var (.inr j) => rfl
  | .func f _ => exact nomatch (show Empty from f)

omit S₁ in
theorem realize_circ (hc : ∀ args : Fin 2 → G, Structure.RelMap (circRel σ) args ↔ args 0 = args 1)
    {k : ℕ} (a b : (sigmaEq σ).lang.Term (Empty ⊕ Fin k)) (v' : Empty → G) (xs : Fin k → G) :
    (BoundedFormula.rel (circRel σ) ![a, b]).Realize v' xs ↔
      a.realize (Sum.elim v' xs) = b.realize (Sum.elim v' xs) := by
  show Structure.RelMap (circRel σ) (fun i => (![a, b] i).realize (Sum.elim v' xs)) ↔ _
  rw [hc]
  exact Iff.rfl

/-- The realization of the matrix reads only the positions below `2 (q + nall f)`. -/
theorem tr_realize_congr (k : ℕ) : ∀ {n : ℕ} (f : σ.lang.BoundedFormula Empty n)
    (env : Fin n → Fin k) (q : ℕ) (neg : Bool) (h : 2 * (q + nall f) ≤ k)
    (v' : Empty → G) (xs xs' : Fin k → G),
    (∀ j, (env j).val < 2 * q) →
    (∀ p : Fin k, p.val < 2 * (q + nall f) → xs p = xs' p) →
    ((tr k f env q neg h).Realize v' xs ↔ (tr k f env q neg h).Realize v' xs') := by
  intro n f
  induction f with
  | falsum => intro env q neg h v' xs xs' henv hx; exact Iff.rfl
  | equal t₁ t₂ =>
      intro env q neg h v' xs xs' henv hx
      have e : (fun j => xs (env j)) = fun j => xs' (env j) :=
        funext fun j => hx _ (by have := henv j; omega)
      show Structure.RelMap (circRel σ)
          (fun i => (![trTerm env t₁, trTerm env t₂] i).realize (Sum.elim v' xs)) ↔
        Structure.RelMap (circRel σ)
          (fun i => (![trTerm env t₁, trTerm env t₂] i).realize (Sum.elim v' xs'))
      have e1 : (fun i => (![trTerm env t₁, trTerm env t₂] i).realize (Sum.elim v' xs)) =
          fun i => (![trTerm env t₁, trTerm env t₂] i).realize (Sum.elim v' xs') := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · show (trTerm env t₁).realize _ = (trTerm env t₁).realize _
          rw [realize_trTerm G env t₁ v' v', realize_trTerm G env t₁ v' v', e]
        · refine Fin.cases ?_ (fun i => i.elim0) i
          show (trTerm env t₂).realize _ = (trTerm env t₂).realize _
          rw [realize_trTerm G env t₂ v' v', realize_trTerm G env t₂ v' v', e]
      rw [e1]
  | rel R ts =>
      intro env q neg h v' xs xs' henv hx
      have e : (fun j => xs (env j)) = fun j => xs' (env j) :=
        funext fun j => hx _ (by have := henv j; omega)
      show Structure.RelMap (liftRel R)
          (fun j => (trTerm env (ts j)).realize (Sum.elim v' xs)) ↔
        Structure.RelMap (liftRel R)
          (fun j => (trTerm env (ts j)).realize (Sum.elim v' xs'))
      have e1 : (fun j => (trTerm env (ts j)).realize (Sum.elim v' xs)) =
          fun j => (trTerm env (ts j)).realize (Sum.elim v' xs') := by
        funext j
        rw [realize_trTerm G env (ts j) v' v', realize_trTerm G env (ts j) v' v', e]
      rw [e1]
  | imp f g ihf ihg =>
      intro env q neg h v' xs xs' henv hx
      have hh : 2 * (q + (nall f + nall g)) ≤ k := h
      have hf2 : 2 * (q + nall f) ≤ k := by omega
      have hg2 : 2 * (q + nall f + nall g) ≤ k := by omega
      have h1 := ihf env q (!neg) hf2 v' xs xs' henv
        (fun p hp => hx p (by simp only [nall]; omega))
      have h2 := ihg env (q + nall f) neg hg2 v' xs xs'
        (fun j => by have := henv j; omega)
        (fun p hp => hx p (by simp only [nall]; omega))
      show ((tr k f env q (!neg) hf2).imp (tr k g env (q + nall f) neg hg2)).Realize v' xs ↔
        ((tr k f env q (!neg) hf2).imp (tr k g env (q + nall f) neg hg2)).Realize v' xs'
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp, h1, h2]
  | all f ih =>
      intro env q neg h v' xs xs' henv hx
      have hh : 2 * (q + (nall f + 1)) ≤ k := h
      have hb := neg.toNat_lt
      exact ih (Fin.snoc (α := fun _ => Fin k) env ⟨2 * q + neg.toNat, by omega⟩) (q + 1) neg
        (by omega) v' xs xs'
        (fun j => by
          refine Fin.lastCases ?_ (fun j => ?_) j
          · rw [Fin.snoc_last]; show 2 * q + neg.toNat < 2 * (q + 1); omega
          · rw [Fin.snoc_castSucc]; have := henv j; omega)
        (fun p hp => hx p (by simp only [nall]; omega))

variable [Nonempty G]

/-- The transform is correct: `f` is equivalent to the alternating prefix of its `nall f` rounds in
front of the matrix. -/
theorem main_sem (hc : ∀ args : Fin 2 → G, Structure.RelMap (circRel σ) args ↔ args 0 = args 1)
    (hl : ∀ {a : ℕ} (R : σ.lang.Relations a) (args : Fin a → G),
      Structure.RelMap (liftRel R) args ↔ Structure.RelMap R args)
    (d : G) (k : ℕ) : ∀ {n : ℕ} (f : σ.lang.BoundedFormula Empty n)
    (env : Fin n → Fin k) (q : ℕ) (neg : Bool) (h : 2 * (q + nall f) ≤ k)
    (v v' : Empty → G) (l : List G),
    l.length = 2 * q → (∀ j, (env j).val < 2 * q) →
    (f.Realize v (fun j => l.getD (env j).val d) ↔
      AltB neg (fun l' : List G =>
        (tr k f env q neg h).Realize v' (fun p : Fin k => l'.getD p.val d)) (nall f) l) := by
  intro n f
  induction f with
  | falsum =>
      intro env q neg h v v' l hl henv
      show _ ↔ AltB neg _ 0 l
      rw [AltB_zero]
      exact Iff.rfl
  | equal t₁ t₂ =>
      intro env q neg h v v' l hl henv
      show _ ↔ AltB neg _ 0 l
      rw [AltB_zero]
      show t₁.realize (Sum.elim v fun j => l.getD (env j).val d) =
          t₂.realize (Sum.elim v fun j => l.getD (env j).val d) ↔
        (BoundedFormula.rel (circRel σ) ![trTerm env t₁, trTerm env t₂]).Realize v'
          (fun p : Fin k => l.getD p.val d)
      rw [realize_circ G hc, realize_trTerm G env t₁ v v', realize_trTerm G env t₂ v v']
  | rel R ts =>
      intro env q neg h v v' l hl' henv
      show _ ↔ AltB neg _ 0 l
      rw [AltB_zero]
      show Structure.RelMap R (fun j => (ts j).realize (Sum.elim v fun j => l.getD (env j).val d)) ↔
        Structure.RelMap (liftRel R)
          (fun j => (trTerm env (ts j)).realize (Sum.elim v' (fun p : Fin k => l.getD p.val d)))
      rw [hl]
      have e1 : (fun j => (trTerm env (ts j)).realize
            (Sum.elim v' (fun p : Fin k => l.getD p.val d))) =
          fun j => (ts j).realize (Sum.elim v fun j => l.getD (env j).val d) := by
        funext j
        rw [realize_trTerm G env (ts j) v v']
      rw [e1]
  | imp f g ihf ihg =>
      intro env q neg h v v' l hl' henv
      have hh : 2 * (q + (nall f + nall g)) ≤ k := h
      have hf2 : 2 * (q + nall f) ≤ k := by omega
      have hg2 : 2 * (q + nall f + nall g) ≤ k := by omega
      show (f.imp g).Realize v (fun j => l.getD (env j).val d) ↔
        AltB neg (fun l' : List G =>
          ((tr k f env q (!neg) hf2).imp (tr k g env (q + nall f) neg hg2)).Realize v'
            (fun p : Fin k => l'.getD p.val d)) (nall f + nall g) l
      rw [BoundedFormula.realize_imp, AltB_add, ihf env q (!neg) hf2 v v' l hl' henv, pull_left]
      apply AltB_congr
      intro e he
      have hg := ihg env (q + nall f) neg hg2 v v' (l ++ e) (by simp [hl', he]; omega)
        (fun j => by have := henv j; omega)
      have e1 : (fun j => (l ++ e).getD (env j).val d) = fun j => l.getD (env j).val d :=
        funext fun j => List.getD_append _ _ _ _ (by have := henv j; omega)
      rw [e1] at hg
      rw [hg, pull_right]
      apply AltB_congr
      intro e' he'
      have e2 := tr_realize_congr G k f env q (!neg) hf2 v'
        (fun p : Fin k => (l ++ e ++ e').getD p.val d)
        (fun p : Fin k => (l ++ e).getD p.val d) henv
        (fun p hp => List.getD_append _ _ _ _ (by simp [hl', he]; omega))
      show _ ↔ ((tr k f env q (!neg) hf2).Realize v' (fun p : Fin k => (l ++ e ++ e').getD p.val d) →
        (tr k g env (q + nall f) neg hg2).Realize v' (fun p : Fin k => (l ++ e ++ e').getD p.val d))
      rw [e2]
  | all f ih =>
      intro env q neg h v v' l hl' henv
      have hh : 2 * (q + (nall f + 1)) ≤ k := h
      have hb := neg.toNat_lt
      have hk : 2 * q + neg.toNat < k := by omega
      have key : ∀ x y : G, (f.Realize v (Fin.snoc (α := fun _ => G) (fun j => l.getD (env j).val d)
            (if neg then y else x)) ↔
          AltB neg (fun l' : List G =>
            (tr k f (Fin.snoc (α := fun _ => Fin k) env ⟨2 * q + neg.toNat, hk⟩) (q + 1) neg
              (by omega)).Realize v' (fun p : Fin k => l'.getD p.val d))
            (nall f) (l ++ [x, y])) := by
        intro x y
        have := ih (Fin.snoc (α := fun _ => Fin k) env ⟨2 * q + neg.toNat, hk⟩) (q + 1) neg
          (by omega) v v' (l ++ [x, y]) (by simp [hl']; omega)
          (fun j => by
            refine Fin.lastCases ?_ (fun j => ?_) j
            · rw [Fin.snoc_last]; show 2 * q + neg.toNat < 2 * (q + 1); omega
            · rw [Fin.snoc_castSucc]; have := henv j; omega)
        rw [← this]
        have e1 : (fun j => (l ++ [x, y]).getD
              (Fin.snoc (α := fun _ => Fin k) env ⟨2 * q + neg.toNat, hk⟩ j).val d) =
            Fin.snoc (α := fun _ => G) (fun j => l.getD (env j).val d) (if neg then y else x) := by
          funext j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · rw [Fin.snoc_last, Fin.snoc_last]
            cases neg
            · simp [List.getD_eq_getElem?_getD, ← hl']
            · simp [List.getD_eq_getElem?_getD, ← hl']
          · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
            exact List.getD_append _ _ _ _ (by have := henv j; omega)
        rw [e1]
      show (∀ a : G, f.Realize v (Fin.snoc (fun j => l.getD (env j).val d) a)) ↔
        AltB neg (fun l' : List G =>
            (tr k f (Fin.snoc (α := fun _ => Fin k) env ⟨2 * q + neg.toNat, hk⟩) (q + 1) neg
              (by omega)).Realize v' (fun p : Fin k => l'.getD p.val d))
          (nall f + 1) l
      cases neg
      · show _ ↔ ∀ x : G, ∃ y : G, AltB false _ (nall f) (l ++ [x, y])
        constructor
        · intro ha x
          exact ⟨d, (key x d).1 (by simpa using ha x)⟩
        · intro ha a
          obtain ⟨y, hy⟩ := ha a
          simpa using (key a y).2 hy
      · show _ ↔ ∃ x : G, ∀ y : G, AltB true _ (nall f) (l ++ [x, y])
        constructor
        · intro ha
          exact ⟨d, fun y => (key d y).1 (by simpa using ha y)⟩
        · rintro ⟨x, hx⟩ a
          simpa using (key x a).2 (hx a)

end sem

end AF
end CoDecompFO

namespace CoDecompFO
namespace AF

open FirstOrder FirstOrder.Language

/-! ### `Holds` on the atoms of a full list is realization -/

theorem term_inr {τ : Sig} {k : ℕ} (t : τ.lang.Term (Empty ⊕ Fin k)) :
    ∃ p : Fin k, t = Term.var (Sum.inr p) := by
  match t with
  | .var (.inl e) => exact e.elim
  | .var (.inr p) => exact ⟨p, rfl⟩
  | .func f _ => exact nomatch (show Empty from f)

theorem holds_iff {τ : Sig} {k : ℕ} (G : Type) [τ.lang.Structure G]
    (ψ : τ.lang.BoundedFormula Empty k) (hqf : ψ.IsQF) :
    EqFree ψ → ∀ (l : List G) (d : G) (v : Empty → G), l.length = k →
      (Holds ψ (atomsOf τ k l) ↔ ψ.Realize v (fun p : Fin k => l.getD p.val d)) := by
  induction hqf with
  | falsum => intro _ l d v hl; exact Iff.rfl
  | of_isAtomic hat =>
      cases hat with
      | equal t₁ t₂ => intro hef; exact hef.elim
      | rel R ts =>
          intro _ l d v hl
          obtain ⟨i, rfl⟩ := R
          have hp : ∀ j, ∃ p : Fin k, ts j = Term.var (Sum.inr p) := fun j => term_inr (ts j)
          choose p hp using hp
          obtain rfl : ts = fun j => Term.var (Sum.inr (p j)) := funext hp
          show (⟨i, p⟩ : τ.Atom k) ∈ atomsOf τ k l ↔ τ.holds i (fun j => l.getD (p j).val d)
          constructor
          · rintro ⟨args, hargs, hh⟩
            have : args = fun j => l.getD (p j).val d := by
              funext j
              have h1 : l[(p j).val]? = some (args j) := hargs j
              rw [List.getD_eq_getElem?_getD, h1]; rfl
            rw [← this]; exact hh
          · intro hh
            refine ⟨fun j => l.getD (p j).val d, fun j => ?_, hh⟩
            show l[(p j).val]? = some (l.getD (p j).val d)
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; exact (p j).2)]
            rfl
  | imp h₁ h₂ ih₁ ih₂ =>
      intro hef l d v hl
      have i1 := ih₁ hef.1 l d v hl
      have i2 := ih₂ hef.2 l d v hl
      show (Holds _ (atomsOf τ k l) → Holds _ (atomsOf τ k l)) ↔ _
      rw [BoundedFormula.realize_imp, i1, i2]

theorem altSat_iff {τ : Sig} {k : ℕ} (G : Type) [τ.lang.Structure G]
    (ψ : τ.lang.BoundedFormula Empty k) : ∀ (m : ℕ) (l : List G),
    AltSat ψ m l ↔ AltB false (fun l' => Holds ψ (atomsOf τ k l')) m l := by
  intro m
  induction m with
  | zero => intro l; exact Iff.rfl
  | succ m ih =>
      intro l
      exact forall_congr' fun x => exists_congr fun y => ih _

/-! ### `G°` -/

theorem circ_relMap (σ : Sig) (M : Type) [σ.lang.Structure M] (args : Fin 2 → Circ σ M) :
    Structure.RelMap (circRel σ) args ↔ args 0 = args 1 :=
  Iff.rfl

theorem lift_relMap (σ : Sig) (M : Type) [S : σ.lang.Structure M] {a : ℕ} (R : σ.lang.Relations a)
    (args : Fin a → Circ σ M) :
    Structure.RelMap (liftRel R) args ↔ @Structure.RelMap σ.lang M S a R args := by
  obtain ⟨i, rfl⟩ := R
  exact Iff.rfl

/-- **Semantics of the alternating form.** -/
theorem sem_final (σ : Sig) (M : Type) [S : σ.lang.Structure M] [Nonempty M] (φ : σ.lang.Sentence) :
    (M ⊨ φ) ↔ AltSat (G := Circ σ M)
      (tr (2 * nall φ) φ (Fin.elim0 : Fin 0 → Fin (2 * nall φ)) 0 false (by omega)) (nall φ) [] := by
  obtain ⟨d⟩ := ‹Nonempty M›
  have : Nonempty (Circ σ M) := ⟨d⟩
  have key := @main_sem σ (Circ σ M) S (Circ.structure σ M) _ (circ_relMap σ M)
    (fun R args => lift_relMap σ M R args) d (2 * nall φ) 0 φ Fin.elim0 0 false (by omega)
    (default : Empty → M) (default : Empty → M) [] rfl (fun j => j.elim0)
  have e0 : (fun j : Fin 0 => ([] : List (Circ σ M)).getD (Fin.elim0 j : Fin (2 * nall φ)).val d) =
      (default : Fin 0 → M) := Subsingleton.elim _ _
  rw [e0] at key
  rw [altSat_iff]
  refine Iff.trans key ?_
  apply AltB_congr
  intro e he
  exact (holds_iff (Circ σ M) _ (tr_isQF _ _ _ _ _ _) (tr_eqFree _ _ _ _ _ _) ([] ++ e) d _
    (by simpa using he)).symm

end AF
end CoDecompFO

namespace CoDecompFO
namespace AF

open FirstOrder FirstOrder.Language

variable {σ : Sig}

/-! ### The scanner on codes

A state is a stack of tasks, the number of quantifiers met so far, and the output. A task is a tag and
an environment (the positions of the bound variables): tag `0` or `1` is "read a formula" in positive
or negative polarity, `2` is "read a term", `3` is "read a symbol index". -/

abbrev St : Type := List (ℕ × List ℕ) × ℕ × List ℕ

/-- One step of the scanner: consume the token `t`. -/
def step (ar' : ℕ → ℕ) (s : St) (t : ℕ) : St :=
  if s.1.headI.1 = 2 then (s.1.tail, s.2.1, s.2.2 ++ [s.1.headI.2.getD t 0])
  else if s.1.headI.1 = 3 then
    ((List.range (ar' t)).map (fun _ => ((2 : ℕ), s.1.headI.2)) ++ s.1.tail, s.2.1, s.2.2 ++ [t + 1])
  else if t = 0 then (s.1.tail, s.2.1, s.2.2 ++ [0])
  else if t = 1 then
    ((2, s.1.headI.2) :: (2, s.1.headI.2) :: s.1.tail, s.2.1, s.2.2 ++ [2, 0])
  else if t = 2 then ((3, s.1.headI.2) :: s.1.tail, s.2.1, s.2.2 ++ [2])
  else if t = 3 then
    ((1 - s.1.headI.1, s.1.headI.2) :: (s.1.headI.1, s.1.headI.2) :: s.1.tail, s.2.1, s.2.2 ++ [3])
  else ((s.1.headI.1, s.1.headI.2 ++ [2 * s.2.1 + s.1.headI.1]) :: s.1.tail, s.2.1 + 1, s.2.2)

/-- The arity of the symbol with index `i`, as a function on `ℕ`. -/
def arN (σ : Sig) (i : ℕ) : ℕ := (List.ofFn σ.ar).getD i 0

/-- The map on codes. -/
def F (σ : Sig) (l : List ℕ) : List ℕ :=
  (l.foldl (step (arN σ)) ([(0, [])], 0, [])).2.1 :: (l.foldl (step (arN σ)) ([(0, [])], 0, [])).2.2

theorem arN_val (σ : Sig) (i : Fin σ.r) : arN σ i.val = σ.ar i := by
  unfold arN
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
  simp

theorem step_term (ar' : ℕ → ℕ) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ) (out : List ℕ)
    (t : ℕ) : step ar' ((2, env) :: rest, q, out) t = (rest, q, out ++ [env.getD t 0]) := by
  simp [step]

theorem step_idx (ar' : ℕ → ℕ) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ) (out : List ℕ)
    (t : ℕ) : step ar' ((3, env) :: rest, q, out) t =
      (List.replicate (ar' t) (2, env) ++ rest, q, out ++ [t + 1]) := by
  simp [step]

theorem step_form0 (ar' : ℕ → ℕ) (neg : Bool) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ)
    (out : List ℕ) : step ar' ((neg.toNat, env) :: rest, q, out) 0 = (rest, q, out ++ [0]) := by
  cases neg <;> simp [step]

theorem step_form1 (ar' : ℕ → ℕ) (neg : Bool) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ)
    (out : List ℕ) : step ar' ((neg.toNat, env) :: rest, q, out) 1 =
      ((2, env) :: (2, env) :: rest, q, out ++ [2, 0]) := by
  cases neg <;> simp [step]

theorem step_form2 (ar' : ℕ → ℕ) (neg : Bool) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ)
    (out : List ℕ) : step ar' ((neg.toNat, env) :: rest, q, out) 2 =
      ((3, env) :: rest, q, out ++ [2]) := by
  cases neg <;> simp [step]

theorem step_form3 (ar' : ℕ → ℕ) (neg : Bool) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ)
    (out : List ℕ) : step ar' ((neg.toNat, env) :: rest, q, out) 3 =
      (((!neg).toNat, env) :: (neg.toNat, env) :: rest, q, out ++ [3]) := by
  cases neg <;> simp [step]

theorem step_form4 (ar' : ℕ → ℕ) (neg : Bool) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ)
    (out : List ℕ) : step ar' ((neg.toNat, env) :: rest, q, out) 4 =
      ((neg.toNat, env ++ [2 * q + neg.toNat]) :: rest, q + 1, out) := by
  cases neg <;> simp [step]

theorem scan_terms (ar' : ℕ → ℕ) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ) :
    ∀ (cs toks out : List ℕ),
      (cs ++ toks).foldl (step ar') (List.replicate cs.length (2, env) ++ rest, q, out) =
        toks.foldl (step ar') (rest, q, out ++ cs.map (fun c => env.getD c 0)) := by
  intro cs
  induction cs with
  | nil => intro toks out; simp
  | cons c cs ih =>
      intro toks out
      rw [List.cons_append, List.foldl_cons, List.length_cons, List.replicate_succ, List.cons_append,
        step_term, ih]
      simp

/-- The list form of an environment. -/
def envL {n k : ℕ} (env : Fin n → Fin k) : List ℕ := List.ofFn (fun j => (env j).val)

theorem encTerm_tr {n k : ℕ} (env : Fin n → Fin k) (t : σ.lang.Term (Empty ⊕ Fin n)) :
    encTerm (trTerm env t) = (envL env).getD (encTerm t) 0 := by
  match t with
  | .var (.inl e) => exact e.elim
  | .var (.inr j) =>
      show (env j).val = (envL env).getD j.val 0
      unfold envL
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
      simp
  | .func f _ => exact nomatch (show Empty from f)

theorem envL_snoc {n k : ℕ} (env : Fin n → Fin k) (p : Fin k) :
    envL (Fin.snoc (α := fun _ => Fin k) env p) = envL env ++ [p.val] := by
  unfold envL
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

/-- The scanner, run on the code of `f`, emits the code of the matrix of `f`. -/
theorem scan (k : ℕ) : ∀ {n : ℕ} (f : σ.lang.BoundedFormula Empty n) (env : Fin n → Fin k) (q : ℕ)
    (neg : Bool) (h : 2 * (q + nall f) ≤ k) (rest : List (ℕ × List ℕ)) (out toks : List ℕ),
    (encF f ++ toks).foldl (step (arN σ)) ((neg.toNat, envL env) :: rest, q, out) =
      toks.foldl (step (arN σ)) (rest, q + nall f, out ++ encF (tr k f env q neg h)) := by
  intro n f
  induction f with
  | falsum =>
      intro env q neg h rest out toks
      show ([0] ++ toks).foldl _ _ = toks.foldl _ (rest, q + 0, out ++ [0])
      rw [List.singleton_append, List.foldl_cons, step_form0]
      rfl
  | equal t₁ t₂ =>
      intro env q neg h rest out toks
      show ([1, encTerm t₁, encTerm t₂] ++ toks).foldl _ _ = toks.foldl _
        (rest, q + 0, out ++ (2 :: 0 :: List.ofFn
          (fun j => encTerm (![trTerm env t₁, trTerm env t₂] j))))
      have e : List.ofFn (fun j => encTerm (![trTerm env t₁, trTerm env t₂] j)) =
          [(envL env).getD (encTerm t₁) 0, (envL env).getD (encTerm t₂) 0] := by
        simp [List.ofFn_succ, encTerm_tr]
      rw [e]
      simp only [List.cons_append, List.nil_append, List.foldl_cons, step_form1, step_term]
      simp
  | rel R ts =>
      intro env q neg h rest out toks
      rename_i a
      show ((2 :: R.1.val :: List.ofFn (fun j => encTerm (ts j))) ++ toks).foldl _ _ = toks.foldl _
        (rest, q + 0, out ++ (2 :: (R.1.val + 1) :: List.ofFn (fun j => encTerm (trTerm env (ts j)))))
      have ha : arN σ R.1.val = (List.ofFn (fun j => encTerm (ts j))).length := by
        rw [arN_val, R.2, List.length_ofFn]
      rw [List.cons_append, List.cons_append, List.foldl_cons, List.foldl_cons, step_form2, step_idx,
        ha, scan_terms]
      have e : (List.ofFn (fun j => encTerm (ts j))).map (fun c => (envL env).getD c 0) =
          List.ofFn (fun j => encTerm (trTerm env (ts j))) := by
        rw [List.map_ofFn]
        congr 1
        funext j
        exact (encTerm_tr env (ts j)).symm
      rw [e]
      simp
  | imp f g ihf ihg =>
      intro env q neg h rest out toks
      have hh : 2 * (q + (nall f + nall g)) ≤ k := h
      have hf2 : 2 * (q + nall f) ≤ k := by omega
      have hg2 : 2 * (q + nall f + nall g) ≤ k := by omega
      show ((3 :: (encF f ++ encF g)) ++ toks).foldl _ _ = toks.foldl _
        (rest, q + (nall f + nall g),
          out ++ (3 :: (encF (tr k f env q (!neg) hf2) ++ encF (tr k g env (q + nall f) neg hg2))))
      rw [List.cons_append, List.foldl_cons, step_form3, List.append_assoc,
        ihf env q (!neg) hf2, ihg env (q + nall f) neg hg2]
      simp [Nat.add_assoc]
  | all f ih =>
      intro env q neg h rest out toks
      have hh : 2 * (q + (nall f + 1)) ≤ k := h
      have hb := neg.toNat_lt
      have hk : 2 * q + neg.toNat < k := by omega
      show ((4 :: encF f) ++ toks).foldl _ _ = toks.foldl _
        (rest, q + (nall f + 1), out ++ encF (tr k f
          (Fin.snoc (α := fun _ => Fin k) env ⟨2 * q + neg.toNat, hk⟩) (q + 1) neg (by omega)))
      rw [List.cons_append, List.foldl_cons, step_form4,
        ← envL_snoc env ⟨2 * q + neg.toNat, hk⟩, ih _ (q + 1) neg (by omega)]
      simp [Nat.add_assoc, Nat.add_comm]

theorem F_enc (φ : σ.lang.Sentence) :
    F σ (encF φ) = nall φ ::
      encF (tr (2 * nall φ) φ (Fin.elim0 : Fin 0 → Fin (2 * nall φ)) 0 false (by omega)) := by
  have h := scan (σ := σ) (2 * nall φ) φ (Fin.elim0 : Fin 0 → Fin (2 * nall φ)) 0 false (by omega)
    [] [] []
  have e : envL (Fin.elim0 : Fin 0 → Fin (2 * nall φ)) = [] := rfl
  rw [e] at h
  simp only [List.append_nil, List.foldl_nil, Bool.toNat_false, Nat.zero_add, List.nil_append] at h
  unfold F
  rw [h]

/-! ### Computability -/

theorem arN_primrec (σ : Sig) : Primrec (arN σ) :=
  (Primrec.list_getD 0).comp (Primrec.const _) Primrec.id

theorem step_primrec {ar' : ℕ → ℕ} (har : Primrec ar') : Primrec₂ (step ar') := by
  have hstk : Primrec (fun p : St × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hhd : Primrec (fun p : St × ℕ => p.1.1.headI) := Primrec.list_headI.comp hstk
  have htag : Primrec (fun p : St × ℕ => p.1.1.headI.1) := Primrec.fst.comp hhd
  have henv : Primrec (fun p : St × ℕ => p.1.1.headI.2) := Primrec.snd.comp hhd
  have hrest : Primrec (fun p : St × ℕ => p.1.1.tail) := Primrec.list_tail.comp hstk
  have hq : Primrec (fun p : St × ℕ => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hout : Primrec (fun p : St × ℕ => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec (fun p : St × ℕ => p.2) := Primrec.snd
  have h2env : Primrec (fun p : St × ℕ => ((2 : ℕ), p.1.1.headI.2)) :=
    Primrec.pair (Primrec.const 2) henv
  have emit : ∀ {g : St × ℕ → List ℕ}, Primrec g →
      Primrec (fun p : St × ℕ => p.1.2.2 ++ g p) := fun hg => Primrec.list_append.comp hout hg
  have single : ∀ {g : St × ℕ → ℕ}, Primrec g → Primrec (fun p : St × ℕ => [g p]) :=
    fun hg => Primrec.list_cons.comp hg (Primrec.const [])
  show Primrec (fun p : St × ℕ => step ar' p.1 p.2)
  unfold step
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) ?_ ?_
  · exact Primrec.pair hrest (Primrec.pair hq
      (emit (single ((Primrec.list_getD 0).comp henv ht))))
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) ?_ ?_
  · refine Primrec.pair ?_ (Primrec.pair hq (emit (single (Primrec.succ.comp ht))))
    refine Primrec.list_append.comp ?_ hrest
    exact Primrec.list_map (Primrec.list_range.comp (har.comp ht))
      (h2env.comp Primrec.fst).to₂
  refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) ?_ ?_
  · exact Primrec.pair hrest (Primrec.pair hq (emit (Primrec.const [0])))
  refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) ?_ ?_
  · exact Primrec.pair (Primrec.list_cons.comp h2env (Primrec.list_cons.comp h2env hrest))
      (Primrec.pair hq (emit (Primrec.const [2, 0])))
  refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) ?_ ?_
  · exact Primrec.pair (Primrec.list_cons.comp (Primrec.pair (Primrec.const 3) henv) hrest)
      (Primrec.pair hq (emit (Primrec.const [2])))
  refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 3)) ?_ ?_
  · exact Primrec.pair
      (Primrec.list_cons.comp (Primrec.pair (Primrec.nat_sub.comp (Primrec.const 1) htag) henv)
        (Primrec.list_cons.comp (Primrec.pair htag henv) hrest))
      (Primrec.pair hq (emit (Primrec.const [3])))
  · refine Primrec.pair (Primrec.list_cons.comp (Primrec.pair htag ?_) hrest)
      (Primrec.pair (Primrec.succ.comp hq) hout)
    exact Primrec.list_append.comp henv
      (single (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hq) htag))

theorem F_primrec (σ : Sig) : Primrec (F σ) := by
  have hfold : Primrec (fun l : List ℕ => l.foldl (step (arN σ)) (([(0, [])], 0, []) : St)) :=
    Primrec.list_foldl (f := fun l : List ℕ => l) (g := fun _ => (([(0, [])], 0, []) : St))
      (h := fun _ p => step (arN σ) p.1 p.2) Primrec.id (Primrec.const _)
      ((step_primrec (arN_primrec σ)).comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp hfold))
    (Primrec.snd.comp (Primrec.snd.comp hfold))

/-- **Alternating form, with equality.** -/
theorem alternating_form_main (σ : Sig) :
    ∃ F : List ℕ → List ℕ, Computable F ∧
      ∀ φ : σ.lang.Sentence,
        ∃ (ℓ : ℕ) (ψ : (sigmaEq σ).lang.BoundedFormula Empty (2 * ℓ)),
          IsMatrix ψ ∧ ℓ ≤ sentLen φ ∧ F (encF φ) = ℓ :: encF ψ ∧ sentLen ψ ≤ 2 * sentLen φ ∧
            ∀ (M : Type) [σ.lang.Structure M] [Nonempty M],
              (M ⊨ φ ↔ AltSat (G := Circ σ M) ψ ℓ []) := by
  refine ⟨F σ, (F_primrec σ).to_comp, fun φ => ⟨nall φ,
    tr (2 * nall φ) φ (Fin.elim0 : Fin 0 → Fin (2 * nall φ)) 0 false (by omega),
    ⟨tr_isQF _ _ _ _ _ _, tr_eqFree _ _ _ _ _ _⟩, nall_le φ, F_enc φ, tr_len _ _ _ _ _ _, ?_⟩⟩
  intro M _ _
  exact sem_final σ M φ

end AF
end CoDecompFO

open CoDecompFO FirstOrder

theorem solution (σ : Sig) :
    ∃ F : List ℕ → List ℕ, Computable F ∧
      ∀ φ : σ.lang.Sentence,
        ∃ (ℓ : ℕ) (ψ : (sigmaEq σ).lang.BoundedFormula Empty (2 * ℓ)),
          IsMatrix ψ ∧ ℓ ≤ sentLen φ ∧ F (encF φ) = ℓ :: encF ψ ∧ sentLen ψ ≤ 2 * sentLen φ ∧
            ∀ (M : Type) [σ.lang.Structure M] [Nonempty M],
              (M ⊨ φ ↔ AltSat (G := Circ σ M) ψ ℓ []) :=
  CoDecompFO.AF.alternating_form_main σ
