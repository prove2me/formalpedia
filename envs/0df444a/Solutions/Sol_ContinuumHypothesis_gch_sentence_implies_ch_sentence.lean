-- Prove2me | solution 1 for ContinuumHypothesis.gch_sentence_implies_ch_sentence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:17:28.143414+00:00
-- url     : https://prove2.me/submissions/1a15d106-ebcb-4231-af52-a3f4a017f8b2

import Mathlib
import Definitions.Def_CH_ZFC

set_option linter.all false


open FirstOrder FirstOrder.Language


namespace CHA
open ContinuumHypothesis ContinuumHypothesis.SFormula

variable {M : Type*} [setLang.Structure M]

/-- membership in the model -/
def Mem (a b : M) : Prop := Structure.RelMap (L := setLang) SetRel.mem ![a, b]

@[simp] theorem realize_mem (v : ℕ → M) (x y : ℕ) : Formula.Realize (mem x y) v ↔ Mem (v x) (v y) := by
  rw [mem, Formula.realize_rel₂]; rfl

@[simp] theorem realize_eq (v : ℕ → M) (x y : ℕ) : Formula.Realize (eq x y) v ↔ v x = v y := by
  rw [eq, Formula.realize_equal]; rfl

@[simp] theorem realize_all (v : ℕ → M) (x : ℕ) (φ : SFormula) :
    Formula.Realize (all x φ) v ↔ ∀ a, Formula.Realize φ (Function.update v x a) := by
  simp only [all, Formula.realize_iAlls, Formula.realize_relabel]
  constructor
  · intro h a
    convert h (fun _ => a) using 2
    ext n; by_cases hn : n = x <;> simp [hn, Function.update]
  · intro h i
    convert h (i ()) using 2
    ext n; by_cases hn : n = x <;> simp [hn, Function.update]

@[simp] theorem realize_ex (v : ℕ → M) (x : ℕ) (φ : SFormula) :
    Formula.Realize (ex x φ) v ↔ ∃ a, Formula.Realize φ (Function.update v x a) := by
  simp only [ex, Formula.realize_iExs, Formula.realize_relabel]
  constructor
  · rintro ⟨i, h⟩
    refine ⟨i (), ?_⟩
    convert h using 2
    ext n; by_cases hn : n = x <;> simp [hn, Function.update]
  · rintro ⟨a, h⟩
    refine ⟨fun _ => a, ?_⟩
    convert h using 2
    ext n; by_cases hn : n = x <;> simp [hn, Function.update]


/-! Lean-level predicates -/
def Sub (x y : M) : Prop := ∀ z, Mem z x → Mem z y
def IsEmp (x : M) : Prop := ∀ z, ¬ Mem z x
def IsSucc (s z : M) : Prop := ∀ w, Mem w s ↔ Mem w z ∨ w = z
def IsInd (w : M) : Prop := (∃ e, IsEmp e ∧ Mem e w) ∧ ∀ a, Mem a w → ∃ s, IsSucc s a ∧ Mem s w
def IsOmega (w : M) : Prop := IsInd w ∧ ∀ u, IsInd u → Sub w u
def IsPow (p x : M) : Prop := ∀ z, Mem z p ↔ Sub z x
def IsSing (t a : M) : Prop := ∀ z, Mem z t ↔ z = a
def IsDbl (t a b : M) : Prop := ∀ z, Mem z t ↔ z = a ∨ z = b
def IsPair (z a b : M) : Prop := ∀ w, Mem w z ↔ IsSing w a ∨ IsDbl w a b
def PairIn (f a b : M) : Prop := ∃ z, IsPair z a b ∧ Mem z f
def IsInj (f x y : M) : Prop :=
  (∀ a, Mem a x → ∃ b, Mem b y ∧ PairIn f a b) ∧
  (∀ a b b', Mem a x → PairIn f a b → PairIn f a b' → b = b') ∧
  (∀ a a' b, Mem a x → Mem a' x → PairIn f a b → PairIn f a' b → a = a')
def Injects (x y : M) : Prop := ∃ f, IsInj f x y
def IsBij (f x y : M) : Prop := IsInj f x y ∧ ∀ b, Mem b y → ∃ a, Mem a x ∧ PairIn f a b
def Equinum (x y : M) : Prop := ∃ f, IsBij f x y
def IsFin (s : M) : Prop := ∃ w, IsOmega w ∧ ∃ n, Mem n w ∧ Equinum n s

def LCH (M : Type*) [setLang.Structure M] : Prop :=
  ∀ w : M, IsOmega w → ∀ p, IsPow p w → ∀ x, Sub x p → Injects x w ∨ Injects p x
def LGCH (M : Type*) [setLang.Structure M] : Prop :=
  ∀ s : M, ¬ IsFin s → ∀ p, IsPow p s → ∀ t, Injects s t ∧ Injects t p → Equinum t s ∨ Equinum t p


section translate
variable (v : ℕ → M)
open Function

@[simp] theorem r_subset (x y : ℕ) (hx : x ≠ 1000) (hy : y ≠ 1000) :
    Formula.Realize (subset x y) v ↔ Sub (v x) (v y) := by
  simp [subset, Sub, update_of_ne hx, update_of_ne hy]
@[simp] theorem r_isEmpty (x : ℕ) (hx : x ≠ 1001) :
    Formula.Realize (isEmpty x) v ↔ IsEmp (v x) := by
  simp [isEmpty, IsEmp, update_of_ne hx]
@[simp] theorem r_isSucc (s z : ℕ) (hs : s ≠ 1002) (hz : z ≠ 1002) :
    Formula.Realize (isSucc s z) v ↔ IsSucc (v s) (v z) := by
  simp [isSucc, IsSucc, update_of_ne hs, update_of_ne hz]
@[simp] theorem r_isInductive (w : ℕ) (h3 : w ≠ 1003) (h4 : w ≠ 1004) (h5 : w ≠ 1005) :
    Formula.Realize (isInductive w) v ↔ IsInd (v w) := by
  simp [isInductive, IsInd, update_of_ne h3, update_of_ne h4, update_of_ne h5]
@[simp] theorem r_isOmega (w : ℕ) (h0 : w < 1000 ∨ 1006 < w) :
    Formula.Realize (isOmega w) v ↔ IsOmega (v w) := by
  simp [isOmega, IsOmega, update_of_ne (show w ≠ 1006 by omega), show w ≠ 1003 by omega,
    show w ≠ 1004 by omega, show w ≠ 1005 by omega, show w ≠ 1000 by omega]
@[simp] theorem r_isPowerset (p x : ℕ) (hp : p ≠ 1007) (hx : x ≠ 1007) (hx' : x ≠ 1000) :
    Formula.Realize (isPowerset p x) v ↔ IsPow (v p) (v x) := by
  simp [isPowerset, IsPow, update_of_ne hp, update_of_ne hx, hx']
@[simp] theorem r_isSingleton (t a : ℕ) (ht : t ≠ 1008) (ha : a ≠ 1008) :
    Formula.Realize (isSingleton t a) v ↔ IsSing (v t) (v a) := by
  simp [isSingleton, IsSing, update_of_ne ht, update_of_ne ha]
@[simp] theorem r_isDoubleton (t a b : ℕ) (ht : t ≠ 1009) (ha : a ≠ 1009) (hb : b ≠ 1009) :
    Formula.Realize (isDoubleton t a b) v ↔ IsDbl (v t) (v a) (v b) := by
  simp [isDoubleton, IsDbl, update_of_ne ht, update_of_ne ha, update_of_ne hb]
@[simp] theorem r_isPair (z a b : ℕ) (hz : z ≠ 1010) (ha : a < 1008 ∨ 1010 < a)
    (hb : b < 1008 ∨ 1010 < b) :
    Formula.Realize (isPair z a b) v ↔ IsPair (v z) (v a) (v b) := by
  simp [isPair, IsPair, update_of_ne hz, update_of_ne (show a ≠ 1010 by omega),
    update_of_ne (show b ≠ 1010 by omega), show a ≠ 1008 by omega, show a ≠ 1009 by omega,
    show b ≠ 1009 by omega]
@[simp] theorem r_pairIn (f a b : ℕ) (hf : f ≠ 1011) (ha : a < 1008 ∨ 1011 < a)
    (hb : b < 1008 ∨ 1011 < b) :
    Formula.Realize (pairIn f a b) v ↔ PairIn (v f) (v a) (v b) := by
  simp [pairIn, PairIn, update_of_ne hf, update_of_ne (show a ≠ 1011 by omega),
    update_of_ne (show b ≠ 1011 by omega), show a < 1008 ∨ 1010 < a by omega,
    show b < 1008 ∨ 1010 < b by omega]
@[simp] theorem r_isInjection (f x y : ℕ) (hf : f < 1011 ∨ 1015 < f) (hx : x < 1012 ∨ 1015 < x)
    (hy : y < 1012 ∨ 1015 < y) :
    Formula.Realize (isInjection f x y) v ↔ IsInj (v f) (v x) (v y) := by
  simp [isInjection, IsInj, update_of_ne, and_assoc, show f ≠ 1011 by omega, show f ≠ 1012 by omega,
    show f ≠ 1013 by omega, show f ≠ 1014 by omega, show f ≠ 1015 by omega,
    show x ≠ 1012 by omega, show x ≠ 1013 by omega, show x ≠ 1014 by omega, show x ≠ 1015 by omega,
    show y ≠ 1012 by omega, show y ≠ 1013 by omega, show y ≠ 1014 by omega, show y ≠ 1015 by omega]
@[simp] theorem r_injects (x y : ℕ) (hx : x < 1012 ∨ 1016 < x) (hy : y < 1012 ∨ 1016 < y) :
    Formula.Realize (injects x y) v ↔ Injects (v x) (v y) := by
  simp [injects, Injects, update_of_ne, show x ≠ 1016 by omega, show y ≠ 1016 by omega,
    show x < 1012 ∨ 1015 < x by omega, show y < 1012 ∨ 1015 < y by omega]
@[simp] theorem r_isBijection (f x y : ℕ) (hf : f < 1011 ∨ 1018 < f) (hx : x < 1012 ∨ 1018 < x)
    (hy : y < 1012 ∨ 1018 < y) :
    Formula.Realize (isBijection f x y) v ↔ IsBij (v f) (v x) (v y) := by
  simp [isBijection, IsBij, update_of_ne, show f ≠ 1011 by omega, show f ≠ 1017 by omega, show f ≠ 1018 by omega,
    show x ≠ 1017 by omega, show x ≠ 1018 by omega, show y ≠ 1017 by omega, show y ≠ 1018 by omega,
    show f < 1011 ∨ 1015 < f by omega, show x < 1012 ∨ 1015 < x by omega,
    show y < 1012 ∨ 1015 < y by omega]
@[simp] theorem r_equinum (x y : ℕ) (hx : x < 1012 ∨ 1019 < x) (hy : y < 1012 ∨ 1019 < y) :
    Formula.Realize (equinum x y) v ↔ Equinum (v x) (v y) := by
  simp [equinum, Equinum, update_of_ne, show x ≠ 1019 by omega, show y ≠ 1019 by omega,
    show x < 1012 ∨ 1018 < x by omega, show y < 1012 ∨ 1018 < y by omega]
@[simp] theorem r_isFiniteSet (s : ℕ) (hs : s < 1000) :
    Formula.Realize (isFiniteSet s) v ↔ IsFin (v s) := by
  simp [isFiniteSet, IsFin, update_of_ne, show s ≠ 1020 by omega, show s ≠ 1021 by omega,
    show s < 1012 ∨ 1019 < s by omega]
end translate

theorem realize_ch (v : ℕ → M) : Formula.Realize ch v ↔ LCH M := by
  simp [ch, LCH]

theorem realize_gch (v : ℕ → M) : Formula.Realize gch v ↔ LGCH M := by
  simp [gch, LGCH]

/-! Free-variable congruence and universal closures -/

theorem term_congr {n : ℕ} (t : setLang.Term (ℕ ⊕ Fin n)) (v v' : ℕ → M) (xs : Fin n → M)
    (h : ∀ k ∈ t.varFinsetLeft, v k = v' k) :
    t.realize (Sum.elim v xs) = t.realize (Sum.elim v' xs) := by
  cases t with
  | var a =>
    cases a with
    | inl k => simpa [Term.varFinsetLeft] using h k (by simp [Term.varFinsetLeft])
    | inr i => rfl
  | func f ts => exact (f : Empty).elim

theorem realize_congr {n : ℕ} (φ : setLang.BoundedFormula ℕ n) (v v' : ℕ → M) (xs : Fin n → M)
    (h : ∀ k ∈ φ.freeVarFinset, v k = v' k) : φ.Realize v xs ↔ φ.Realize v' xs := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [BoundedFormula.Realize]
    rw [term_congr t₁ v v' _ (fun k hk => h k (by simp [BoundedFormula.freeVarFinset, hk])),
      term_congr t₂ v v' _ (fun k hk => h k (by simp [BoundedFormula.freeVarFinset, hk]))]
  | rel R ts =>
    simp only [BoundedFormula.Realize]
    have : (fun i => (ts i).realize (Sum.elim v xs)) = (fun i => (ts i).realize (Sum.elim v' xs)) := by
      funext i
      exact term_congr (ts i) v v' _ (fun k hk => h k (by
        simp only [BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, hk⟩))
    rw [this]
  | imp f₁ f₂ ih₁ ih₂ =>
    simp only [BoundedFormula.Realize]
    rw [ih₁ _ (fun k hk => h k (by simp [BoundedFormula.freeVarFinset, hk])),
      ih₂ _ (fun k hk => h k (by simp [BoundedFormula.freeVarFinset, hk]))]
  | all f ih =>
    simp only [BoundedFormula.Realize]
    exact forall_congr' fun a => ih _ (fun k hk => h k (by simpa [BoundedFormula.freeVarFinset] using hk))

theorem formula_congr (φ : SFormula) (v v' : ℕ → M) (h : ∀ k ∈ φ.freeVarFinset, v k = v' k) :
    Formula.Realize φ v ↔ Formula.Realize φ v' := realize_congr φ v v' default h

theorem realize_of_close (φ : SFormula) (h : M ⊨ close φ) (v : ℕ → M) : Formula.Realize φ v := by
  have h' := h
  simp only [Sentence.Realize, close, Formula.realize_iAlls, Formula.realize_relabel] at h'
  have := h' (fun j => v j)
  refine (formula_congr φ _ _ ?_).1 this
  intro k hk
  have hk' : k ≤ varBound φ := by
    unfold varBound; exact Finset.le_sup (f := id) hk
  simp [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hk')]

/-! The axioms, as Lean facts -/
section axioms
variable [hM : M ⊨ (ZFC ∪ {gchSentence})]
open Function

theorem mod_ax (σ : SFormula) (hσ : σ ∈ ZFAxioms) (v : ℕ → M) : Formula.Realize σ v := by
  apply realize_of_close
  apply Theory.realize_sentence_of_mem (ZFC ∪ {gchSentence})
  left; left; exact ⟨σ, hσ, rfl⟩

theorem ax_ext (x y : M) (h : ∀ z, Mem z x ↔ Mem z y) : x = y := by
  have := mod_ax (M := M) extensionality (by simp [ZFAxioms]) (fun _ => x)
  simp [extensionality] at this
  exact this x y h

theorem ax_found (x : M) (h : ∃ y, Mem y x) : ∃ y, Mem y x ∧ ∀ z, Mem z y → ¬ Mem z x := by
  have := mod_ax (M := M) foundation (by simp [ZFAxioms]) (fun _ => x)
  simp [foundation] at this
  obtain ⟨y, hy⟩ := h
  exact this x y hy

theorem ax_pair (a b : M) : ∃ t, IsDbl t a b := by
  have := mod_ax (M := M) pairing (by simp [ZFAxioms]) (fun _ => a)
  simp [pairing] at this
  exact this a b

theorem ax_union (x : M) : ∃ u, ∀ z, Mem z u ↔ ∃ y, Mem y x ∧ Mem z y := by
  have := mod_ax (M := M) union (by simp [ZFAxioms]) (fun _ => x)
  simp [union] at this
  exact this x

theorem ax_pow (x : M) : ∃ p, IsPow p x := by
  have := mod_ax (M := M) powerset (by simp [ZFAxioms]) (fun _ => x)
  simp [powerset] at this
  exact this x

theorem ax_sep (φ : SFormula) (v : ℕ → M) (A : M) :
    ∃ B, ∀ z, Mem z B ↔ Mem z A ∧ Formula.Realize φ (update v 0 z) := by
  set N := varBound φ
  have hfv : ∀ k ∈ φ.freeVarFinset, k ≤ N := fun k hk => Finset.le_sup (f := id) hk
  have hσ : all (N+1) (ex (N+2) (all 0 (mem 0 (N+2) ⇔ (mem 0 (N+1) ⊓ φ)))) ∈ ZFAxioms := by
    left; right
    refine ⟨φ, 0, N+1, N+2, by omega, by omega, by omega, fun h => ?_, rfl⟩
    have := hfv _ h; omega
  have := mod_ax (M := M) _ hσ v
  simp only [realize_all, realize_ex, Formula.realize_iff, Formula.realize_inf, realize_mem] at this
  obtain ⟨B, hB⟩ := this A
  refine ⟨B, fun z => ?_⟩
  have := hB z
  simp only [update_self, ne_eq, show N + 2 ≠ 0 by omega, show N + 1 ≠ 0 by omega,
    show N + 2 ≠ N + 1 by omega, not_false_eq_true, update_of_ne] at this
  rw [this, update_of_ne (show N + 1 ≠ N + 2 by omega), update_self]
  apply and_congr_right; intro _
  apply formula_congr
  intro k hk
  have := hfv k hk
  by_cases h0 : k = 0
  · subst h0; simp
  · simp [update_of_ne h0, show k ≠ N + 2 by omega, show k ≠ N + 1 by omega]

theorem ax_gch : LGCH M := by
  intro s
  have : M ⊨ gchSentence := Theory.realize_sentence_of_mem (ZFC ∪ {gchSentence}) (by simp)
  exact (realize_gch (fun _ => s)).1 (realize_of_close gch this (fun _ => s)) s

end axioms

end CHA


open FirstOrder FirstOrder.Language Function


namespace CHA
open ContinuumHypothesis ContinuumHypothesis.SFormula

variable {M : Type*} [setLang.Structure M] [M ⊨ (ZFC ∪ {gchSentence})]

theorem sep_build (ψ : SFormula) (v : ℕ → M) (A : M) (P : M → Prop)
    (hP : ∀ z, Formula.Realize ψ (update v 0 z) ↔ P z) : ∃ B, ∀ z, Mem z B ↔ Mem z A ∧ P z := by
  obtain ⟨B, hB⟩ := ax_sep ψ v A
  exact ⟨B, fun z => by rw [hB, hP]⟩

theorem exists_sing (a : M) : ∃ t, IsSing t a := by
  obtain ⟨t, ht⟩ := ax_pair a a
  exact ⟨t, fun z => by rw [ht]; simp⟩

theorem exists_pair (a b : M) : ∃ z, IsPair z a b := by
  obtain ⟨s, hs⟩ := exists_sing a
  obtain ⟨d, hd⟩ := ax_pair a b
  obtain ⟨z, hz⟩ := ax_pair s d
  refine ⟨z, fun w => ?_⟩
  rw [hz]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl hs
    · exact Or.inr hd
  · rintro (h | h)
    · left; exact ax_ext _ _ fun u => by rw [h, hs]
    · right; exact ax_ext _ _ fun u => by rw [h, hd]

theorem sing_eq {s t a b : M} (hs : IsSing s a) (ht : IsSing t b) : s = t ↔ a = b := by
  constructor
  · rintro rfl
    exact (ht a).1 ((hs a).2 rfl)
  · rintro rfl
    exact ax_ext _ _ fun u => by rw [hs, ht]

theorem pair_inj {z a b a' b' : M} (h : IsPair z a b) (h' : IsPair z a' b') : a = a' ∧ b = b' := by
  obtain ⟨s, hs⟩ := exists_sing a
  obtain ⟨d, hd⟩ := ax_pair a b
  obtain ⟨d', hd'⟩ := ax_pair a' b'
  have hsz : Mem s z := (h s).2 (Or.inl hs)
  have hdz : Mem d z := (h d).2 (Or.inr hd)
  have hd'z : Mem d' z := (h' d').2 (Or.inr hd')
  -- a = a'
  have haa : a = a' := by
    rcases (h' s).1 hsz with h1 | h1
    · exact (h1 a).1 ((hs a).2 rfl)
    · have := (hs a').1 ((h1 a').2 (Or.inl rfl)); exact this.symm
  subst haa
  refine ⟨rfl, ?_⟩
  -- d' ∈ z: d' is {a} or {a,b}
  rcases (h d').1 hd'z with h1 | h1
  · -- {a,b'} = {a}, so b' = a
    have hb' : b' = a := (h1 b').1 ((hd' b').2 (Or.inr rfl))
    subst hb'
    -- d ∈ z = pair a b' with b' = a: d is {a} or {a,a}
    rcases (h' d).1 hdz with h2 | h2
    · exact (h2 b).1 ((hd b).2 (Or.inr rfl))
    · rcases (h2 b).1 ((hd b).2 (Or.inr rfl)) with h3 | h3 <;> exact h3
  · rcases (h1 b').1 ((hd' b').2 (Or.inr rfl)) with h3 | h3
    · -- b' = a; then d' = {a}; d = {a, b} ∈ z must be {a} or {a, a}
      subst h3
      rcases (h' d).1 hdz with h2 | h2
      · have := (h2 b).1 ((hd b).2 (Or.inr rfl))
        exact this
      · rcases (h2 b).1 ((hd b).2 (Or.inr rfl)) with h4 | h4 <;> exact h4
    · exact h3.symm

theorem pair_eq {z z' a b : M} (h : IsPair z a b) (h' : IsPair z' a b) : z = z' :=
  ax_ext _ _ fun u => by rw [h, h']

theorem union2 (a b : M) : ∃ u, ∀ z, Mem z u ↔ Mem z a ∨ Mem z b := by
  obtain ⟨d, hd⟩ := ax_pair a b
  obtain ⟨u, hu⟩ := ax_union d
  refine ⟨u, fun z => ?_⟩
  rw [hu]
  constructor
  · rintro ⟨y, hy, hzy⟩
    rcases (hd y).1 hy with rfl | rfl
    · exact Or.inl hzy
    · exact Or.inr hzy
  · rintro (h | h)
    · exact ⟨a, (hd a).2 (Or.inl rfl), h⟩
    · exact ⟨b, (hd b).2 (Or.inr rfl), h⟩

theorem container (A B : M) : ∃ C, ∀ a b z, Mem a A → Mem b B → IsPair z a b → Mem z C := by
  obtain ⟨U, hU⟩ := union2 A B
  obtain ⟨P1, hP1⟩ := ax_pow U
  obtain ⟨C, hC⟩ := ax_pow P1
  refine ⟨C, fun a b z ha hb hz => ?_⟩
  rw [hC]
  intro w hw
  rw [hP1]
  rcases (hz w).1 hw with h | h
  · intro u hu; rw [h] at hu; subst hu; exact (hU _).2 (Or.inl ha)
  · intro u hu; rw [h] at hu; rcases hu with rfl | rfl
    · exact (hU _).2 (Or.inl ha)
    · exact (hU _).2 (Or.inr hb)

theorem rel_build (A B : M) (ψ : SFormula) (v : ℕ → M) (R : M → M → Prop)
    (hR : ∀ z a b, Formula.Realize ψ
      (update (update (update (update (update v 3 A) 4 B) 0 z) 1 a) 2 b) ↔ R a b) :
    ∃ f, ∀ a b, PairIn f a b ↔ Mem a A ∧ Mem b B ∧ R a b := by
  obtain ⟨C, hC⟩ := container A B
  obtain ⟨F, hF⟩ := ax_sep (ex 1 (ex 2 (mem 1 3 ⊓ mem 2 4 ⊓ isPair 0 1 2 ⊓ ψ)))
    (update (update v 3 A) 4 B) C
  simp only [realize_ex, Formula.realize_inf, realize_mem] at hF
  simp at hF
  simp only [hR] at hF
  refine ⟨F, fun a b => ⟨?_, ?_⟩⟩
  · rintro ⟨z, hz, hzF⟩
    obtain ⟨_, a', b', ⟨⟨ha, hb⟩, hz'⟩, hR'⟩ := (hF z).1 hzF
    obtain ⟨rfl, rfl⟩ := pair_inj hz hz'
    exact ⟨ha, hb, hR'⟩
  · rintro ⟨ha, hb, hab⟩
    obtain ⟨z, hz⟩ := exists_pair a b
    exact ⟨z, hz, (hF z).2 ⟨hC a b z ha hb hz, a, b, ⟨⟨ha, hb⟩, hz⟩, hab⟩⟩

theorem exists_empty (a : M) : ∃ e : M, IsEmp e := by
  obtain ⟨B, hB⟩ := ax_sep (∼(eq 0 0)) (fun _ => a) a
  exact ⟨B, fun z hz => by simpa using (hB z).1 hz⟩

theorem emp_unique {e e' : M} (h : IsEmp e) (h' : IsEmp e') : e = e' :=
  ax_ext _ _ fun z => ⟨fun hz => (h z hz).elim, fun hz => (h' z hz).elim⟩

theorem succ_unique {s s' n : M} (h : IsSucc s n) (h' : IsSucc s' n) : s = s' :=
  ax_ext _ _ fun z => by rw [h, h']

theorem exists_succ (n : M) : ∃ s, IsSucc s n := by
  obtain ⟨t, ht⟩ := exists_sing n
  obtain ⟨u, hu⟩ := union2 n t
  exact ⟨u, fun z => by rw [hu, ht]⟩

theorem not_mem_self (x : M) : ¬ Mem x x := by
  intro hx
  obtain ⟨t, ht⟩ := exists_sing x
  obtain ⟨y, hy, hy'⟩ := ax_found t ⟨x, (ht x).2 rfl⟩
  rw [ht] at hy; subst hy
  exact hy' y hx ((ht y).2 rfl)

theorem succ_inj {s n m : M} (hn : IsSucc s n) (hm : IsSucc s m) : n = m := by
  by_contra hne
  have h1 : Mem n m := by
    rcases (hm n).1 ((hn n).2 (Or.inr rfl)) with h | h
    · exact h
    · exact (hne h).elim
  have h2 : Mem m n := by
    rcases (hn m).1 ((hm m).2 (Or.inr rfl)) with h | h
    · exact h
    · exact (hne h.symm).elim
  obtain ⟨t, ht⟩ := ax_pair n m
  obtain ⟨y, hy, hy'⟩ := ax_found t ⟨n, (ht n).2 (Or.inl rfl)⟩
  rcases (ht y).1 hy with rfl | rfl
  · exact hy' m h2 ((ht m).2 (Or.inr rfl))
  · exact hy' n h1 ((ht n).2 (Or.inl rfl))

theorem succ_ne_emp {s n : M} (h : IsSucc s n) : ¬ IsEmp s :=
  fun he => he n ((h n).2 (Or.inr rfl))

section omega
variable {w : M} (hw : IsOmega w)
include hw

theorem emp_mem {e : M} (he : IsEmp e) : Mem e w := by
  obtain ⟨e0, he0, hmem⟩ := hw.1.1
  rwa [emp_unique he he0]

theorem succ_mem {n s : M} (hn : Mem n w) (hs : IsSucc s n) : Mem s w := by
  obtain ⟨s0, hs0, hmem⟩ := hw.1.2 n hn
  rwa [succ_unique hs hs0]

theorem omega_ind (ψ : SFormula) (v : ℕ → M) (P : M → Prop)
    (hP : ∀ z, Formula.Realize ψ (update v 0 z) ↔ P z)
    (base : ∀ e, IsEmp e → P e) (step : ∀ n, Mem n w → P n → ∀ s, IsSucc s n → P s) :
    ∀ n, Mem n w → P n := by
  obtain ⟨B, hB⟩ := sep_build ψ v w P hP
  have hind : IsInd B := by
    refine ⟨?_, ?_⟩
    · obtain ⟨e, he, hew⟩ := hw.1.1
      exact ⟨e, he, (hB e).2 ⟨hew, base e he⟩⟩
    · intro a ha
      obtain ⟨haw, hPa⟩ := (hB a).1 ha
      obtain ⟨s, hs, hsw⟩ := hw.1.2 a haw
      exact ⟨s, hs, (hB s).2 ⟨hsw, step a haw hPa s hs⟩⟩
  intro n hn
  exact ((hB n).1 (hw.2 B hind n hn)).2

theorem omega_trans : ∀ n, Mem n w → Sub n w := by
  refine omega_ind hw (all 5 (mem 5 0 ⟹ mem 5 1)) (fun _ => w) (fun z => Sub z w)
    (fun z => by simp [Sub]) ?_ ?_
  · intro e he z hz; exact (he z hz).elim
  · intro n hn hsub s hs z hz
    rcases (hs z).1 hz with h | rfl
    · exact hsub z h
    · exact hn

theorem zero_or_succ : ∀ n, Mem n w → IsEmp n ∨ ∃ k, Mem k w ∧ IsSucc n k := by
  refine omega_ind hw (isEmpty 0 ⊔ ex 5 (mem 5 1 ⊓ isSucc 0 5)) (fun _ => w)
    (fun z => IsEmp z ∨ ∃ k, Mem k w ∧ IsSucc z k) (fun z => by simp) ?_ ?_
  · intro e he; exact Or.inl he
  · intro n hn _ s hs; exact Or.inr ⟨n, hn, hs⟩

theorem omega_unique {w' : M} (hw' : IsOmega w') : w = w' :=
  ax_ext _ _ fun z => ⟨fun h => hw.2 w' hw'.1 z h, fun h => hw'.2 w hw.1 z h⟩

end omega

theorem IsInj.mono {f x y y' : M} (h : IsInj f x y) (hy : Sub y y') : IsInj f x y' :=
  ⟨fun a ha => by obtain ⟨b, hb, hab⟩ := h.1 a ha; exact ⟨b, hy b hb, hab⟩, h.2.1, h.2.2⟩

theorem inv_inj {f x y : M} (h : IsBij f x y) : Injects y x := by
  obtain ⟨g, hg⟩ := rel_build y x (pairIn 7 2 1) (fun _ => f) (fun b a => PairIn f a b)
    (fun z a b => by simp)
  refine ⟨g, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, hab⟩ := h.2 b hb
    exact ⟨a, ha, (hg b a).2 ⟨hb, ha, hab⟩⟩
  · intro b a a' hb h1 h2
    obtain ⟨-, ha, h1⟩ := (hg b a).1 h1
    obtain ⟨-, ha', h2⟩ := (hg b a').1 h2
    exact h.1.2.2 a a' b ha ha' h1 h2
  · intro b b' a hb hb' h1 h2
    obtain ⟨-, ha, h1⟩ := (hg b a).1 h1
    obtain ⟨-, -, h2⟩ := (hg b' a).1 h2
    exact h.1.2.1 a b b' ha h1 h2

theorem id_inj {x y : M} (h : Sub x y) : Injects x y := by
  obtain ⟨g, hg⟩ := rel_build x y (eq 1 2) (fun _ => x) (fun a b => a = b)
    (fun z a b => by simp)
  refine ⟨g, ?_, ?_, ?_⟩
  · intro a ha; exact ⟨a, h a ha, (hg a a).2 ⟨ha, h a ha, rfl⟩⟩
  · intro a b b' ha h1 h2
    obtain ⟨-, -, rfl⟩ := (hg a b).1 h1
    obtain ⟨-, -, rfl⟩ := (hg a b').1 h2
    rfl
  · intro a a' b ha ha' h1 h2
    obtain ⟨-, -, rfl⟩ := (hg a b).1 h1
    obtain ⟨-, -, rfl⟩ := (hg a' a).1 h2
    rfl

section omega2
variable {w : M} (hw : IsOmega w)
include hw

theorem pigeonhole : ∀ n, Mem n w → ¬ Injects w n := by
  refine omega_ind hw (∼(injects 1 0)) (fun _ => w) (fun z => ¬ Injects w z)
    (fun z => by simp) ?_ ?_
  · intro e he ⟨g, hg⟩
    obtain ⟨e0, he0, he0w⟩ := hw.1.1
    obtain ⟨b, hb, -⟩ := hg.1 e0 he0w
    exact he b hb
  · intro n hn ih s hs ⟨g, hg⟩
    apply ih
    obtain ⟨g', hg'⟩ := rel_build w n
      (ex 5 (isSucc 5 1 ⊓ ((pairIn 6 5 2 ⊓ ∼(eq 2 4)) ⊔ (pairIn 6 5 4 ⊓ ex 8 (isEmpty 8 ⊓ pairIn 6 8 2)))))
      (fun _ => g)
      (fun m y => ∃ sm, IsSucc sm m ∧ ((PairIn g sm y ∧ ¬ y = n) ∨
        (PairIn g sm n ∧ ∃ e, IsEmp e ∧ PairIn g e y)))
      (fun z a b => by simp)
    obtain ⟨e, he⟩ := exists_empty n
    have hew : Mem e w := emp_mem hw he
    -- value of g at e is not n
    obtain ⟨ye, hye, hgye⟩ := hg.1 e hew
    refine ⟨g', ?_, ?_, ?_⟩
    · intro m hm
      obtain ⟨sm, hsm⟩ := exists_succ m
      have hsmw := succ_mem hw hm hsm
      obtain ⟨y0, hy0, hgy0⟩ := hg.1 sm hsmw
      by_cases hy0n : y0 = n
      · subst hy0n
        have hye_ne : ye ≠ y0 := by
          rintro rfl
          exact succ_ne_emp hsm (by rwa [hg.2.2 e sm ye hew hsmw hgye hgy0] at he)
        have hyen : Mem ye y0 := by
          rcases (hs ye).1 hye with h | h
          · exact h
          · exact (hye_ne h).elim
        exact ⟨ye, hyen, (hg' m ye).2 ⟨hm, hyen, sm, hsm, Or.inr ⟨hgy0, e, he, hgye⟩⟩⟩
      · have : Mem y0 n := by
          rcases (hs y0).1 hy0 with h | h
          · exact h
          · exact (hy0n h).elim
        exact ⟨y0, this, (hg' m y0).2 ⟨hm, this, sm, hsm, Or.inl ⟨hgy0, hy0n⟩⟩⟩
    · intro m y y' hm h1 h2
      obtain ⟨-, -, sm, hsm, h1⟩ := (hg' m y).1 h1
      obtain ⟨-, -, sm', hsm', h2⟩ := (hg' m y').1 h2
      obtain rfl := succ_unique hsm hsm'
      have hsmw := succ_mem hw hm hsm
      rcases h1 with ⟨h1, h1n⟩ | ⟨h1, e1, he1, h1'⟩ <;>
        rcases h2 with ⟨h2, h2n⟩ | ⟨h2, e2, he2, h2'⟩
      · exact hg.2.1 sm y y' hsmw h1 h2
      · exact (h1n (hg.2.1 sm y n hsmw h1 h2)).elim
      · exact (h2n (hg.2.1 sm y' n hsmw h2 h1)).elim
      · obtain rfl := emp_unique he1 he2
        exact hg.2.1 e1 y y' (emp_mem hw he1) h1' h2'
    · intro m m' y hm hm' h1 h2
      obtain ⟨-, -, sm, hsm, h1⟩ := (hg' m y).1 h1
      obtain ⟨-, -, sm', hsm', h2⟩ := (hg' m' y).1 h2
      have hsmw := succ_mem hw hm hsm
      have hsmw' := succ_mem hw hm' hsm'
      rcases h1 with ⟨h1, h1n⟩ | ⟨h1, e1, he1, h1'⟩ <;>
        rcases h2 with ⟨h2, h2n⟩ | ⟨h2, e2, he2, h2'⟩
      · have := hg.2.2 sm sm' y hsmw hsmw' h1 h2
        subst this; exact succ_inj hsm hsm'
      · have := hg.2.2 sm e2 y hsmw (emp_mem hw he2) h1 h2'
        subst this; exact (succ_ne_emp hsm he2).elim
      · have := hg.2.2 sm' e1 y hsmw' (emp_mem hw he1) h2 h1'
        subst this; exact (succ_ne_emp hsm' he1).elim
      · have := hg.2.2 sm sm' n hsmw hsmw' h1 h2
        subst this; exact succ_inj hsm hsm'

theorem omega_not_fin : ¬ IsFin w := by
  rintro ⟨w', hw', n, hn, f, hf⟩
  obtain rfl := omega_unique hw hw'
  exact pigeonhole hw n hn (inv_inj hf)

theorem fin_injects {x : M} (hx : IsFin x) : Injects x w := by
  obtain ⟨w', hw', n, hn, f, hf⟩ := hx
  obtain rfl := omega_unique hw hw'
  obtain ⟨g, hg⟩ := inv_inj hf
  exact ⟨g, hg.mono (omega_trans hw n hn)⟩

end omega2

end CHA


open FirstOrder FirstOrder.Language Function


namespace CHA
open ContinuumHypothesis ContinuumHypothesis.SFormula

variable {M : Type*} [setLang.Structure M] [M ⊨ (ZFC ∪ {gchSentence})]

section main
variable {w : M} (hw : IsOmega w)
include hw

theorem not_fin_two {x : M} (hx : ¬ IsFin x) : ∃ b c, Mem b x ∧ Mem c x ∧ b ≠ c := by
  by_contra hcon
  push Not at hcon
  apply hx
  obtain ⟨e, he⟩ := exists_empty x
  have hew := emp_mem hw he
  by_cases hne : ∃ b, Mem b x
  · obtain ⟨b, hb⟩ := hne
    obtain ⟨s, hs⟩ := exists_succ e
    have hsw := succ_mem hw hew hs
    have hs' : ∀ a, Mem a s → a = e := fun a ha => by
      rcases (hs a).1 ha with h | h
      · exact (he a h).elim
      · exact h
    obtain ⟨f, hf⟩ := rel_build s x (eq 1 1) (fun _ => x) (fun _ _ => True) (fun z a b => by simp)
    refine ⟨w, hw, s, hsw, f, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro a ha; exact ⟨b, hb, (hf a b).2 ⟨ha, hb, trivial⟩⟩
    · intro a y y' ha h1 h2
      exact hcon y y' ((hf a y).1 h1).2.1 ((hf a y').1 h2).2.1
    · intro a a' y ha ha' _ _; rw [hs' a ha, hs' a' ha']
    · intro y hy
      have hes : Mem e s := (hs e).2 (Or.inr rfl)
      exact ⟨e, hes, (hf e y).2 ⟨hes, hy, trivial⟩⟩
  · push Not at hne
    refine ⟨w, hw, e, hew, e, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro a ha; exact (he a ha).elim
    · intro a _ _ ha; exact (he a ha).elim
    · intro a _ _ ha; exact (he a ha).elim
    · intro y hy; exact (hne y hy).elim

end main

/-- The Cantor-type step: `x ∪ {x}` is not equinumerous with `𝒫(x)` when `x` has two
distinct elements. -/
theorem not_equinum_succ_pow {x t q b c : M} (hbx : Mem b x) (hcx : Mem c x) (hbc : b ≠ c)
    (ht : ∀ z, Mem z t ↔ Mem z x ∨ z = x) (hq : IsPow q x) (f : M) (hf : IsBij f t q) : False := by
  have hxt : Mem x t := (ht x).2 (Or.inr rfl)
  have hsub : ∀ a, Mem a x → Mem a t := fun a ha => (ht a).2 (Or.inl ha)
  have hfun : ∀ a Z Z', Mem a x → PairIn f a Z → PairIn f a Z' → Z = Z' :=
    fun a Z Z' ha h1 h2 => hf.1.2.1 a Z Z' (hsub a ha) h1 h2
  obtain ⟨q0, hq0, hfq0⟩ := hf.1.1 x hxt
  have Lsurj : ∀ Z, Sub Z x → Z ≠ q0 → ∃ a, Mem a x ∧ PairIn f a Z := by
    intro Z hZ hZq
    obtain ⟨u, hu, hfu⟩ := hf.2 Z ((hq Z).2 hZ)
    rcases (ht u).1 hu with h | rfl
    · exact ⟨u, h, hfu⟩
    · exact (hZq (hf.1.2.1 u Z q0 hxt hfu hfq0)).elim
  obtain ⟨Y, hY⟩ := sep_build (all 5 (pairIn 6 0 5 ⟹ ∼(mem 0 5))) (fun _ => f) x
    (fun a => ∀ Z, PairIn f a Z → ¬ Mem a Z) (fun z => by simp)
  have key : ∀ a Z, Mem a x → PairIn f a Z → (Mem a Y ↔ ¬ Mem a Z) := by
    intro a Z ha haZ
    rw [hY]
    constructor
    · rintro ⟨-, h⟩; exact h Z haZ
    · intro h; exact ⟨ha, fun Z' hZ' => by rwa [hfun a Z' Z ha hZ' haZ]⟩
  have diag : ∀ Z a, Mem a x → PairIn f a Z → ¬ (Mem a Z ↔ Mem a Y) := by
    intro Z a ha haZ h
    have := key a Z ha haZ
    tauto
  have hYsub : Sub Y x := fun a ha => ((hY a).1 ha).1
  have hYq : Y = q0 := by
    by_contra hne
    obtain ⟨a, ha, haY⟩ := Lsurj Y hYsub hne
    exact diag Y a ha haY Iff.rfl
  subst hYq
  -- the sets `Z_d`
  have hZd : ∀ d, Mem d x → ∃ Zd, (∀ a, Mem a Zd ↔ Mem a x ∧ (Mem a Y ↔ a ≠ d)) ∧ PairIn f d Zd := by
    intro d hd
    obtain ⟨Zd, hZd⟩ := sep_build (mem 0 7 ⇔ ∼(eq 0 8)) (update (fun _ => Y) 8 d) x
      (fun a => Mem a Y ↔ a ≠ d) (fun z => by simp)
    refine ⟨Zd, hZd, ?_⟩
    have hne : Zd ≠ Y := by
      intro h
      have := hZd d
      rw [h] at this
      simp only [ne_eq, not_true_eq_false, iff_false] at this
      tauto
    obtain ⟨a, ha, haZ⟩ := Lsurj Zd (fun a h => ((hZd a).1 h).1) hne
    by_cases had : a = d
    · subst had; exact haZ
    · exfalso
      apply diag Zd a ha haZ
      rw [hZd]
      simp [ha, had]
  obtain ⟨Z, hZ⟩ := sep_build (mem 0 7 ⇔ (∼(eq 0 8) ⊓ ∼(eq 0 9)))
    (update (update (fun _ => Y) 8 b) 9 c) x
    (fun a => Mem a Y ↔ (a ≠ b ∧ a ≠ c)) (fun z => by simp)
  have hne : Z ≠ Y := by
    intro h
    have := hZ b
    rw [h] at this
    simp only [ne_eq, not_true_eq_false, false_and, iff_false] at this
    tauto
  obtain ⟨a, ha, haZ⟩ := Lsurj Z (fun a h => ((hZ a).1 h).1) hne
  by_cases hab : a = b
  · subst hab
    obtain ⟨Zb, hZb, hfb⟩ := hZd a ha
    have := hfun a Z Zb ha haZ hfb
    subst this
    have h1 := hZ c
    have h2 := hZb c
    rw [h1] at h2
    have hca : c ≠ a := fun h => hbc h.symm
    simp only [ne_eq, hca, not_false_eq_true, true_and, and_true, hcx] at h2
    tauto
  · by_cases hac : a = c
    · subst hac
      obtain ⟨Zc, hZc, hfc⟩ := hZd a ha
      have := hfun a Z Zc ha haZ hfc
      subst this
      have h1 := hZ b
      have h2 := hZc b
      rw [h1] at h2
      simp only [ne_eq, hbc, not_false_eq_true, and_true, true_and, hbx] at h2
      tauto
    · apply diag Z a ha haZ
      rw [hZ]
      simp [ha, hab, hac]

section main2
variable {w : M} (hw : IsOmega w)
include hw

/-- A non-finite set admits an injection into itself missing a point. -/
theorem dedekind {x : M} (hx : ¬ IsFin x) :
    ∃ f c0, IsInj f x x ∧ Mem c0 x ∧ ∀ a, Mem a x → ¬ PairIn f a c0 := by
  obtain ⟨b, c, hb, hc, hbc⟩ := not_fin_two hw hx
  obtain ⟨sx, hsx⟩ := exists_sing x
  obtain ⟨t, ht0⟩ := union2 x sx
  have ht : ∀ z, Mem z t ↔ Mem z x ∨ z = x := fun z => by rw [ht0, hsx]
  obtain ⟨q, hq⟩ := ax_pow x
  have inj1 : Injects x t := id_inj fun a ha => (ht a).2 (Or.inl ha)
  have inj2 : Injects t q := by
    obtain ⟨g, hg⟩ := rel_build t q ((mem 1 5 ⊓ isSingleton 2 1) ⊔ (∼(mem 1 5) ⊓ isEmpty 2))
      (fun _ => x) (fun u v => (Mem u x ∧ IsSing v u) ∨ (¬ Mem u x ∧ IsEmp v)) (fun z a b => by simp)
    refine ⟨g, ?_, ?_, ?_⟩
    · intro u hu
      by_cases hux : Mem u x
      · obtain ⟨s, hs⟩ := exists_sing u
        have hsq : Mem s q := (hq s).2 fun z hz => by rw [hs] at hz; subst hz; exact hux
        exact ⟨s, hsq, (hg u s).2 ⟨hu, hsq, Or.inl ⟨hux, hs⟩⟩⟩
      · obtain ⟨e, he⟩ := exists_empty u
        have heq : Mem e q := (hq e).2 fun z hz => (he z hz).elim
        exact ⟨e, heq, (hg u e).2 ⟨hu, heq, Or.inr ⟨hux, he⟩⟩⟩
    · intro u v v' hu h1 h2
      obtain ⟨-, -, h1⟩ := (hg u v).1 h1
      obtain ⟨-, -, h2⟩ := (hg u v').1 h2
      rcases h1 with ⟨h1x, h1⟩ | ⟨h1x, h1⟩ <;> rcases h2 with ⟨h2x, h2⟩ | ⟨h2x, h2⟩
      · exact (sing_eq h1 h2).2 rfl
      · exact (h2x h1x).elim
      · exact (h1x h2x).elim
      · exact emp_unique h1 h2
    · intro u u' v hu hu' h1 h2
      obtain ⟨-, -, h1⟩ := (hg u v).1 h1
      obtain ⟨-, -, h2⟩ := (hg u' v).1 h2
      rcases h1 with ⟨h1x, h1⟩ | ⟨h1x, h1⟩ <;> rcases h2 with ⟨h2x, h2⟩ | ⟨h2x, h2⟩
      · exact ((sing_eq h1 h2).1 rfl)
      · exact (h2 u ((h1 u).2 rfl)).elim
      · exact (h1 u' ((h2 u').2 rfl)).elim
      · rcases (ht u).1 hu with h | rfl
        · exact (h1x h).elim
        · rcases (ht u').1 hu' with h' | rfl
          · exact (h2x h').elim
          · rfl
  rcases ax_gch x hx q hq t ⟨inj1, inj2⟩ with ⟨f, hf⟩ | ⟨f, hf⟩
  · have hxt : Mem x t := (ht x).2 (Or.inr rfl)
    have hsub : ∀ a, Mem a x → Mem a t := fun a ha => (ht a).2 (Or.inl ha)
    obtain ⟨c0, hc0, hfc0⟩ := hf.1.1 x hxt
    refine ⟨f, c0, ⟨fun a ha => hf.1.1 a (hsub a ha), fun a y y' ha => hf.1.2.1 a y y' (hsub a ha),
      fun a a' y ha ha' => hf.1.2.2 a a' y (hsub a ha) (hsub a' ha')⟩, hc0, ?_⟩
    intro a ha hac
    have := hf.1.2.2 a x c0 (hsub a ha) hxt hac hfc0
    subst this
    exact not_mem_self a ha
  · exact (not_equinum_succ_pow hb hc hbc ht hq f hf).elim

def Closed (w x f e c0 Q : M) : Prop :=
  (∀ z, IsPair z e c0 → Mem z Q) ∧
  (∀ m y s y' z z', Mem m w → Mem y x → IsPair z m y → Mem z Q → IsSucc s m → PairIn f y y' →
    IsPair z' s y' → Mem z' Q)

omit hw in
theorem realize_closed (v : ℕ → M) :
    Formula.Realize (all 11 (isPair 11 12 13 ⟹ mem 11 10) ⊓
      all 14 (all 15 (all 16 (all 17 (all 18 (all 19 ((mem 14 7 ⊓ mem 15 8 ⊓ isPair 18 14 15 ⊓
        mem 18 10 ⊓ isSucc 16 14 ⊓ pairIn 9 15 17 ⊓ isPair 19 16 17) ⟹ mem 19 10))))))) v ↔
      Closed (v 7) (v 8) (v 9) (v 12) (v 13) (v 10) := by
  simp [Closed]

/-- Internal recursion: an injection `f : x → x` missing `c0` yields `ω ↪ x`. -/
theorem rec_inj {x f c0 : M} (hf : IsInj f x x) (hc0 : Mem c0 x)
    (hnot : ∀ a, Mem a x → ¬ PairIn f a c0) : Injects w x := by
  obtain ⟨e, he⟩ := exists_empty x
  have hew := emp_mem hw he
  have fx : ∀ y y', Mem y x → PairIn f y y' → Mem y' x := by
    intro y y' hy hyy'
    obtain ⟨y'', hy'', h''⟩ := hf.1 y hy
    rwa [hf.2.1 y y' y'' hy hyy' h'']
  obtain ⟨C, hC⟩ := container w x
  obtain ⟨C', hC'⟩ := sep_build (ex 5 (ex 6 (mem 5 7 ⊓ mem 6 8 ⊓ isPair 0 5 6)))
    (update (fun _ => w) 8 x) C (fun z => ∃ m y, Mem m w ∧ Mem y x ∧ IsPair z m y)
    (fun z => by simp [and_assoc])
  obtain ⟨R, hR⟩ := sep_build
    (all 10 ((all 11 (isPair 11 12 13 ⟹ mem 11 10) ⊓
      all 14 (all 15 (all 16 (all 17 (all 18 (all 19 ((mem 14 7 ⊓ mem 15 8 ⊓ isPair 18 14 15 ⊓
        mem 18 10 ⊓ isSucc 16 14 ⊓ pairIn 9 15 17 ⊓ isPair 19 16 17) ⟹ mem 19 10))))))) ⟹ mem 0 10))
    (update (update (update (update (fun _ => w) 8 x) 9 f) 12 e) 13 c0) C'
    (fun z => ∀ Q, Closed w x f e c0 Q → Mem z Q)
    (fun z => by
      simp only [realize_all, Formula.realize_imp, realize_mem]
      apply forall_congr'; intro Q
      rw [realize_closed]
      simp)
  have closedR : Closed w x f e c0 R := by
    refine ⟨?_, ?_⟩
    · intro z hz
      exact (hR z).2 ⟨(hC' z).2 ⟨hC e c0 z hew hc0 hz, e, c0, hew, hc0, hz⟩, fun Q hQ => hQ.1 z hz⟩
    · intro m y s y' z z' hm hy hz hzR hs hyy' hz'
      have hsw := succ_mem hw hm hs
      have hy'x := fx y y' hy hyy'
      refine (hR z').2 ⟨(hC' z').2 ⟨hC s y' z' hsw hy'x hz', s, y', hsw, hy'x, hz'⟩, fun Q hQ => ?_⟩
      exact hQ.2 m y s y' z z' hm hy hz (((hR z).1 hzR).2 Q hQ) hs hyy' hz'
  have minR : ∀ Q, Closed w x f e c0 Q → ∀ z, Mem z R → Mem z Q :=
    fun Q hQ z hz => ((hR z).1 hz).2 Q hQ
  have memR : ∀ m y, PairIn R m y → Mem m w ∧ Mem y x := by
    rintro m y ⟨z, hz, hzR⟩
    obtain ⟨-, m', y', hm', hy', hz'⟩ := (hC' z).1 ((hR z).1 hzR).1
    obtain ⟨rfl, rfl⟩ := pair_inj hz hz'
    exact ⟨hm', hy'⟩
  have stepR : ∀ m y s y', PairIn R m y → IsSucc s m → PairIn f y y' → PairIn R s y' := by
    rintro m y s y' ⟨z, hz, hzR⟩ hs hyy'
    obtain ⟨hm, hy⟩ := memR m y ⟨z, hz, hzR⟩
    obtain ⟨z', hz'⟩ := exists_pair s y'
    exact ⟨z', hz', closedR.2 m y s y' z z' hm hy hz hzR hs hyy' hz'⟩
  have baseR : PairIn R e c0 := by
    obtain ⟨z, hz⟩ := exists_pair e c0
    exact ⟨z, hz, closedR.1 z hz⟩
  have remove : ∀ m0 y0, PairIn R m0 y0 → ¬ (m0 = e ∧ y0 = c0) →
      (∀ m y s y', PairIn R m y → IsSucc s m → PairIn f y y' → ¬ (s = m0 ∧ y' = y0)) → False := by
    intro m0 y0 h0 hbase hstep
    obtain ⟨R', hR'⟩ := sep_build (∼(isPair 0 5 6)) (update (fun _ => m0) 6 y0) R
      (fun z => ¬ IsPair z m0 y0) (fun z => by simp)
    have hcl : Closed w x f e c0 R' := by
      refine ⟨?_, ?_⟩
      · intro z hz
        refine (hR' z).2 ⟨closedR.1 z hz, fun hz0 => hbase ?_⟩
        obtain ⟨h1, h2⟩ := pair_inj hz hz0
        exact ⟨h1.symm, h2.symm⟩
      · intro m y s y' z z' hm hy hz hzR' hs hyy' hz'
        obtain ⟨hzR, -⟩ := (hR' z).1 hzR'
        refine (hR' z').2 ⟨closedR.2 m y s y' z z' hm hy hz hzR hs hyy' hz', fun hz0 => ?_⟩
        obtain ⟨h1, h2⟩ := pair_inj hz' hz0
        exact hstep m y s y' ⟨z, hz, hzR⟩ hs hyy' ⟨h1, h2⟩
    obtain ⟨z0, hz0, hz0R⟩ := h0
    exact ((hR' z0).1 (minR R' hcl z0 hz0R)).2 hz0
  -- functionality
  have funR : ∀ m, Mem m w → ∃ y, Mem y x ∧ PairIn R m y ∧ ∀ y', PairIn R m y' → y' = y := by
    refine omega_ind hw (ex 5 (mem 5 8 ⊓ pairIn 10 0 5 ⊓ all 6 (pairIn 10 0 6 ⟹ eq 6 5)))
      (update (fun _ => x) 10 R) _ (fun z => by simp [and_assoc]) ?_ ?_
    · intro e' he'
      obtain rfl := emp_unique he' he
      refine ⟨c0, hc0, baseR, fun y' hy' => ?_⟩
      by_contra hne
      exact remove e' y' hy' (fun h => hne h.2) fun m y s y' _ hs _ h => succ_ne_emp hs (h.1 ▸ he')
    · rintro n hn ⟨yn, hyn, hRn, huniq⟩ s hs
      obtain ⟨y1, hy1, hfy1⟩ := hf.1 yn hyn
      refine ⟨y1, hy1, stepR n yn s y1 hRn hs hfy1, fun y' hy' => ?_⟩
      by_contra hne
      refine remove s y' hy' (fun h => succ_ne_emp hs (h.1 ▸ he)) ?_
      rintro m y s' y'' hmy hs' hyy'' ⟨rfl, rfl⟩
      obtain rfl := succ_inj hs hs'
      obtain rfl := huniq y hmy
      exact hne (hf.2.1 y y'' y1 hyn hyy'' hfy1)
  have succR : ∀ m s y, Mem m w → IsSucc s m → PairIn R s y →
      ∃ ym, Mem ym x ∧ PairIn R m ym ∧ PairIn f ym y := by
    intro m s y hm hs hsy
    obtain ⟨ym, hym, hRm, -⟩ := funR m hm
    obtain ⟨y1, hy1, hfy1⟩ := hf.1 ym hym
    obtain ⟨y2, -, -, hu⟩ := funR s (succ_mem hw hm hs)
    have e1 := hu y hsy
    have e2 := hu y1 (stepR m ym s y1 hRm hs hfy1)
    exact ⟨ym, hym, hRm, by rw [e1, ← e2]; exact hfy1⟩
  have zeroR : ∀ y, PairIn R e y → y = c0 := by
    intro y hy
    obtain ⟨y2, -, -, hu⟩ := funR e hew
    rw [hu y hy, hu c0 baseR]
  -- injectivity
  have injR : ∀ n, Mem n w → ∀ m y, Mem m w → PairIn R n y → PairIn R m y → n = m := by
    refine omega_ind hw (all 5 (all 6 ((mem 5 7 ⊓ pairIn 10 0 6 ⊓ pairIn 10 5 6) ⟹ eq 0 5)))
      (update (fun _ => w) 10 R) _ (fun z => by simp) ?_ ?_
    · intro e' he' m y hm h1 h2
      obtain rfl := emp_unique he' he
      rcases zero_or_succ hw m hm with hm0 | ⟨k, hk, hks⟩
      · exact emp_unique he' hm0
      · obtain ⟨yk, hyk, -, hfk⟩ := succR k m y hk hks h2
        exact (hnot yk hyk (zeroR y h1 ▸ hfk)).elim
    · intro n hn ih s hs m y hm h1 h2
      obtain ⟨yn, hyn, hRn, hfn⟩ := succR n s y hn hs h1
      rcases zero_or_succ hw m hm with hm0 | ⟨k, hk, hks⟩
      · obtain rfl := emp_unique hm0 he
        exact (hnot yn hyn (zeroR y h2 ▸ hfn)).elim
      · obtain ⟨yk, hyk, hRk, hfk⟩ := succR k m y hk hks h2
        obtain rfl := hf.2.2 yn yk y hyn hyk hfn hfk
        obtain rfl := ih k yn hk hRn hRk
        exact succ_unique hs hks
  refine ⟨R, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨y, hy, hRy, -⟩ := funR m hm
    exact ⟨y, hy, hRy⟩
  · intro m y y' hm h1 h2
    obtain ⟨y0, -, -, hu⟩ := funR m hm
    rw [hu y h1, hu y' h2]
  · intro m m' y hm hm' h1 h2
    exact injR m hm m' y hm' h1 h2

end main2

theorem lch : LCH M := by
  intro w hw p hp x hxp
  by_cases hfin : IsFin x
  · exact Or.inl (fin_injects hw hfin)
  · obtain ⟨f, c0, hf, hc0, hnot⟩ := dedekind hw hfin
    have h1 : Injects w x := rec_inj hw hf hc0 hnot
    have h2 : Injects x p := id_inj hxp
    rcases ax_gch w (omega_not_fin hw) p hp x ⟨h1, h2⟩ with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact Or.inl ⟨g, hg.1⟩
    · exact Or.inr (inv_inj hg)

end CHA


open FirstOrder FirstOrder.Language ContinuumHypothesis in
theorem solution : (ZFC ∪ {gchSentence}) ⊨ᵇ chSentence := by
  rw [Theory.models_sentence_iff]
  intro M
  simp only [Sentence.Realize, chSentence, SFormula.close, Formula.realize_iAlls, Formula.realize_relabel]
  intro i
  exact (CHA.realize_ch _).2 CHA.lch
