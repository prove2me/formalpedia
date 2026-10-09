-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityD.m_convex_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T07:37:23.155524+00:00
-- url     : https://prove2.me/submissions/14465861-49ee-4e99-bd9b-cb6067e88bf9

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConvexConjE
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SubDifferentialZEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_PhiR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRSmall
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_PhiGen
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GGen

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace P0fc

open DiscreteConvex.ConjugacyDualityD

/-! ## Generic EReal helpers (copied from our proved sibling 2f7fafd3) -/

lemma sInf_setOf {ι : Sort*} (f : ι → EReal) : sInf {t : EReal | ∃ x, t = f x} = ⨅ x, f x := by
  have : {t : EReal | ∃ x, t = f x} = Set.range f := by ext t; simp [eq_comm]
  rw [this, sInf_range]

lemma sSup_setOf {ι : Sort*} (f : ι → EReal) : sSup {t : EReal | ∃ x, t = f x} = ⨆ x, f x := by
  have : {t : EReal | ∃ x, t = f x} = Set.range f := by ext t; simp [eq_comm]
  rw [this, sSup_range]

lemma neg_iSup' {ι : Sort*} (f : ι → EReal) : -(⨆ i, f i) = ⨅ i, -(f i) := by
  apply le_antisymm
  · exact le_iInf fun i => EReal.neg_le_neg_iff.mpr (le_iSup f i)
  · rw [EReal.le_neg]
    exact iSup_le fun i => EReal.le_neg.mp (iInf_le (fun j => -(f j)) i)

lemma add_cancel (x : EReal) (c : ℝ) : (x + (c : EReal)) + ((-c : ℝ) : EReal) = x := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe a =>
    rw [← EReal.coe_add, ← EReal.coe_add]
    congr 1
    ring

lemma iInf_add_coe {ι : Sort*} (f : ι → EReal) (c : ℝ) :
    (⨅ i, f i) + (c : EReal) = ⨅ i, (f i + (c : EReal)) := by
  apply le_antisymm
  · exact le_iInf fun i => by gcongr; exact iInf_le f i
  · have h : (⨅ i, (f i + (c : EReal))) + ((-c : ℝ) : EReal) ≤ ⨅ i, f i := by
      refine le_iInf fun i => ?_
      calc (⨅ i, (f i + (c : EReal))) + ((-c : ℝ) : EReal)
          ≤ (f i + (c : EReal)) + ((-c : ℝ) : EReal) := by gcongr; exact iInf_le _ i
        _ = f i := add_cancel _ _
    have h2 : (⨅ i, (f i + (c : EReal))) + ((-c : ℝ) : EReal) + (c : EReal) ≤ (⨅ i, f i) + (c : EReal) := by gcongr
    have e : (⨅ i, (f i + (c : EReal))) + ((-c : ℝ) : EReal) + (c : EReal)
        = ⨅ i, (f i + (c : EReal)) := by
      have := add_cancel (⨅ i, (f i + (c : EReal))) (-c)
      simpa using this
    rwa [e] at h2

/-- Proved sibling 2f7fafd3 (general_duality_relations), proof copied. -/
theorem gen_dual {V : Type u} [Fintype V] [DecidableEq V] (F : (V → ℤ) → (V → ℤ) → WithTop ℝ) :
    (∀ y : V → ℤ, GGen F y = -(ConvexConjE (PhiGen F) (fun v => -y v))) ∧
    (sSup {t : EReal | ∃ y, t = GGen F y} = ConvexConjE (ConvexConjE (PhiGen F)) 0) := by
  have h1 : ∀ y : V → ℤ, GGen F y = -(ConvexConjE (PhiGen F) (fun v => -y v)) := by
    intro y
    simp only [GGen, KGen, PhiGen, ConvexConjE, sInf_setOf, sSup_setOf, neg_iSup']
    rw [iInf_comm]
    refine iInf_congr fun u => ?_
    rw [EReal.neg_sub (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
      add_comm, ← EReal.coe_neg, iInf_add_coe]
    refine iInf_congr fun x => ?_
    congr 2
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have h2 : sSup {t : EReal | ∃ y, t = GGen F y} = ConvexConjE (ConvexConjE (PhiGen F)) 0 := by
    rw [sSup_setOf]
    simp only [h1]
    conv_rhs => rw [ConvexConjE, sSup_setOf]
    simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, EReal.coe_zero,
      zero_sub]
    exact (neg_surjective (G := V → ℤ)).iSup_comp (fun y => -(ConvexConjE (PhiGen F) y))
  exact ⟨h1, h2⟩

/-! ## SD-C: Fenchel–Young bookkeeping for an EReal function with a subgradient at 0 -/

lemma sub_le_iff' (s a : ℝ) (e : EReal) :
    (s : EReal) - e ≤ ((-a : ℝ) : EReal) ↔ (s : EReal) ≤ e - (a : EReal) := by
  induction e using EReal.rec with
  | bot => simp
  | top => simp
  | coe b =>
    rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

lemma conj_le_iff {V : Type u} [Fintype V] [DecidableEq V] (φ : (V → ℤ) → EReal) (a : ℝ)
    (ha : φ (fun _ => 0) = (a : EReal)) (q : V → ℤ) :
    ConvexConjE φ q ≤ ((-a : ℝ) : EReal) ↔ q ∈ SubDifferentialZEReal φ (fun _ => 0) := by
  simp only [ConvexConjE, SubDifferentialZEReal, Set.mem_ofPred_eq, ha, sSup_le_iff,
    forall_exists_index]
  constructor
  · intro h x
    have := (sub_le_iff' _ a (φ x)).1 (h _ x rfl)
    simpa [Int.cast_zero, sub_zero] using this
  · intro h t x ht
    subst ht
    rw [sub_le_iff']
    simpa [Int.cast_zero, sub_zero] using h x

lemma conj_ge {V : Type u} [Fintype V] [DecidableEq V] (φ : (V → ℤ) → EReal) (a : ℝ)
    (ha : φ (fun _ => 0) = (a : EReal)) (q : V → ℤ) :
    ((-a : ℝ) : EReal) ≤ ConvexConjE φ q := by
  unfold ConvexConjE
  refine le_sSup_of_le ⟨fun _ => 0, rfl⟩ ?_
  rw [ha]
  simp

theorem biconj_of_subgradient {V : Type u} [Fintype V] [DecidableEq V]
    (φ : (V → ℤ) → EReal) (a : ℝ) (ha : φ (fun _ => 0) = (a : EReal))
    (hsub : (SubDifferentialZEReal φ (fun _ => 0)).Nonempty) :
    φ (fun _ => 0) = ConvexConjE (ConvexConjE φ) (fun _ => 0) ∧
      {y : V → ℤ | -(ConvexConjE φ (fun v => -y v)) =
          sSup {t : EReal | ∃ y' : V → ℤ, t = -(ConvexConjE φ (fun v => -y' v))}} =
        (fun p => fun v => -p v) '' SubDifferentialZEReal φ (fun _ => 0) := by
  obtain ⟨y0, hy0⟩ := hsub
  have hFY : ∀ q, -(ConvexConjE φ q) ≤ (a : EReal) := by
    intro q
    rw [EReal.neg_le, ← EReal.coe_neg]
    exact conj_ge φ a ha q
  have hy0' : ConvexConjE φ y0 ≤ ((-a : ℝ) : EReal) := (conj_le_iff φ a ha y0).2 hy0
  have hy0'' : (a : EReal) ≤ -(ConvexConjE φ y0) := by
    rw [EReal.le_neg, ← EReal.coe_neg]; exact hy0'
  have hbi : ConvexConjE (ConvexConjE φ) (fun _ => 0) = (a : EReal) := by
    unfold ConvexConjE
    simp only [Int.cast_zero, zero_mul, Finset.sum_const_zero, EReal.coe_zero, zero_sub]
    apply le_antisymm
    · refine sSup_le ?_
      rintro t ⟨q, rfl⟩
      exact hFY q
    · exact le_sSup_of_le ⟨y0, rfl⟩ hy0''
  have hsup : sSup {t : EReal | ∃ y' : V → ℤ, t = -(ConvexConjE φ (fun v => -y' v))} = (a : EReal) := by
    apply le_antisymm
    · refine sSup_le ?_
      rintro t ⟨q, rfl⟩
      exact hFY _
    · refine le_sSup_of_le ⟨fun v => -y0 v, ?_⟩ hy0''
      simp
  refine ⟨by rw [ha, hbi], ?_⟩
  rw [hsup]
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hy
    refine ⟨fun v => -y v, ?_, by simp⟩
    rw [← conj_le_iff φ a ha]
    have : ConvexConjE φ (fun v => -y v) = ((-a : ℝ) : EReal) := by
      rw [EReal.coe_neg, ← hy, neg_neg]
    exact this.le
  · rintro ⟨p, hp, rfl⟩
    have h1 := (conj_le_iff φ a ha p).2 hp
    have h2 := conj_ge φ a ha p
    have : ConvexConjE φ p = ((-a : ℝ) : EReal) := le_antisymm h1 h2
    simp only [neg_neg]
    have e : (fun v => p v) = p := rfl
    rw [e, this, EReal.coe_neg, neg_neg]


/-! ## K: exchange machinery for M-convex functions -/

section K

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `x - χa + χb` -/
def ex (x : V → ℤ) (a b : V) : V → ℤ := fun w => x w - IndicatorVec {a} w + IndicatorVec {b} w

/-- `x - χA + χW` -/
def exs (x : V → ℤ) (A W : Finset V) : V → ℤ := fun w => x w - IndicatorVec A w + IndicatorVec W w

/-- the pairing `⟨p, x⟩` -/
def lin (p : V → ℝ) (x : V → ℤ) : ℝ := ∑ i, p i * (x i : ℝ)

/-- l1 distance -/
def dist1 (x y : V → ℤ) : ℕ := ∑ i, (x i - y i).natAbs

lemma mem_suppPos {x y : V → ℤ} {u : V} : u ∈ SuppPos x y ↔ y u < x u :=
  ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩

lemma mem_suppNeg {x y : V → ℤ} {u : V} : u ∈ SuppNeg x y ↔ x u < y u :=
  ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩

lemma mexc' {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) {x y : V → ℤ}
    (hx : f x ≠ ⊤) (hy : f y ≠ ⊤) {u : V} (hu : u ∈ SuppPos x y) :
    ∃ v ∈ SuppNeg x y, f (ex x u v) + f (ex y v u) ≤ f x + f y := by
  obtain ⟨v, hv, h⟩ := hf x hx y hy u hu
  refine ⟨v, hv, ?_⟩
  have e : ex y v u = (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w) := by
    funext w; simp only [ex]; ring
  rw [e]
  exact h

lemma ex_self (x : V → ℤ) (a : V) : ex x a a = x := by
  funext w; simp only [ex]; ring

lemma ex_ex_cancel (x : V → ℤ) (a b c : V) : ex (ex x a b) b c = ex x a c := by
  funext w; simp only [ex]; ring

lemma ex_ex_swap (x : V → ℤ) (a b c : V) : ex (ex x a b) c a = ex x c b := by
  funext w; simp only [ex]; ring

lemma ex_comm (x : V → ℤ) (a b c d : V) : ex (ex x a b) c d = ex (ex x c d) a b := by
  funext w; simp only [ex]; ring

lemma iv_insert {A : Finset V} {a : V} (ha : a ∉ A) (w : V) :
    IndicatorVec (insert a A) w = IndicatorVec {a} w + IndicatorVec A w := by
  simp only [IndicatorVec, Finset.mem_insert, Finset.mem_singleton]
  by_cases h : w = a
  · subst h; simp [ha]
  · simp [h]

lemma iv_erase {A : Finset V} {a : V} (ha : a ∈ A) (w : V) :
    IndicatorVec A w = IndicatorVec {a} w + IndicatorVec (A.erase a) w := by
  conv_lhs => rw [← Finset.insert_erase ha]
  exact iv_insert (Finset.notMem_erase a A) w

lemma exs_empty (x : V → ℤ) : exs x ∅ ∅ = x := by
  funext w; simp [exs, IndicatorVec]

lemma ex_exs_insert (x : V → ℤ) {A W : Finset V} {a b : V} (ha : a ∉ A) (hb : b ∉ W) :
    ex (exs x A W) a b = exs x (insert a A) (insert b W) := by
  funext w; simp only [ex, exs]; rw [iv_insert ha, iv_insert hb]; ring

lemma ex_exs_erase (x : V → ℤ) {A W : Finset V} {v b : V} (hv : v ∈ A) (hb : b ∈ W) :
    ex (exs x A W) b v = exs x (A.erase v) (W.erase b) := by
  funext w; simp only [ex, exs]; rw [iv_erase hv, iv_erase hb]; ring

lemma ex_exs_swap (x : V → ℤ) {A W : Finset V} {a v : V} (hv : v ∈ A) (ha : a ∉ A) :
    ex (exs x A W) a v = exs x (insert a (A.erase v)) W := by
  have ha' : a ∉ A.erase v := fun h => ha (Finset.mem_of_mem_erase h)
  funext w; simp only [ex, exs]; rw [iv_insert ha', iv_erase hv]; ring

lemma lin_add_eq (p : V → ℝ) (x y x' y' : V → ℤ) (h : ∀ w, x' w + y' w = x w + y w) :
    lin p x' + lin p y' = lin p x + lin p y := by
  simp only [lin, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h' : ((x' i : ℝ) + (y' i : ℝ)) = (x i : ℝ) + (y i : ℝ) := by exact_mod_cast h i
  rw [h']

lemma lin_ex (p : V → ℝ) (x : V → ℤ) (a b : V) : lin p (ex x a b) = lin p x - p a + p b := by
  have h : ∀ i, p i * ((ex x a b i : ℤ) : ℝ) =
      p i * (x i : ℝ) - (if i = a then p i else 0) + (if i = b then p i else 0) := by
    intro i
    simp only [ex, IndicatorVec, Finset.mem_singleton]
    split_ifs <;> push_cast <;> ring
  simp only [lin]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

lemma mexc_add_linear {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (p : V → ℝ) :
    MExchangeAxiom (fun y => f y + ((lin p y : ℝ) : WithTop ℝ)) := by
  intro x hx y hy u hu
  have hx2 : f x + ((lin p x : ℝ) : WithTop ℝ) ≠ ⊤ := hx
  have hy2 : f y + ((lin p y : ℝ) : WithTop ℝ) ≠ ⊤ := hy
  have hx' : f x ≠ ⊤ := fun h => hx2 (by rw [h, top_add])
  have hy' : f y ≠ ⊤ := fun h => hy2 (by rw [h, top_add])
  obtain ⟨v, hv, h⟩ := hf x hx' y hy' u hu
  refine ⟨v, hv, ?_⟩
  have hl := lin_add_eq p x y (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w)
    (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w) (fun w => by ring)
  show f (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) +
      ((lin p (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) : ℝ) : WithTop ℝ) +
      (f (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w) +
      ((lin p (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w) : ℝ) : WithTop ℝ)) ≤
      f x + ((lin p x : ℝ) : WithTop ℝ) + (f y + ((lin p y : ℝ) : WithTop ℝ))
  rw [add_add_add_comm, add_add_add_comm (f x), ← WithTop.coe_add, ← WithTop.coe_add, hl]
  exact add_le_add h le_rfl

lemma mexc_indicator {B : Set (V → ℤ)} (hB : ExchangeAxiomB B) : MExchangeAxiom (IndicatorWT B) := by
  intro x hx y hy u hu
  have hx2 : IndicatorWT B x ≠ ⊤ := hx
  have hy2 : IndicatorWT B y ≠ ⊤ := hy
  have hxB : x ∈ B := by
    by_contra h; exact hx2 (by simp [IndicatorWT, h])
  have hyB : y ∈ B := by
    by_contra h; exact hy2 (by simp [IndicatorWT, h])
  obtain ⟨v, hv, h1, h2⟩ := hB x hxB y hyB u hu
  refine ⟨v, hv, ?_⟩
  simp [IndicatorWT, hxB, hyB, h1, h2]

lemma exists_suppPos_of_ne {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) {x y : V → ℤ}
    (hx : f x ≠ ⊤) (hy : f y ≠ ⊤) (hne : y ≠ x) : ∃ u, u ∈ SuppPos y x := by
  by_contra h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hi' : i ∈ SuppPos x y := by
    rw [mem_suppPos]
    by_contra h2
    exact h ⟨i, mem_suppPos.2 (by omega)⟩
  obtain ⟨v, hv, -⟩ := hf x hx y hy i hi'
  rw [mem_suppNeg] at hv
  exact h ⟨v, mem_suppPos.2 hv⟩

lemma dist_ex_lt {y x0 : V → ℤ} {u v : V} (hu : x0 u < y u) (hv : y v < x0 v) :
    dist1 (ex y u v) x0 < dist1 y x0 := by
  have huv : u ≠ v := by rintro rfl; omega
  apply Finset.sum_lt_sum
  · intro w _
    simp only [ex, IndicatorVec, Finset.mem_singleton]
    split_ifs with h1 h2 h2 <;> subst_vars <;> omega
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [ex, IndicatorVec, Finset.mem_singleton, if_neg huv]
    simp only [if_pos]
    omega

/-- Local optimality ⇒ global optimality for an M-convex function (Murota Thm 6.26). -/
theorem local_opt {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) {x0 : V → ℤ}
    (hx0 : f x0 ≠ ⊤) (hloc : ∀ a b : V, f x0 ≤ f (ex x0 a b)) : ∀ y, f x0 ≤ f y := by
  suffices H : ∀ n : ℕ, ∀ y, dist1 y x0 < n → f x0 ≤ f y from
    fun y => H _ y (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro y h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro y hn
    by_cases hyt : f y = ⊤
    · rw [hyt]; exact le_top
    by_cases hyx : y = x0
    · rw [hyx]
    obtain ⟨u, hu⟩ := exists_suppPos_of_ne hf hx0 hyt hyx
    obtain ⟨v, hv, h⟩ := mexc' hf hyt hx0 hu
    have h1 := hloc v u
    rw [mem_suppPos] at hu
    rw [mem_suppNeg] at hv
    have hd := dist_ex_lt hu hv
    have h2 := ih (ex y u v) (by omega)
    have h3 : f x0 + f x0 ≤ f y + f x0 := (add_le_add h2 h1).trans h
    exact (WithTop.add_le_add_iff_right hx0).1 h3

/-- Triangle inequality of exchange weights (two consecutive exchange arcs a → b → d). -/
theorem triangle {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (x : V → ℤ) {a b d : V}
    (hab : a ≠ b) (hbd : b ≠ d) :
    f x + f (ex x a d) ≤ f (ex x a b) + f (ex x b d) := by
  by_cases h1 : f (ex x a b) = ⊤
  · rw [h1, top_add]; exact le_top
  by_cases h2 : f (ex x b d) = ⊤
  · rw [h2, add_top]; exact le_top
  have hu : b ∈ SuppPos (ex x a b) (ex x b d) := by
    rw [mem_suppPos]
    simp only [ex, IndicatorVec, Finset.mem_singleton, if_neg hab.symm, if_neg hbd]
    simp only [if_pos]
    omega
  obtain ⟨v, hv, h⟩ := mexc' hf h1 h2 hu
  rw [mem_suppNeg] at hv
  have hv' : v = a ∨ v = d := by
    by_contra hc
    simp only [not_or] at hc
    simp only [ex, IndicatorVec, Finset.mem_singleton, if_neg hc.1, if_neg hc.2] at hv
    split_ifs at hv <;> omega
  rcases hv' with rfl | rfl
  · rw [ex_ex_cancel, ex_self, ex_ex_swap] at h
    exact h
  · rw [ex_ex_cancel, ex_ex_cancel, ex_self] at h
    rwa [add_comm (f x)]

/-- Lower bound: all exchange weights over `A × W` at least `α` ⇒ the joint exchange costs at
least `|A| α`. -/
theorem lb {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) {x : V → ℤ} {fx : ℝ}
    (hx : f x = (fx : WithTop ℝ)) (α : ℝ) :
    ∀ n : ℕ, ∀ A W : Finset V, A.card = n → W.card = n → Disjoint A W →
      (∀ a ∈ A, ∀ b ∈ W, ((fx + α : ℝ) : WithTop ℝ) ≤ f (ex x a b)) →
      ((fx + n * α : ℝ) : WithTop ℝ) ≤ f (exs x A W) := by
  intro n
  induction n with
  | zero =>
    intro A W hA hW _ _
    rw [Finset.card_eq_zero.1 hA, Finset.card_eq_zero.1 hW, exs_empty, hx]
    simp
  | succ n ih =>
    intro A W hA hW hd hω
    by_cases hz : f (exs x A W) = ⊤
    · rw [hz]; exact le_top
    obtain ⟨b, hb⟩ : W.Nonempty := Finset.card_pos.1 (by omega)
    have hbA : b ∉ A := Finset.disjoint_right.1 hd hb
    have hu : b ∈ SuppPos (exs x A W) x := by
      rw [mem_suppPos]; simp [exs, IndicatorVec, hb, hbA]
    obtain ⟨v, hv, h⟩ := mexc' hf hz (by rw [hx]; exact WithTop.coe_ne_top) hu
    rw [mem_suppNeg] at hv
    have hvA : v ∈ A := by
      by_contra hc
      simp only [exs, IndicatorVec, if_neg hc] at hv
      split_ifs at hv <;> omega
    rw [ex_exs_erase x hvA hb] at h
    have hA' : (A.erase v).card = n := by rw [Finset.card_erase_of_mem hvA]; omega
    have hW' : (W.erase b).card = n := by rw [Finset.card_erase_of_mem hb]; omega
    have hd' : Disjoint (A.erase v) (W.erase b) :=
      Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd)
    have hω' : ∀ a ∈ A.erase v, ∀ b' ∈ W.erase b,
        ((fx + α : ℝ) : WithTop ℝ) ≤ f (ex x a b') :=
      fun a ha b' hb' => hω a (Finset.mem_of_mem_erase ha) b' (Finset.mem_of_mem_erase hb')
    have h3 := (add_le_add (ih _ _ hA' hW' hd' hω') (hω v hvA b hb)).trans h
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hz
    rw [← ht, hx, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h3
    rw [← ht, WithTop.coe_le_coe]
    push_cast
    linarith


lemma wt_two {T1 T2 : WithTop ℝ} {r : ℝ} (h : T1 + T2 ≤ (r : WithTop ℝ)) :
    ∃ s1 s2 : ℝ, T1 = s1 ∧ T2 = s2 ∧ s1 + s2 ≤ r := by
  induction T1 using WithTop.recTopCoe with
  | top => simp at h
  | coe s1 =>
    induction T2 using WithTop.recTopCoe with
    | top => simp at h
    | coe s2 => exact ⟨s1, s2, rfl, rfl, by exact_mod_cast h⟩

/-- Unique-min lemma (strict-diagonal form; Murota DCA Lemma 6.? / Murota 1996): if every
diagonal exchange `(u_i, v_i)` costs `α` and every off-diagonal one `(u_i, v_j)` costs more,
the joint exchange costs at most `k α`. -/
theorem um {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) {x : V → ℤ} {fx : ℝ}
    (hx : f x = (fx : WithTop ℝ)) (α : ℝ) :
    ∀ L : List (V × V), (L.map Prod.fst).Nodup → (L.map Prod.snd).Nodup →
      (∀ q ∈ L, ∀ q' ∈ L, q.1 ≠ q'.2) →
      (∀ q ∈ L, f (ex x q.1 q.2) = ((fx + α : ℝ) : WithTop ℝ)) →
      (∀ q ∈ L, ∀ q' ∈ L, q ≠ q' → ((fx + α : ℝ) : WithTop ℝ) < f (ex x q.1 q'.2)) →
      f (exs x (L.map Prod.fst).toFinset (L.map Prod.snd).toFinset) ≤
        ((fx + L.length * α : ℝ) : WithTop ℝ) := by
  intro L
  induction L with
  | nil =>
    intro _ _ _ _ _
    simp only [List.map_nil, List.toFinset_nil, exs_empty, hx, List.length_nil]
    simp
  | cons q L ih =>
    obtain ⟨a, b⟩ := q
    intro hn1 hn2 hd hdiag hoff
    have ih' := ih (List.nodup_cons.1 hn1).2 (List.nodup_cons.1 hn2).2
      (fun q hq q' hq' => hd q (List.mem_cons_of_mem _ hq) q' (List.mem_cons_of_mem _ hq'))
      (fun q hq => hdiag q (List.mem_cons_of_mem _ hq))
      (fun q hq q' hq' hne => hoff q (List.mem_cons_of_mem _ hq) q' (List.mem_cons_of_mem _ hq') hne)
    have key : ∀ q1 ∈ (a, b) :: L, ∀ q2 ∈ (a, b) :: L,
        ((fx + α : ℝ) : WithTop ℝ) ≤ f (ex x q1.1 q2.2) := by
      intro q1 h1 q2 h2
      by_cases h : q1 = q2
      · subst h; exact (hdiag q1 h1).ge
      · exact (hoff q1 h1 q2 h2 h).le
    have hn1' := List.nodup_cons.1 hn1
    have hn2' := List.nodup_cons.1 hn2
    simp only [List.map_cons, List.toFinset_cons, List.length_cons]
    set A' := (L.map Prod.fst).toFinset with hA'
    set W' := (L.map Prod.snd).toFinset with hW'
    have memA : ∀ w, w ∈ A' ↔ ∃ q ∈ L, q.1 = w := by
      intro w; rw [hA', List.mem_toFinset, List.mem_map]
    have memW : ∀ w, w ∈ W' ↔ ∃ q ∈ L, q.2 = w := by
      intro w; rw [hW', List.mem_toFinset, List.mem_map]
    have haA : a ∉ A' := by
      rw [hA', List.mem_toFinset]; exact hn1'.1
    have hbW : b ∉ W' := by
      rw [hW', List.mem_toFinset]; exact hn2'.1
    have haW : a ∉ W' := by
      rw [memW]; rintro ⟨q, hq, hqa⟩
      exact hd (a, b) List.mem_cons_self q (List.mem_cons_of_mem _ hq) hqa.symm
    have hab : a ≠ b := hd (a, b) List.mem_cons_self (a, b) List.mem_cons_self
    have hdisj : ∀ w ∈ A', w ∉ W' := by
      intro w hw hw'
      obtain ⟨q, hq, rfl⟩ := (memA w).1 hw
      obtain ⟨q', hq', hq'e⟩ := (memW q.1).1 hw'
      exact hd q (List.mem_cons_of_mem _ hq) q' (List.mem_cons_of_mem _ hq') hq'e.symm
    have cardA : A'.card = L.length := by
      rw [hA', List.toFinset_card_of_nodup hn1'.2, List.length_map]
    have cardW : W'.card = L.length := by
      rw [hW', List.toFinset_card_of_nodup hn2'.2, List.length_map]
    have hy'top : f (exs x A' W') ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top ih'
    have hxk : f (ex x a b) = ((fx + α : ℝ) : WithTop ℝ) := hdiag (a, b) List.mem_cons_self
    have hxktop : f (ex x a b) ≠ ⊤ := by rw [hxk]; exact WithTop.coe_ne_top
    have hu : a ∈ SuppPos (exs x A' W') (ex x a b) := by
      rw [mem_suppPos]
      simp only [exs, ex, IndicatorVec, Finset.mem_singleton, if_neg haA, if_neg haW, if_neg hab]
      simp
    obtain ⟨v, hv, h⟩ := mexc' hf hy'top hxktop hu
    rw [mem_suppNeg] at hv
    have hv' : v = b ∨ v ∈ A' := by
      by_contra hc
      simp only [not_or] at hc
      simp only [exs, ex, IndicatorVec, Finset.mem_singleton, if_neg hc.2, if_neg hc.1] at hv
      split_ifs at hv <;> omega
    rcases hv' with hvb | hvA
    · rw [hvb, ex_exs_insert x haA hbW, ex_ex_cancel, ex_self, hx] at h
      have h2 := h.trans (add_le_add ih' hxk.le)
      rw [← WithTop.coe_add] at h2
      obtain ⟨s1, s2, hs1, hs2, hle⟩ := wt_two h2
      have : s2 = fx := (WithTop.coe_injective hs2).symm
      rw [hs1, WithTop.coe_le_coe]
      push_cast
      linarith
    · exfalso
      obtain ⟨q, hq, hqv⟩ := (memA v).1 hvA
      have hva : v ≠ a := fun h => haA (h ▸ hvA)
      rw [ex_exs_swap x hvA haA, ex_ex_swap] at h
      have hlt : ((fx + α : ℝ) : WithTop ℝ) < f (ex x v b) := by
        have := hoff q (List.mem_cons_of_mem _ hq) (a, b) List.mem_cons_self
          (fun h => hva (by rw [← hqv, h]))
        dsimp only at this
        rwa [hqv] at this
      have hLpos : 0 < L.length := by rw [← cardA]; exact Finset.card_pos.2 ⟨v, hvA⟩
      have haE : a ∉ A'.erase v := fun h => haA (Finset.mem_of_mem_erase h)
      have hcard : (insert a (A'.erase v)).card = L.length := by
        rw [Finset.card_insert_of_notMem haE, Finset.card_erase_of_mem hvA, cardA]; omega
      have hdj : Disjoint (insert a (A'.erase v)) W' := by
        rw [Finset.disjoint_left]
        intro w hw
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact haW
        · exact hdisj w (Finset.mem_of_mem_erase hw)
      have hω : ∀ a'' ∈ insert a (A'.erase v), ∀ b'' ∈ W',
          ((fx + α : ℝ) : WithTop ℝ) ≤ f (ex x a'' b'') := by
        intro a'' ha'' b'' hb''
        obtain ⟨q2, hq2, rfl⟩ := (memW b'').1 hb''
        rcases Finset.mem_insert.1 ha'' with rfl | ha''
        · exact key (a'', b) List.mem_cons_self q2 (List.mem_cons_of_mem _ hq2)
        · obtain ⟨q1, hq1, rfl⟩ := (memA a'').1 (Finset.mem_of_mem_erase ha'')
          exact key q1 (List.mem_cons_of_mem _ hq1) q2 (List.mem_cons_of_mem _ hq2)
      have hLB := lb hf hx α L.length _ _ hcard cardW hdj hω
      have h2 := h.trans (add_le_add ih' hxk.le)
      rw [← WithTop.coe_add] at h2
      obtain ⟨s1, s2, hs1, hs2, hle⟩ := wt_two h2
      rw [hs1, WithTop.coe_le_coe] at hLB
      rw [hs2, WithTop.coe_lt_coe] at hlt
      linarith

end K


/-! ## G: walks, cycle splitting, potentials (functional walks `g : ℕ → V` of length `m`) -/

section G

variable {V : Type u} [Fintype V] [DecidableEq V]

def wsum (l : V → V → ℝ) (g : ℕ → V) (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, l (g i) (g (i + 1))

def walkOK (adj : V → V → Prop) (g : ℕ → V) (m : ℕ) : Prop := ∀ i < m, adj (g i) (g (i + 1))

/-- the walk with the closed segment `[i, i+d]` cut out -/
def outerW (g : ℕ → V) (i d : ℕ) : ℕ → V := fun k => if k ≤ i then g k else g (k + d)

lemma split_sum (l : V → V → ℝ) (g : ℕ → V) (i d r : ℕ) (hij : g i = g (i + d)) :
    wsum l g (i + d + r) = wsum l (fun k => g (i + k)) d + wsum l (outerW g i d) (i + r) := by
  unfold wsum
  rw [add_assoc]
  simp only [Finset.sum_range_add]
  have h1 : ∑ k ∈ Finset.range i, l (outerW g i d k) (outerW g i d (k + 1)) =
      ∑ k ∈ Finset.range i, l (g k) (g (k + 1)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    simp only [outerW, if_pos hk.le, if_pos (show k + 1 ≤ i by omega)]
  have h2 : ∑ k ∈ Finset.range r, l (outerW g i d (i + k)) (outerW g i d (i + k + 1)) =
      ∑ k ∈ Finset.range r, l (g (i + (d + k))) (g (i + (d + k) + 1)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : outerW g i d (i + k) = g (i + (d + k)) := by
      unfold outerW
      split_ifs with h
      · have : k = 0 := by omega
        subst this; simpa using hij
      · congr 1; omega
    have e2 : outerW g i d (i + k + 1) = g (i + (d + k) + 1) := by
      unfold outerW; rw [if_neg (by omega)]; congr 1; omega
    rw [e1, e2]
  have h3 : ∑ k ∈ Finset.range d, l (g (i + k)) (g (i + (k + 1))) =
      ∑ k ∈ Finset.range d, l (g (i + k)) (g (i + k + 1)) :=
    Finset.sum_congr rfl fun k _ => by rw [add_assoc]
  rw [h1, h2, h3]
  ring

lemma split_ok (adj : V → V → Prop) (g : ℕ → V) (i d r : ℕ) (hij : g i = g (i + d))
    (h : walkOK adj g (i + d + r)) :
    walkOK adj (fun k => g (i + k)) d ∧ walkOK adj (outerW g i d) (i + r) := by
  constructor
  · intro k hk
    have := h (i + k) (by omega)
    simpa [add_assoc] using this
  · intro k hk
    by_cases hki : k < i
    · simp only [outerW, if_pos hki.le, if_pos (show k + 1 ≤ i by omega)]
      exact h k (by omega)
    · have e1 : outerW g i d k = g (k + d) := by
        unfold outerW
        split_ifs with h'
        · have : k = i := by omega
          subst this; exact hij
        · rfl
      have e2 : outerW g i d (k + 1) = g (k + d + 1) := by
        unfold outerW; rw [if_neg (by omega)]; congr 1; omega
      rw [e1, e2]
      exact h (k + d) (by omega)

lemma outerW_zero (g : ℕ → V) (i d : ℕ) : outerW g i d 0 = g 0 := by
  simp [outerW]

lemma outerW_end (g : ℕ → V) (i d r : ℕ) (hij : g i = g (i + d)) :
    outerW g i d (i + r) = g (i + d + r) := by
  unfold outerW
  split_ifs with h
  · have : r = 0 := by omega
    subst this; simpa using hij
  · congr 1; omega

lemma pigeon (g : ℕ → V) (n : ℕ) (hn : Fintype.card V < n) :
    ∃ i d, 0 < d ∧ i + d < n ∧ g i = g (i + d) := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin n => g k.val) (by simpa using hn)
  simp only at heq
  have hne' : i ≠ j := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne' with h | h
  · exact ⟨i, j - i, by omega, by omega, by rw [Nat.add_sub_of_le h.le]; exact heq⟩
  · exact ⟨j, i - j, by omega, by omega, by rw [Nat.add_sub_of_le h.le]; exact heq.symm⟩

/-- closed walks of length ≤ |V| control all closed walks -/
theorem closed_nonneg_of_short (adj : V → V → Prop) (l : V → V → ℝ)
    (hshort : ∀ m g, walkOK adj g m → g m = g 0 → m ≤ Fintype.card V → 0 ≤ wsum l g m) :
    ∀ m g, walkOK adj g m → g m = g 0 → 0 ≤ wsum l g m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro g hw hc
  by_cases hm : m ≤ Fintype.card V
  · exact hshort m g hw hc hm
  obtain ⟨i, d, hd, hid, hg⟩ := pigeon g m (by omega)
  obtain ⟨r, hr⟩ : ∃ r, m = i + d + r := ⟨m - (i + d), by omega⟩
  subst hr
  have hs := split_sum l g i d r hg
  obtain ⟨hw1, hw2⟩ := split_ok adj g i d r hg hw
  have c1 : (fun k => g (i + k)) d = (fun k => g (i + k)) 0 := by
    show g (i + d) = g (i + 0); rw [add_zero, hg]
  have c2 : outerW g i d (i + r) = outerW g i d 0 := by
    rw [outerW_end g i d r hg, outerW_zero, hc]
  have n1 := ih d (by omega) _ hw1 c1
  have n2 := ih (i + r) (by omega) _ hw2 c2
  rw [hs]; linarith

/-- No negative closed walk ⇒ a feasible potential (shortest-walk argument). -/
theorem potential (adj : V → V → Prop) (l : V → V → ℝ)
    (hcyc : ∀ m g, walkOK adj g m → g m = g 0 → 0 ≤ wsum l g m) :
    ∃ p : V → ℝ, ∀ a b, adj a b → p a - p b ≤ l a b := by
  set M : ℝ := ∑ a, ∑ b, |l a b| with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM : ∀ a b, -M ≤ l a b := by
    intro a b
    have h1 : |l a b| ≤ ∑ b', |l a b'| :=
      Finset.single_le_sum (f := fun b' => |l a b'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
    have h2 : ∑ b', |l a b'| ≤ M :=
      Finset.single_le_sum (f := fun a' => ∑ b', |l a' b'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    have := neg_abs_le (l a b)
    linarith
  have H : ∀ m g, walkOK adj g m → -wsum l g m ≤ Fintype.card V * M := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro g hw
    by_cases hm : m ≤ Fintype.card V
    · have h1 : ∑ i ∈ Finset.range m, (-M) ≤ ∑ i ∈ Finset.range m, l (g i) (g (i + 1)) :=
        Finset.sum_le_sum fun i _ => hM _ _
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
      have h2 : (m : ℝ) * M ≤ Fintype.card V * M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hM0
      unfold wsum
      linarith
    obtain ⟨i, d, hd, hid, hg⟩ := pigeon g (m + 1) (by omega)
    obtain ⟨r, hr⟩ : ∃ r, m = i + d + r := ⟨m - (i + d), by omega⟩
    subst hr
    have hs := split_sum l g i d r hg
    obtain ⟨hw1, hw2⟩ := split_ok adj g i d r hg hw
    have c1 : (fun k => g (i + k)) d = (fun k => g (i + k)) 0 := by
      show g (i + d) = g (i + 0); rw [add_zero, hg]
    have n1 := hcyc d _ hw1 c1
    have n2 := ih (i + r) (by omega) _ hw2
    rw [hs]; linarith
  set S : V → Set ℝ := fun v => {s | ∃ m g, walkOK adj g m ∧ g m = v ∧ s = -wsum l g m}
    with hSdef
  have hne : ∀ v, (S v).Nonempty := fun v =>
    ⟨0, 0, fun _ => v, fun i hi => absurd hi (Nat.not_lt_zero _), rfl, by simp [wsum]⟩
  have hbdd : ∀ v, BddAbove (S v) := by
    intro v
    refine ⟨Fintype.card V * M, ?_⟩
    rintro s ⟨m, g, hw, -, rfl⟩
    exact H m g hw
  refine ⟨fun v => sSup (S v), ?_⟩
  intro a b hab
  have key : sSup (S a) ≤ sSup (S b) + l a b := by
    apply csSup_le (hne a)
    rintro s ⟨m, g, hw, hga, rfl⟩
    have hmem : -wsum l g m - l a b ∈ S b := by
      refine ⟨m + 1, fun k => if k ≤ m then g k else b, ?_, by simp, ?_⟩
      · intro i hi
        by_cases him : i < m
        · simp only [if_pos him.le, if_pos (show i + 1 ≤ m by omega)]
          exact hw i him
        · have : i = m := by omega
          subst this
          simp only [le_refl, if_true, if_neg (show ¬ (i + 1 ≤ i) by omega)]
          rw [hga]; exact hab
      · unfold wsum
        rw [Finset.sum_range_succ]
        simp only [le_refl, if_true, if_neg (show ¬ (m + 1 ≤ m) by omega), hga]
        have : ∑ x ∈ Finset.range m, l (if x ≤ m then g x else b) (if x + 1 ≤ m then g (x + 1) else b)
            = ∑ x ∈ Finset.range m, l (g x) (g (x + 1)) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [Finset.mem_range] at hx
          rw [if_pos hx.le, if_pos (show x + 1 ≤ m by omega)]
        rw [this]; ring
    have := le_csSup (hbdd b) hmem
    linarith
  show sSup (S a) - sSup (S b) ≤ l a b
  linarith

end G


/-! ## T: tight walks and minimal closed walks of a relation -/

section T

variable {V : Type u} [Fintype V] [DecidableEq V]

lemma all_tight (adj : V → V → Prop) (l : V → V → ℝ) (p : V → ℝ)
    (hp : ∀ a b, adj a b → p a - p b ≤ l a b) (g : ℕ → V) (m : ℕ) (hw : walkOK adj g m)
    (hc : g m = g 0) (h0 : wsum l g m ≤ 0) :
    walkOK (fun a b => adj a b ∧ p a - p b = l a b) g m := by
  have hnn : ∀ i ∈ Finset.range m, 0 ≤ l (g i) (g (i + 1)) - (p (g i) - p (g (i + 1))) := by
    intro i hi
    have := hp _ _ (hw i (Finset.mem_range.1 hi))
    linarith
  have hsum : ∑ i ∈ Finset.range m, (l (g i) (g (i + 1)) - (p (g i) - p (g (i + 1)))) =
      wsum l g m := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub' (fun i => p (g i)), hc, sub_self, sub_zero]
    rfl
  have hz : ∑ i ∈ Finset.range m, (l (g i) (g (i + 1)) - (p (g i) - p (g (i + 1)))) = 0 :=
    le_antisymm (hsum ▸ h0) (Finset.sum_nonneg hnn)
  intro i hi
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hz i (Finset.mem_range.2 hi)
  exact ⟨hw i hi, by linarith⟩

variable (T : V → V → Prop)

/-- a closed `T`-walk of minimal positive length -/
def MinW (g : ℕ → V) (m : ℕ) : Prop :=
  0 < m ∧ walkOK T g m ∧ g m = g 0 ∧
    ∀ m' (g' : ℕ → V), 0 < m' → walkOK T g' m' → g' m' = g' 0 → m ≤ m'

lemma minw_inj {g : ℕ → V} {m : ℕ} (h : MinW T g m) {i j : ℕ} (hij : i < j) (hjm : j < m) :
    g i ≠ g j := by
  intro he
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  have hw := h.2.1
  have h1 : walkOK T (fun k => g (i + k)) d := by
    intro k hk
    have := hw (i + k) (by omega)
    simpa [add_assoc] using this
  have h2 : (fun k => g (i + k)) d = (fun k => g (i + k)) 0 := by
    show g (i + d) = g (i + 0); rw [add_zero, he]
  have := h.2.2.2 d _ (by omega) h1 h2
  omega

lemma mod_succ_eq {m k : ℕ} (hm : 0 < m) :
    (k + 1) % m = if k % m + 1 < m then k % m + 1 else 0 := by
  rw [Nat.add_mod]
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · have : k % m + 1 = m := by have := Nat.mod_lt k hm; omega
      rw [this, Nat.mod_self]
  · have : m = 1 := by omega
    subst this
    simp [Nat.mod_one]

lemma minw_period {g : ℕ → V} {m : ℕ} (h : MinW T g m) (k : ℕ) :
    T (g (k % m)) (g ((k + 1) % m)) := by
  have hm := h.1
  have := h.2.1 (k % m) (Nat.mod_lt k hm)
  rw [mod_succ_eq hm]
  split_ifs with h'
  · exact this
  · have e : k % m + 1 = m := by have := Nat.mod_lt k hm; omega
    rw [e, h.2.2.1] at this
    exact this

lemma minw_chord {g : ℕ → V} {m : ℕ} (h : MinW T g m) {s t : ℕ} (hs : s < m) (ht : t < m)
    (hT : T (g s) (g t)) : t = s + 1 ∨ (s + 1 = m ∧ t = 0) := by
  have hm := h.1
  obtain ⟨d, hdm, htd, hfin⟩ : ∃ d, d < m ∧ (t + d) % m = s ∧
      (m ≤ d + 1 → t = s + 1 ∨ (s + 1 = m ∧ t = 0)) := by
    by_cases hts : t ≤ s
    · refine ⟨s - t, by omega, ?_, fun h' => Or.inr ⟨by omega, by omega⟩⟩
      rw [Nat.add_sub_of_le hts, Nat.mod_eq_of_lt hs]
    · refine ⟨s + m - t, by omega, ?_, fun h' => Or.inl (by omega)⟩
      have e : t + (s + m - t) = s + m := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hs]
  apply hfin
  let δ : ℕ → V := fun k => if k ≤ d then g ((t + k) % m) else g t
  have hδ : walkOK T δ (d + 1) := by
    intro k hk
    by_cases hkd : k < d
    · have e1 : δ k = g ((t + k) % m) := if_pos hkd.le
      have e2 : δ (k + 1) = g ((t + k + 1) % m) := if_pos (show k + 1 ≤ d by omega)
      rw [e1, e2]
      exact minw_period T h (t + k)
    · have hk' : k = d := by omega
      have e1 : δ k = g s := by
        show (if k ≤ d then g ((t + k) % m) else g t) = g s
        rw [if_pos (by omega), hk', htd]
      have e2 : δ (k + 1) = g t := if_neg (by omega)
      rw [e1, e2]
      exact hT
  have hδc : δ (d + 1) = δ 0 := by
    have e1 : δ (d + 1) = g t := if_neg (by omega)
    have e2 : δ 0 = g ((t + 0) % m) := if_pos (Nat.zero_le _)
    rw [e1, e2, add_zero, Nat.mod_eq_of_lt ht]
  exact h.2.2.2 (d + 1) δ (by omega) hδ hδc

/-- rotating a minimal closed walk by one step gives a minimal closed walk -/
lemma minw_rot {g : ℕ → V} {m : ℕ} (h : MinW T g m) : MinW T (fun k => g ((k + 1) % m)) m := by
  have hm := h.1
  refine ⟨hm, ?_, ?_, fun m' g' h1 h2 h3 => h.2.2.2 m' g' h1 h2 h3⟩
  · intro k _
    have := minw_period T h (k + 1)
    exact this
  · show g ((m + 1) % m) = g ((0 + 1) % m)
    rw [Nat.add_mod_left, zero_add]

end T


/-! ## M: the exchange graph of `(c, B)` at `x` -/

section M

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- arc level: `c(x - χa + χb)` for a c-arc, `c(x)` for a B-arc `a → b` (`x - χb + χa ∈ B`) -/
noncomputable def lw (c : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x : V → ℤ) (a0 : ℝ) (a b : V) :
    WithTop ℝ :=
  min (c (ex x a b)) (IndicatorWT B (ex x b a) + ((a0 : ℝ) : WithTop ℝ))

noncomputable def lr (c : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x : V → ℤ) (a0 : ℝ) (a b : V) :
    ℝ := (lw c B x a0 a b).untopD 0 - a0

def adjM (c : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x : V → ℤ) (a0 : ℝ) (a b : V) : Prop :=
  lw c B x a0 a b ≠ ⊤

variable {c : (V → ℤ) → WithTop ℝ} {B : Set (V → ℤ)} {x : V → ℤ} {a0 : ℝ}

lemma lw_eq {a b : V} (h : adjM c B x a0 a b) :
    lw c B x a0 a b = ((lr c B x a0 a b + a0 : ℝ) : WithTop ℝ) := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h
  simp [lr, ← ht]

lemma arc_c {a b : V} {β : ℝ} (h : c (ex x a b) = (β : WithTop ℝ)) :
    adjM c B x a0 a b ∧ lr c B x a0 a b ≤ β - a0 := by
  have hle : lw c B x a0 a b ≤ (β : WithTop ℝ) := h ▸ min_le_left _ _
  have hadj : adjM c B x a0 a b := ne_top_of_le_ne_top WithTop.coe_ne_top hle
  refine ⟨hadj, ?_⟩
  rw [lw_eq hadj, WithTop.coe_le_coe] at hle
  linarith

lemma arc_b {a b : V} (h : ex x b a ∈ B) :
    adjM c B x a0 a b ∧ lr c B x a0 a b ≤ 0 := by
  have hle : lw c B x a0 a b ≤ ((a0 : ℝ) : WithTop ℝ) := by
    have : IndicatorWT B (ex x b a) + ((a0 : ℝ) : WithTop ℝ) = ((a0 : ℝ) : WithTop ℝ) := by
      simp [IndicatorWT, h]
    exact this ▸ min_le_right _ _
  have hadj : adjM c B x a0 a b := ne_top_of_le_ne_top WithTop.coe_ne_top hle
  refine ⟨hadj, ?_⟩
  rw [lw_eq hadj, WithTop.coe_le_coe] at hle
  linarith

lemma arc_cases {a b : V} (h : adjM c B x a0 a b) :
    c (ex x a b) = ((lr c B x a0 a b + a0 : ℝ) : WithTop ℝ) ∨
      (ex x b a ∈ B ∧ lr c B x a0 a b = 0) := by
  have he := lw_eq h
  rcases min_choice (c (ex x a b)) (IndicatorWT B (ex x b a) + ((a0 : ℝ) : WithTop ℝ)) with h1 | h1
  · left; rw [← h1]; exact he
  · right
    unfold lw at he
    rw [h1] at he
    by_cases hB : ex x b a ∈ B
    · refine ⟨hB, ?_⟩
      simp only [IndicatorWT, if_pos hB, zero_add, WithTop.coe_eq_coe] at he
      linarith
    · simp only [IndicatorWT, if_neg hB, top_add] at he
      exact absurd he WithTop.top_ne_coe

lemma lr_self (hx : c x = ((a0 : ℝ) : WithTop ℝ)) (hxB : x ∈ B) (a : V) : lr c B x a0 a a = 0 := by
  have : lw c B x a0 a a = ((a0 : ℝ) : WithTop ℝ) := by
    simp [lw, ex_self, hx, IndicatorWT, hxB]
  simp [lr, this]

lemma no_two_c (hc : MExchangeAxiom c) (hx : c x = ((a0 : ℝ) : WithTop ℝ)) (p : V → ℝ) (μ : ℝ)
    (hμ : μ < 0) (hp : ∀ a b, adjM c B x a0 a b → p a - p b ≤ lr c B x a0 a b - μ)
    {a b d : V} (hab : a ≠ b) (hbd : b ≠ d)
    (t1 : p a - p b = lr c B x a0 a b - μ) (t2 : p b - p d = lr c B x a0 b d - μ)
    (c1 : c (ex x a b) = ((lr c B x a0 a b + a0 : ℝ) : WithTop ℝ))
    (c2 : c (ex x b d) = ((lr c B x a0 b d + a0 : ℝ) : WithTop ℝ)) : False := by
  have htri := triangle hc x hab hbd
  rw [c1, c2, hx, ← WithTop.coe_add] at htri
  obtain ⟨s1, s2, hs1, hs2, hle⟩ := wt_two htri
  have e1 : a0 = s1 := WithTop.coe_injective hs1
  obtain ⟨hadj, hlr⟩ := arc_c (B := B) (a0 := a0) hs2
  have := hp a d hadj
  linarith

lemma no_two_b (hB : ExchangeAxiomB B) (hxB : x ∈ B) (p : V → ℝ) (μ : ℝ)
    (hμ : μ < 0) (hp : ∀ a b, adjM c B x a0 a b → p a - p b ≤ lr c B x a0 a b - μ)
    {a b d : V} (hab : a ≠ b) (hbd : b ≠ d)
    (t1 : p a - p b = lr c B x a0 a b - μ) (t2 : p b - p d = lr c B x a0 b d - μ)
    (b1 : ex x b a ∈ B) (l1 : lr c B x a0 a b = 0)
    (b2 : ex x d b ∈ B) (l2 : lr c B x a0 b d = 0) : False := by
  have htri := triangle (mexc_indicator hB) x (a := d) (b := b) (d := a) hbd.symm hab.symm
  have hin : ex x d a ∈ B := by
    by_contra hn
    simp [IndicatorWT, hxB, hn, b1, b2] at htri
  obtain ⟨hadj, hlr⟩ := arc_b (c := c) (a0 := a0) hin
  have := hp a d hadj
  linarith

lemma lin_exs (p : V → ℝ) (x : V → ℤ) (A W : Finset V) :
    lin p (exs x A W) = lin p x - ∑ a ∈ A, p a + ∑ b ∈ W, p b := by
  have h : ∀ i, p i * ((exs x A W i : ℤ) : ℝ) =
      p i * (x i : ℝ) - (if i ∈ A then p i else 0) + (if i ∈ W then p i else 0) := by
    intro i
    simp only [exs, IndicatorVec]
    split_ifs <;> push_cast <;> ring
  simp only [lin]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter]

end M


/-! ## M3: an alternating minimal tight cycle contradicts optimality of `x` -/

section M3

variable {V : Type u} [Fintype V] [DecidableEq V]

lemma list_range_sum (f : ℕ → ℝ) (K : ℕ) :
    ((List.range K).map f).sum = ∑ i ∈ Finset.range K, f i := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem contra_alt {c : (V → ℤ) → WithTop ℝ} {B : Set (V → ℤ)} {x : V → ℤ} {a0 : ℝ}
    (hc : MExchangeAxiom c) (hB : ExchangeAxiomB B) (hxB : x ∈ B)
    (hx : c x = ((a0 : ℝ) : WithTop ℝ)) (hmin : ∀ z ∈ B, c x ≤ c z)
    (p : V → ℝ) (μ : ℝ) (hμ : μ < 0)
    (hp : ∀ a b, adjM c B x a0 a b → p a - p b ≤ lr c B x a0 a b - μ)
    (g : ℕ → V) (K : ℕ) (hK : 0 < K)
    (hMin : MinW (fun a b => adjM c B x a0 a b ∧ p a - p b = lr c B x a0 a b - μ) g (2 * K))
    (hlab : ∀ i < K, c (ex x (g (2 * i)) (g (2 * i + 1))) =
        ((lr c B x a0 (g (2 * i)) (g (2 * i + 1)) + a0 : ℝ) : WithTop ℝ) ∧
      ¬ c (ex x (g (2 * i + 1)) (g (2 * i + 2))) =
        ((lr c B x a0 (g (2 * i + 1)) (g (2 * i + 2)) + a0 : ℝ) : WithTop ℝ)) : False := by
  set Tt : V → V → Prop := fun a b => adjM c B x a0 a b ∧ p a - p b = lr c B x a0 a b - μ
    with hTt
  have hw := hMin.2.1
  have hcl : g (2 * K) = g 0 := hMin.2.2.1
  have inj : ∀ i j, i < 2 * K → j < 2 * K → g i = g j → i = j := by
    intro i j hi hj he
    rcases lt_trichotomy i j with h | h | h
    · exact absurd he (minw_inj Tt hMin h hj)
    · exact h
    · exact absurd he.symm (minw_inj Tt hMin h hi)
  have hcT : ∀ i < K, p (g (2 * i)) - p (g (2 * i + 1)) =
      lr c B x a0 (g (2 * i)) (g (2 * i + 1)) - μ := fun i hi => (hw (2 * i) (by omega)).2
  have hbT : ∀ i < K, ex x (g (2 * i + 2)) (g (2 * i + 1)) ∈ B ∧
      p (g (2 * i + 1)) - p (g (2 * i + 2)) = -μ := by
    intro i hi
    have h1 : Tt (g (2 * i + 1)) (g (2 * i + 2)) := hw (2 * i + 1) (by omega)
    rcases arc_cases h1.1 with h2 | ⟨h2, h3⟩
    · exact absurd h2 (hlab i hi).2
    · refine ⟨h2, ?_⟩
      have := h1.2
      rw [h3] at this
      linarith
  have pos' : ∀ i < K, ∃ t < 2 * K, g (2 * i + 2) = g t ∧
      (t = 2 * i + 2 ∨ (i + 1 = K ∧ t = 0)) := by
    intro i hi
    by_cases h : i + 1 < K
    · exact ⟨2 * i + 2, by omega, rfl, Or.inl rfl⟩
    · refine ⟨0, by omega, ?_, Or.inr ⟨by omega, rfl⟩⟩
      have : 2 * i + 2 = 2 * K := by omega
      rw [this, hcl]
  -- the c side
  have hf1 : MExchangeAxiom (fun y => c y + ((lin p y : ℝ) : WithTop ℝ)) := mexc_add_linear hc p
  have hx1 : c x + ((lin p x : ℝ) : WithTop ℝ) = ((a0 + lin p x : ℝ) : WithTop ℝ) := by
    rw [hx, ← WithTop.coe_add]
  have diag1 : ∀ i < K, c (ex x (g (2 * i)) (g (2 * i + 1))) +
      ((lin p (ex x (g (2 * i)) (g (2 * i + 1))) : ℝ) : WithTop ℝ) =
      ((a0 + lin p x + μ : ℝ) : WithTop ℝ) := by
    intro i hi
    rw [(hlab i hi).1, lin_ex, ← WithTop.coe_add, WithTop.coe_eq_coe]
    have := hcT i hi
    linarith
  have off1 : ∀ i < K, ∀ j < K, i ≠ j → ((a0 + lin p x + μ : ℝ) : WithTop ℝ) <
      c (ex x (g (2 * i)) (g (2 * j + 1))) +
        ((lin p (ex x (g (2 * i)) (g (2 * j + 1))) : ℝ) : WithTop ℝ) := by
    intro i hi j hj hij
    by_cases htop : c (ex x (g (2 * i)) (g (2 * j + 1))) = ⊤
    · rw [htop, top_add]; exact WithTop.coe_lt_top _
    obtain ⟨β, hβ⟩ := WithTop.ne_top_iff_exists.1 htop
    obtain ⟨hadj, hlr⟩ := arc_c (B := B) (a0 := a0) hβ.symm
    have hnt : ¬ (p (g (2 * i)) - p (g (2 * j + 1)) =
        lr c B x a0 (g (2 * i)) (g (2 * j + 1)) - μ) := by
      intro ht
      have := minw_chord Tt hMin (s := 2 * i) (t := 2 * j + 1) (by omega) (by omega) ⟨hadj, ht⟩
      omega
    have hlt := lt_of_le_of_ne (hp _ _ hadj) hnt
    rw [← hβ, lin_ex, ← WithTop.coe_add, WithTop.coe_lt_coe]
    linarith
  -- the B side
  have hf2 : MExchangeAxiom (fun y => IndicatorWT B y + ((lin (fun w => -p w) y : ℝ) : WithTop ℝ)) :=
    mexc_add_linear (mexc_indicator hB) _
  have hx2 : IndicatorWT B x + ((lin (fun w => -p w) x : ℝ) : WithTop ℝ) =
      ((lin (fun w => -p w) x : ℝ) : WithTop ℝ) := by
    simp [IndicatorWT, hxB]
  have diag2 : ∀ i < K, IndicatorWT B (ex x (g (2 * i + 2)) (g (2 * i + 1))) +
      ((lin (fun w => -p w) (ex x (g (2 * i + 2)) (g (2 * i + 1))) : ℝ) : WithTop ℝ) =
      ((lin (fun w => -p w) x + μ : ℝ) : WithTop ℝ) := by
    intro i hi
    rw [lin_ex]
    simp only [IndicatorWT, if_pos (hbT i hi).1, zero_add, WithTop.coe_eq_coe]
    have := (hbT i hi).2
    linarith
  have off2 : ∀ i < K, ∀ j < K, i ≠ j → ((lin (fun w => -p w) x + μ : ℝ) : WithTop ℝ) <
      IndicatorWT B (ex x (g (2 * i + 2)) (g (2 * j + 1))) +
        ((lin (fun w => -p w) (ex x (g (2 * i + 2)) (g (2 * j + 1))) : ℝ) : WithTop ℝ) := by
    intro i hi j hj hij
    by_cases hin : ex x (g (2 * i + 2)) (g (2 * j + 1)) ∈ B
    · obtain ⟨hadj, hlr⟩ := arc_b (c := c) (a0 := a0) hin
      obtain ⟨t, ht, hgt, htc⟩ := pos' i hi
      have hnt : ¬ (p (g (2 * j + 1)) - p (g (2 * i + 2)) =
          lr c B x a0 (g (2 * j + 1)) (g (2 * i + 2)) - μ) := by
        intro hT
        have hT' : Tt (g (2 * j + 1)) (g t) := by rw [← hgt]; exact ⟨hadj, hT⟩
        have := minw_chord Tt hMin (s := 2 * j + 1) (t := t) (by omega) ht hT'
        omega
      have hlt := lt_of_le_of_ne (hp _ _ hadj) hnt
      rw [lin_ex]
      simp only [IndicatorWT, if_pos hin, zero_add, WithTop.coe_lt_coe]
      linarith
    · simp [IndicatorWT, hin]
  -- the two pair lists
  have injU : ∀ i ∈ List.range K, ∀ j ∈ List.range K, g (2 * i) = g (2 * j) → i = j := by
    intro i hi j hj h
    rw [List.mem_range] at hi hj
    have := inj _ _ (by omega) (by omega) h
    omega
  have injV : ∀ i ∈ List.range K, ∀ j ∈ List.range K, g (2 * i + 1) = g (2 * j + 1) → i = j := by
    intro i hi j hj h
    rw [List.mem_range] at hi hj
    have := inj _ _ (by omega) (by omega) h
    omega
  have injU' : ∀ i ∈ List.range K, ∀ j ∈ List.range K, g (2 * i + 2) = g (2 * j + 2) → i = j := by
    intro i hi j hj h
    rw [List.mem_range] at hi hj
    obtain ⟨t1, ht1, hg1, hc1⟩ := pos' i hi
    obtain ⟨t2, ht2, hg2, hc2⟩ := pos' j hj
    have := inj t1 t2 ht1 ht2 (hg1.symm.trans (h.trans hg2))
    omega
  set L1 : List (V × V) := (List.range K).map (fun i => (g (2 * i), g (2 * i + 1))) with hL1
  set L2 : List (V × V) := (List.range K).map (fun i => (g (2 * i + 2), g (2 * i + 1))) with hL2
  have f1 : L1.map Prod.fst = (List.range K).map (fun i => g (2 * i)) := by
    simp [hL1, List.map_map, Function.comp_def]
  have s1 : L1.map Prod.snd = (List.range K).map (fun i => g (2 * i + 1)) := by
    simp [hL1, List.map_map, Function.comp_def]
  have f2 : L2.map Prod.fst = (List.range K).map (fun i => g (2 * i + 2)) := by
    simp [hL2, List.map_map, Function.comp_def]
  have s2 : L2.map Prod.snd = (List.range K).map (fun i => g (2 * i + 1)) := by
    simp [hL2, List.map_map, Function.comp_def]
  have mem1 : ∀ q ∈ L1, ∃ i < K, q = (g (2 * i), g (2 * i + 1)) := by
    intro q hq
    rw [hL1, List.mem_map] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact ⟨i, List.mem_range.1 hi, rfl⟩
  have mem2 : ∀ q ∈ L2, ∃ i < K, q = (g (2 * i + 2), g (2 * i + 1)) := by
    intro q hq
    rw [hL2, List.mem_map] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact ⟨i, List.mem_range.1 hi, rfl⟩
  have um1 := um hf1 hx1 μ L1
    (by rw [f1]; exact List.Nodup.map_on injU List.nodup_range)
    (by rw [s1]; exact List.Nodup.map_on injV List.nodup_range)
    (by
      intro q hq q' hq'
      obtain ⟨i, hi, rfl⟩ := mem1 q hq
      obtain ⟨j, hj, rfl⟩ := mem1 q' hq'
      intro h
      have := inj _ _ (by omega) (by omega) h
      omega)
    (by
      intro q hq
      obtain ⟨i, hi, rfl⟩ := mem1 q hq
      exact diag1 i hi)
    (by
      intro q hq q' hq' hne
      obtain ⟨i, hi, rfl⟩ := mem1 q hq
      obtain ⟨j, hj, rfl⟩ := mem1 q' hq'
      exact off1 i hi j hj (fun h => hne (by rw [h])))
  have um2 := um hf2 hx2 μ L2
    (by rw [f2]; exact List.Nodup.map_on injU' List.nodup_range)
    (by rw [s2]; exact List.Nodup.map_on injV List.nodup_range)
    (by
      intro q hq q' hq'
      obtain ⟨i, hi, rfl⟩ := mem2 q hq
      obtain ⟨j, hj, rfl⟩ := mem2 q' hq'
      intro h
      obtain ⟨t1, ht1, hg1, hc1⟩ := pos' i hi
      have := inj t1 (2 * j + 1) ht1 (by omega) (hg1.symm.trans h)
      omega)
    (by
      intro q hq
      obtain ⟨i, hi, rfl⟩ := mem2 q hq
      exact diag2 i hi)
    (by
      intro q hq q' hq' hne
      obtain ⟨i, hi, rfl⟩ := mem2 q hq
      obtain ⟨j, hj, rfl⟩ := mem2 q' hq'
      exact off2 i hi j hj (fun h => hne (by rw [h])))
  -- the finsets coincide
  have hlen1 : L1.length = K := by simp [hL1]
  have hlen2 : L2.length = K := by simp [hL2]
  have hU : (L2.map Prod.fst).toFinset = (L1.map Prod.fst).toFinset := by
    rw [f1, f2]
    ext w
    simp only [List.mem_toFinset, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases h : i + 1 < K
      · exact ⟨i + 1, h, by congr 1⟩
      · refine ⟨0, hK, ?_⟩
        have : 2 * i + 2 = 2 * K := by omega
        rw [this, hcl]
    · rintro ⟨j, hj, rfl⟩
      by_cases h : 0 < j
      · exact ⟨j - 1, by omega, by congr 1; omega⟩
      · refine ⟨K - 1, by omega, ?_⟩
        have e1 : 2 * (K - 1) + 2 = 2 * K := by omega
        have e2 : j = 0 := by omega
        rw [e1, hcl, e2]
  have hW : (L2.map Prod.snd).toFinset = (L1.map Prod.snd).toFinset := by rw [s1, s2]
  rw [hU, hW] at um2
  set U := (L1.map Prod.fst).toFinset with hUdef
  set W := (L1.map Prod.snd).toFinset with hWdef
  set z := exs x U W with hz
  -- z ∈ B
  have hzB : z ∈ B := by
    by_contra hn
    simp only [IndicatorWT, if_neg hn, top_add, top_le_iff] at um2
    exact WithTop.coe_ne_top um2
  -- sums
  have hsum : ∀ f : ℕ → V, (∀ i ∈ List.range K, ∀ j ∈ List.range K, f i = f j → i = j) →
      ∑ w ∈ ((List.range K).map f).toFinset, p w = ∑ i ∈ Finset.range K, p (f i) := by
    intro f hf
    rw [List.sum_toFinset _ (List.Nodup.map_on hf List.nodup_range), List.map_map]
    exact list_range_sum _ K
  have sU : ∑ w ∈ U, p w = ∑ i ∈ Finset.range K, p (g (2 * i)) := by
    rw [hUdef, f1]; exact hsum _ injU
  have sU' : ∑ w ∈ U, p w = ∑ i ∈ Finset.range K, p (g (2 * i + 2)) := by
    rw [← hU, f2]; exact hsum _ injU'
  have sW : ∑ w ∈ W, p w = ∑ i ∈ Finset.range K, p (g (2 * i + 1)) := by
    rw [hWdef, s1]; exact hsum _ injV
  have hdiff : ∑ i ∈ Finset.range K, (p (g (2 * i + 1)) - p (g (2 * i + 2))) = -((K : ℝ) * μ) := by
    rw [Finset.sum_congr rfl (fun i hi => (hbT i (Finset.mem_range.1 hi)).2)]
    simp
  rw [Finset.sum_sub_distrib] at hdiff
  have hlz : lin p z = lin p x - ∑ a ∈ U, p a + ∑ b ∈ W, p b := lin_exs p x U W
  have um1' : c z + ((lin p z : ℝ) : WithTop ℝ) ≤ ((a0 + lin p x + (K : ℝ) * μ : ℝ) : WithTop ℝ) := by
    have := um1
    rw [hlen1] at this
    exact this
  obtain ⟨s1, s2, hs1, hs2, hle⟩ := wt_two um1'
  have e2 : lin p z = s2 := WithTop.coe_injective hs2
  have hm := hmin z hzB
  rw [hx, hs1, WithTop.coe_le_coe] at hm
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have : (K : ℝ) * μ < 0 := mul_neg_of_pos_of_neg hKpos hμ
  linarith

end M3


/-! ## M4: parity, finite min-mean, no negative closed walk -/

section M4

variable {V : Type u} [Fintype V] [DecidableEq V]

lemma parity_aux (P : ℕ → Prop) (halt : ∀ k, P k ↔ ¬ P (k + 1)) :
    ∀ j, (P (2 * j) ↔ P 0) ∧ (P (2 * j + 1) ↔ ¬ P 0) := by
  intro j
  induction j with
  | zero =>
    have := halt 0
    simp only [zero_add] at this
    simp only [mul_zero, zero_add]
    tauto
  | succ j ih =>
    have h1 := halt (2 * j + 1)
    have h2 := halt (2 * j + 1 + 1)
    have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [e1]
    obtain ⟨ih1, ih2⟩ := ih
    constructor <;> tauto

lemma parity_of_alt (P : ℕ → Prop) (halt : ∀ k, P k ↔ ¬ P (k + 1)) (m : ℕ) (hper : P m ↔ P 0) :
    ∃ K, m = 2 * K := by
  obtain ⟨K, hK | hK⟩ := Nat.even_or_odd' m
  · exact ⟨K, hK⟩
  · exfalso
    have := (parity_aux P halt K).2
    rw [← hK] at this
    tauto

lemma gmod {T : V → V → Prop} {g : ℕ → V} {m : ℕ} (h : MinW T g m) {k : ℕ} (hk : k ≤ m) :
    g (k % m) = g k := by
  rcases Nat.lt_or_ge k m with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]
  · have : k = m := le_antisymm hk h1
    subst this
    rw [Nat.mod_self, h.2.2.1]

lemma minw_ne {T : V → V → Prop} {g : ℕ → V} {m : ℕ} (h : MinW T g m) {i j : ℕ} (hi : i < m)
    (hj : j < m) (hij : i ≠ j) : g i ≠ g j := by
  rcases Nat.lt_or_gt_of_ne hij with h1 | h1
  · exact minw_inj T h h1 hj
  · exact fun e => minw_inj T h h1 hi e.symm

lemma mod_ne_succ {m k : ℕ} (hm : 2 ≤ m) : k % m ≠ (k + 1) % m := by
  rw [mod_succ_eq (by omega)]
  split_ifs with h
  · omega
  · have := Nat.mod_lt k (by omega : 0 < m); omega

variable {c : (V → ℤ) → WithTop ℝ} {B : Set (V → ℤ)} {x : V → ℤ} {a0 : ℝ}

theorem alt_struct (hc : MExchangeAxiom c) (hB : ExchangeAxiomB B) (hxB : x ∈ B)
    (hx : c x = ((a0 : ℝ) : WithTop ℝ)) (p : V → ℝ) (μ : ℝ) (hμ : μ < 0)
    (hp : ∀ a b, adjM c B x a0 a b → p a - p b ≤ lr c B x a0 a b - μ)
    {g : ℕ → V} {m : ℕ}
    (hMin : MinW (fun a b => adjM c B x a0 a b ∧ p a - p b = lr c B x a0 a b - μ) g m)
    (hm2 : 2 ≤ m) (k : ℕ) :
    (c (ex x (g (k % m)) (g ((k + 1) % m))) =
        ((lr c B x a0 (g (k % m)) (g ((k + 1) % m)) + a0 : ℝ) : WithTop ℝ)) ↔
      ¬ (c (ex x (g ((k + 1) % m)) (g ((k + 1 + 1) % m))) =
        ((lr c B x a0 (g ((k + 1) % m)) (g ((k + 1 + 1) % m)) + a0 : ℝ) : WithTop ℝ)) := by
  have t1 := minw_period _ hMin k
  have t2 := minw_period _ hMin (k + 1)
  have hm0 : 0 < m := by omega
  have hab : g (k % m) ≠ g ((k + 1) % m) :=
    minw_ne hMin (Nat.mod_lt _ hm0) (Nat.mod_lt _ hm0) (mod_ne_succ hm2)
  have hbd : g ((k + 1) % m) ≠ g ((k + 1 + 1) % m) :=
    minw_ne hMin (Nat.mod_lt _ hm0) (Nat.mod_lt _ hm0) (mod_ne_succ hm2)
  constructor
  · intro h1 h2
    exact no_two_c hc hx p μ hμ hp hab hbd t1.2 t2.2 h1 h2
  · intro h1
    by_contra h2
    rcases arc_cases t1.1 with h3 | ⟨b1, l1⟩
    · exact h2 h3
    rcases arc_cases t2.1 with h4 | ⟨b2, l2⟩
    · exact h1 h4
    exact no_two_b hB hxB p μ hμ hp hab hbd t1.2 t2.2 b1 l1 b2 l2

theorem from_minw (hc : MExchangeAxiom c) (hB : ExchangeAxiomB B) (hxB : x ∈ B)
    (hx : c x = ((a0 : ℝ) : WithTop ℝ)) (hmin : ∀ z ∈ B, c x ≤ c z)
    (p : V → ℝ) (μ : ℝ) (hμ : μ < 0)
    (hp : ∀ a b, adjM c B x a0 a b → p a - p b ≤ lr c B x a0 a b - μ)
    {g : ℕ → V} {m : ℕ}
    (hMin : MinW (fun a b => adjM c B x a0 a b ∧ p a - p b = lr c B x a0 a b - μ) g m)
    (hm2 : 2 ≤ m)
    (h0 : c (ex x (g 0) (g 1)) = ((lr c B x a0 (g 0) (g 1) + a0 : ℝ) : WithTop ℝ)) : False := by
  have halt := alt_struct hc hB hxB hx p μ hμ hp hMin hm2
  set LAB : ℕ → Prop := fun k => c (ex x (g (k % m)) (g ((k + 1) % m))) =
    ((lr c B x a0 (g (k % m)) (g ((k + 1) % m)) + a0 : ℝ) : WithTop ℝ) with hLAB
  have halt' : ∀ k, LAB k ↔ ¬ LAB (k + 1) := halt
  have hper : LAB m ↔ LAB 0 := by
    simp only [hLAB, Nat.mod_self, Nat.zero_mod, Nat.add_mod_left, zero_add]
  have hev := parity_aux LAB halt'
  obtain ⟨K, hK⟩ := parity_of_alt LAB halt' m hper
  have hL0 : LAB 0 := by
    show c (ex x (g (0 % m)) (g ((0 + 1) % m))) = _
    rw [Nat.zero_mod, zero_add, Nat.mod_eq_of_lt (by omega : 1 < m)]
    exact h0
  subst hK
  apply contra_alt hc hB hxB hx hmin p μ hμ hp g K (by omega) hMin
  intro i hi
  have g1 := gmod hMin (k := 2 * i) (by omega)
  have g2 := gmod hMin (k := 2 * i + 1) (by omega)
  have g3 := gmod hMin (k := 2 * i + 1 + 1) (by omega)
  have l1 : LAB (2 * i) := (hev i).1.2 hL0
  have l2 : ¬ LAB (2 * i + 1) := fun h => (hev i).2.1 h hL0
  simp only [hLAB] at l1 l2
  rw [g1, g2] at l1
  rw [g2, g3] at l2
  refine ⟨l1, ?_⟩
  rw [show 2 * i + 2 = 2 * i + 1 + 1 by ring]
  exact l2

def toG {N : ℕ} (t : Fin (N + 1) × (Fin (N + 1) → V)) (k : ℕ) : V :=
  t.2 ⟨min k N, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma toG_mk {N : ℕ} (n : Fin (N + 1)) (g : ℕ → V) {k : ℕ} (hk : k ≤ N) :
    toG (n, fun j : Fin (N + 1) => g j.val) k = g k := by
  simp [toG, min_eq_left hk]

lemma walkOK_congr {adj : V → V → Prop} {g1 g2 : ℕ → V} {m : ℕ} (h : ∀ k ≤ m, g1 k = g2 k)
    (hw : walkOK adj g1 m) : walkOK adj g2 m := by
  intro i hi
  rw [← h i (by omega), ← h (i + 1) (by omega)]
  exact hw i hi

lemma wsum_congr {l : V → V → ℝ} {g1 g2 : ℕ → V} {m : ℕ} (h : ∀ k ≤ m, g1 k = g2 k) :
    wsum l g1 m = wsum l g2 m := by
  unfold wsum
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [h i (by omega), h (i + 1) (by omega)]

/-- The exchange graph of `(c, B)` at a minimiser `x` of `c` on `B` has no negative closed walk. -/
theorem nnc (hc : MExchangeAxiom c) (hB : ExchangeAxiomB B) (hxB : x ∈ B)
    (hx : c x = ((a0 : ℝ) : WithTop ℝ)) (hmin : ∀ z ∈ B, c x ≤ c z) :
    ∀ m g, walkOK (adjM c B x a0) g m → g m = g 0 → 0 ≤ wsum (lr c B x a0) g m := by
  by_contra hneg
  obtain ⟨m1, g1, hw1, hc1, hm1, hm1N, hneg1⟩ : ∃ m g, walkOK (adjM c B x a0) g m ∧ g m = g 0 ∧
      0 < m ∧ m ≤ Fintype.card V ∧ wsum (lr c B x a0) g m < 0 := by
    by_contra h2
    apply hneg
    apply closed_nonneg_of_short
    intro m g hw hcl hm
    by_contra h3
    apply h2
    refine ⟨m, g, hw, hcl, ?_, hm, lt_of_not_ge h3⟩
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp [wsum] at h3
    · exact h0
  set N := Fintype.card V with hN
  let S : Set (Fin (N + 1) × (Fin (N + 1) → V)) :=
    {t | 0 < t.1.val ∧ walkOK (adjM c B x a0) (toG t) t.1.val ∧ toG t t.1.val = toG t 0}
  let mean : Fin (N + 1) × (Fin (N + 1) → V) → ℝ :=
    fun t => wsum (lr c B x a0) (toG t) t.1.val / t.1.val
  have memS : ∀ m (hm : m ≤ N) (g : ℕ → V), 0 < m → walkOK (adjM c B x a0) g m → g m = g 0 →
      ((⟨m, by omega⟩ : Fin (N + 1)), fun j : Fin (N + 1) => g j.val) ∈ S ∧
      mean ((⟨m, by omega⟩ : Fin (N + 1)), fun j : Fin (N + 1) => g j.val) =
        wsum (lr c B x a0) g m / m := by
    intro m hm g h0 hw hcl
    have ag : ∀ k ≤ m, toG ((⟨m, by omega⟩ : Fin (N + 1)), fun j : Fin (N + 1) => g j.val) k = g k :=
      fun k hk => toG_mk _ g (by omega)
    refine ⟨⟨h0, walkOK_congr (fun k hk => (ag k hk).symm) hw, ?_⟩, ?_⟩
    · show toG _ m = toG _ 0
      rw [ag m le_rfl, ag 0 (Nat.zero_le _), hcl]
    · show wsum _ (toG _) m / (m : ℝ) = _
      rw [wsum_congr ag]
  obtain ⟨tstar, htS, htmin⟩ := Set.exists_min_image S mean (Set.toFinite S)
    ⟨_, (memS m1 hm1N g1 hm1 hw1 hc1).1⟩
  set μ := mean tstar with hμdef
  have hμ : μ < 0 := by
    have h1 := htmin _ (memS m1 hm1N g1 hm1 hw1 hc1).1
    rw [(memS m1 hm1N g1 hm1 hw1 hc1).2] at h1
    have : wsum (lr c B x a0) g1 m1 / m1 < 0 := div_neg_of_neg_of_pos hneg1 (by exact_mod_cast hm1)
    linarith
  have hsub : ∀ m g, wsum (fun a b => lr c B x a0 a b - μ) g m =
      wsum (lr c B x a0) g m - m * μ := by
    intro m g
    unfold wsum
    rw [Finset.sum_sub_distrib]
    simp
  have hcyc' : ∀ m g, walkOK (adjM c B x a0) g m → g m = g 0 →
      0 ≤ wsum (fun a b => lr c B x a0 a b - μ) g m := by
    apply closed_nonneg_of_short
    intro m g hw hcl hm
    rw [hsub]
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp [wsum]
    obtain ⟨hS, hmean⟩ := memS m hm g h0 hw hcl
    have h1 := htmin _ hS
    rw [hmean, le_div_iff₀ (by exact_mod_cast h0)] at h1
    linarith
  obtain ⟨p, hp⟩ := potential (adjM c B x a0) (fun a b => lr c B x a0 a b - μ) hcyc'
  obtain ⟨hpos, hwst, hclst⟩ := htS
  have hm0ne : ((tstar.1.val : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hzero : wsum (fun a b => lr c B x a0 a b - μ) (toG tstar) tstar.1.val ≤ 0 := by
    rw [hsub]
    have e : ((tstar.1.val : ℕ) : ℝ) * μ = wsum (lr c B x a0) (toG tstar) tstar.1.val := by
      rw [hμdef]
      show ((tstar.1.val : ℕ) : ℝ) * (wsum (lr c B x a0) (toG tstar) tstar.1.val / tstar.1.val) = _
      field_simp
    linarith
  have htight := all_tight (adjM c B x a0) (fun a b => lr c B x a0 a b - μ) p hp (toG tstar)
    tstar.1.val hwst hclst hzero
  let P : ℕ → Prop := fun n => ∃ g : ℕ → V, 0 < n ∧
    walkOK (fun a b => adjM c B x a0 a b ∧ p a - p b = lr c B x a0 a b - μ) g n ∧ g n = g 0
  have : DecidablePred P := Classical.decPred P
  have hPex : ∃ n, P n := ⟨tstar.1.val, toG tstar, hpos, htight, hclst⟩
  obtain ⟨g0, hg0pos, hg0w, hg0c⟩ := Nat.find_spec hPex
  have hMin : MinW (fun a b => adjM c B x a0 a b ∧ p a - p b = lr c B x a0 a b - μ) g0
      (Nat.find hPex) :=
    ⟨hg0pos, hg0w, hg0c, fun m' g' h1 h2 h3 => Nat.find_min' hPex ⟨g', h1, h2, h3⟩⟩
  set m0 := Nat.find hPex with hm0def
  have hm2 : 2 ≤ m0 := by
    by_contra h
    have h1 : m0 = 1 := by omega
    have t : adjM c B x a0 (g0 0) (g0 1) ∧ p (g0 0) - p (g0 1) = lr c B x a0 (g0 0) (g0 1) - μ :=
      hg0w 0 (by omega)
    rw [h1] at hg0c
    rw [hg0c, lr_self hx hxB, sub_self] at t
    linarith [t.2]
  by_cases h0 : c (ex x (g0 0) (g0 1)) = ((lr c B x a0 (g0 0) (g0 1) + a0 : ℝ) : WithTop ℝ)
  · exact from_minw hc hB hxB hx hmin p μ hμ hp hMin hm2 h0
  · have halt0 := alt_struct hc hB hxB hx p μ hμ hp hMin hm2 0
    have e1 : 1 % m0 = 1 := Nat.mod_eq_of_lt (by omega)
    simp only [Nat.zero_mod, zero_add, e1] at halt0
    have hL1 := by_contra fun hb => h0 (halt0.2 hb)
    have hMin' := minw_rot _ hMin
    apply from_minw hc hB hxB hx hmin p μ hμ hp hMin' hm2
    show c (ex x (g0 ((0 + 1) % m0)) (g0 ((1 + 1) % m0))) =
      ((lr c B x a0 (g0 ((0 + 1) % m0)) (g0 ((1 + 1) % m0)) + a0 : ℝ) : WithTop ℝ)
    rw [zero_add, e1]
    exact hL1

end M4

/-! ## CORE: M-convex intersection for a function and a set (Murota DCA Thm 8.17 special case) -/

theorem core {V : Type u} [Fintype V] [DecidableEq V] (c : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hB : ExchangeAxiomB B) (hc : MExchangeAxiom c)
    (xs : V → ℤ) (hxs : xs ∈ B) (a : ℝ) (ha : c xs = ((a : ℝ) : WithTop ℝ))
    (hmin : ∀ x ∈ B, c xs ≤ c x) :
    ∃ p : V → ℤ,
      (∀ (x : V → ℤ) (b : ℝ), c x = ((b : ℝ) : WithTop ℝ) →
        a + ∑ i, (p i : ℝ) * (xs i : ℝ) ≤ b + ∑ i, (p i : ℝ) * (x i : ℝ)) ∧
      (∀ z ∈ B, ∑ i, (p i : ℝ) * (z i : ℝ) ≤ ∑ i, (p i : ℝ) * (xs i : ℝ)) := by
  have hxc : c xs ≠ ⊤ := by rw [ha]; exact WithTop.coe_ne_top
  obtain ⟨ka, hka⟩ : ∃ k : ℤ, a = k := by
    rcases hcZ xs with h | ⟨k, hk⟩
    · exact absurd h hxc
    · exact ⟨k, WithTop.coe_injective (ha.symm.trans hk)⟩
  have hN := nnc hc hB hxs ha hmin
  obtain ⟨p, hp⟩ := potential (adjM c B xs a) (lr c B xs a) hN
  set P : V → ℤ := fun v => ⌊p v⌋ with hPdef
  have floor_le : ∀ u v (n : ℤ), p u - p v ≤ n → P u - P v ≤ n := by
    intro u v n h
    have h1 := Int.floor_le (p u)
    have h2 := Int.lt_floor_add_one (p v)
    have h3 : ((P u : ℤ) : ℝ) < (P v : ℝ) + n + 1 := by simp only [hPdef]; linarith
    have h4 : P u < P v + n + 1 := by exact_mod_cast h3
    omega
  refine ⟨P, ?_, ?_⟩
  · have hf := mexc_add_linear hc (fun i => (P i : ℝ))
    have hloc : ∀ u v, c xs + ((lin (fun i => (P i : ℝ)) xs : ℝ) : WithTop ℝ) ≤
        c (ex xs u v) + ((lin (fun i => (P i : ℝ)) (ex xs u v) : ℝ) : WithTop ℝ) := by
      intro u v
      by_cases htop : c (ex xs u v) = ⊤
      · rw [htop, top_add]; exact le_top
      obtain ⟨β, hβ⟩ := WithTop.ne_top_iff_exists.1 htop
      obtain ⟨kb, hkb⟩ : ∃ k : ℤ, β = k := by
        rcases hcZ (ex xs u v) with h | ⟨k, hk⟩
        · exact absurd h htop
        · exact ⟨k, WithTop.coe_injective (hβ.trans hk)⟩
      obtain ⟨hadj, hlr⟩ := arc_c (B := B) (a0 := a) hβ.symm
      have h1 := hp u v hadj
      have h2 := floor_le u v (kb - ka) (by push_cast; linarith)
      have h3 : ((P u : ℝ) - P v) ≤ (kb : ℝ) - ka := by exact_mod_cast h2
      rw [← hβ, ha, lin_ex, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
      linarith
    have hg := local_opt hf (by rw [ha, ← WithTop.coe_add]; exact WithTop.coe_ne_top) hloc
    intro x b hxb
    have := hg x
    rw [ha, hxb, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at this
    exact this
  · have hf := mexc_add_linear (mexc_indicator hB) (fun i => -(P i : ℝ))
    have hloc : ∀ u v, IndicatorWT B xs + ((lin (fun i => -(P i : ℝ)) xs : ℝ) : WithTop ℝ) ≤
        IndicatorWT B (ex xs u v) + ((lin (fun i => -(P i : ℝ)) (ex xs u v) : ℝ) : WithTop ℝ) := by
      intro u v
      by_cases hin : ex xs u v ∈ B
      · obtain ⟨hadj, hlr⟩ := arc_b (c := c) (a0 := a) (a := v) (b := u) hin
        have h1 := hp v u hadj
        have h2 : P v ≤ P u := Int.floor_mono (by linarith)
        have h3 : (P v : ℝ) ≤ P u := by exact_mod_cast h2
        rw [lin_ex]
        simp only [IndicatorWT, if_pos hxs, if_pos hin, zero_add, WithTop.coe_le_coe]
        linarith
      · simp [IndicatorWT, hin]
    have hg := local_opt hf (by simp [IndicatorWT, hxs]) hloc
    intro z hz
    have := hg z
    simp only [IndicatorWT, if_pos hxs, if_pos hz, zero_add, WithTop.coe_le_coe] at this
    have e : ∀ y : V → ℤ, lin (fun i => -(P i : ℝ)) y = -(∑ i, (P i : ℝ) * (y i : ℝ)) := by
      intro y
      simp only [lin, neg_mul, Finset.sum_neg_distrib]
    rw [e, e] at this
    linarith

/-! ## Assembly -/

lemma exB_singleton {V : Type u} [Fintype V] [DecidableEq V] (x0 : V → ℤ) :
    ExchangeAxiomB ({x0} : Set (V → ℤ)) := by
  intro x hx y hy w hw
  simp only [Set.mem_singleton_iff] at hx hy
  subst hx; subst hy
  simp [SuppPos] at hw

lemma toEReal_coe (b : ℝ) : ToEReal ((b : ℝ) : WithTop ℝ) = ((b : ℝ) : EReal) := rfl

lemma toEReal_top : ToEReal (⊤ : WithTop ℝ) = ⊤ := rfl

lemma le_sub_of_add_le' (e : EReal) (m s : ℝ) (h : (((m + s : ℝ)) : EReal) ≤ e) :
    (s : EReal) ≤ e - (m : EReal) := by
  induction e using EReal.rec with
  | bot => simp at h
  | top => simp
  | coe b =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [EReal.coe_le_coe_iff] at h
    linarith

end P0fc

open Classical DiscreteConvex.ConjugacyDualityD in
theorem solution {V : Type u} [Fintype V] [DecidableEq V] (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r)
    (hB : ExchangeAxiomB B) (hc : MExchangeAxiom c) (hr : MExchangeAxiom r)
    (hr0 : r (fun _ => (0 : ℤ)) = 0) (hfeas : ∃ x ∈ B, c x ≠ ⊤)
    (hbdd : PhiR c r B (fun _ => 0) ≠ ⊥) :
    PhiR c r B (fun _ => 0) = ConvexConjE (ConvexConjE (PhiR c r B)) (fun _ => 0) ∧
    ConvexConjE (ConvexConjE (PhiR c r B)) (fun _ => 0) =
      sSup {t : EReal | ∃ y, t = GRSmall c r B y} ∧
    {y | GRSmall c r B y = sSup {t : EReal | ∃ y', t = GRSmall c r B y'}} =
      (fun p => fun v => -p v) '' SubDifferentialZEReal (PhiR c r B) (fun _ => 0) ∧
    (SubDifferentialZEReal (PhiR c r B) (fun _ => 0)).Nonempty := by
  -- definitional identities
  have hP : PhiR c r B = PhiGen (Fr c r B) := rfl
  have hG : GRSmall c r B = GGen (Fr c r B) := rfl
  have gd := P0fc.gen_dual (Fr c r B)
  -- values of φr at 0 on B
  have hF0 : ∀ x, Fr c r B x (fun _ => 0) = c x + IndicatorWT B x := by
    intro x
    simp only [Fr, F0, hr0, add_zero]
  have hPle : ∀ x ∈ B, PhiR c r B (fun _ => 0) ≤ ToEReal (c x) := by
    intro x hx
    refine sInf_le ⟨x, ?_⟩
    rw [hF0]; simp [IndicatorWT, hx]
  -- φr(0) is a real number l
  obtain ⟨x0, hx0B, hx0c⟩ := hfeas
  have hne_top : PhiR c r B (fun _ => 0) ≠ ⊤ := by
    intro h
    have := hPle x0 hx0B
    rw [h, top_le_iff] at this
    exact hx0c (WithBot.coe_injective (this.trans P0fc.toEReal_top.symm))
  obtain ⟨l, hl⟩ : ∃ l : ℝ, PhiR c r B (fun _ => 0) = (l : EReal) :=
    ⟨(PhiR c r B (fun _ => 0)).toReal, (EReal.coe_toReal hne_top hbdd).symm⟩
  -- integer values of c on B are bounded below by l; take a minimiser
  have hbelow : ∀ x ∈ B, ∀ k : ℤ, c x = (((k : ℝ)) : WithTop ℝ) → l ≤ k := by
    intro x hx k hk
    have := hPle x hx
    rw [hl, hk, P0fc.toEReal_coe, EReal.coe_le_coe_iff] at this
    exact this
  obtain ⟨k0, hk0⟩ : ∃ k : ℤ, c x0 = (((k : ℝ)) : WithTop ℝ) := by
    rcases hcZ x0 with h | h
    · exact absurd h hx0c
    · exact h
  have hbdP : ∃ b : ℤ, ∀ k : ℤ, (∃ x ∈ B, c x = (((k : ℝ)) : WithTop ℝ)) → b ≤ k := by
    refine ⟨⌊l⌋, ?_⟩
    rintro k ⟨x, hx, hk⟩
    have h1 := hbelow x hx k hk
    rw [Int.floor_le_iff]
    linarith
  obtain ⟨ks, ⟨xs, hxsB, hxsc⟩, hks⟩ := Int.exists_least_of_bdd
    (P := fun k : ℤ => ∃ x ∈ B, c x = (((k : ℝ)) : WithTop ℝ)) hbdP ⟨k0, x0, hx0B, hk0⟩
  have hmin : ∀ x ∈ B, c xs ≤ c x := by
    intro x hx
    rcases hcZ x with h | ⟨k, hk⟩
    · rw [h]; exact le_top
    · rw [hxsc, hk]
      have := hks k ⟨x, hx, hk⟩
      exact_mod_cast this
  -- CORE twice: (c, B) at xs and (r, {0}) at 0
  obtain ⟨p, hp1, hp2⟩ := P0fc.core c B hcZ hB hc xs hxsB (ks : ℝ) hxsc hmin
  obtain ⟨q, hq1, -⟩ := P0fc.core r {fun _ => (0 : ℤ)} hrZ (P0fc.exB_singleton _) hr
    (fun _ => 0) rfl 0 (by rw [hr0]; rfl) (fun x hx => by rw [Set.mem_singleton_iff] at hx; rw [hx])
  -- the subgradient y = p - q, with lower bound φr(u) ≥ ks + <y,u>
  set y : V → ℤ := fun v => p v - q v with hy
  have hlow : ∀ u : V → ℤ, (((ks : ℝ) + ∑ i, (y i : ℝ) * (u i : ℝ) : ℝ) : EReal) ≤ PhiR c r B u := by
    intro u
    refine le_sInf ?_
    rintro t ⟨x, rfl⟩
    simp only [Fr, F0, IndicatorWT]
    rcases hcZ x with hcx | ⟨kx, hkx⟩
    · rw [hcx]; simp [P0fc.toEReal_top]
    by_cases hxu : (fun v => x v + u v) ∈ B
    swap
    · simp [hxu, P0fc.toEReal_top]
    rcases hrZ u with hru | ⟨ku, hku⟩
    · rw [hru]; simp [P0fc.toEReal_top]
    rw [if_pos hxu, hkx, hku, add_zero, ← WithTop.coe_add, P0fc.toEReal_coe, EReal.coe_le_coe_iff]
    have h1 := hp1 x kx hkx
    have h2 := hp2 _ hxu
    have h3 := hq1 u ku hku
    simp only [Int.cast_zero, mul_zero, Finset.sum_const_zero, add_zero] at h3
    simp only [Int.cast_add] at h2
    have e1 : ∑ i, (p i : ℝ) * ((x i : ℝ) + (u i : ℝ)) =
        ∑ i, (p i : ℝ) * (x i : ℝ) + ∑ i, (p i : ℝ) * (u i : ℝ) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, (y i : ℝ) * (u i : ℝ) =
        ∑ i, (p i : ℝ) * (u i : ℝ) - ∑ i, (q i : ℝ) * (u i : ℝ) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by
        simp only [hy, Int.cast_sub]; ring
    rw [e1] at h2
    rw [e2]
    linarith
  have hval : PhiR c r B (fun _ => 0) = ((ks : ℝ) : EReal) := by
    apply le_antisymm
    · have := hPle xs hxsB
      rwa [hxsc, P0fc.toEReal_coe] at this
    · have := hlow (fun _ => 0)
      simpa using this
  have hsub : y ∈ SubDifferentialZEReal (PhiR c r B) (fun _ => 0) := by
    intro u
    rw [hval]
    have := P0fc.le_sub_of_add_le' _ _ _ (hlow u)
    simpa [Int.cast_zero, sub_zero] using this
  have hC := P0fc.biconj_of_subgradient (PhiR c r B) (ks : ℝ) hval ⟨y, hsub⟩
  have hg : ∀ y' : V → ℤ, GRSmall c r B y' = -(ConvexConjE (PhiR c r B) (fun v => -y' v)) :=
    fun y' => gd.1 y'
  refine ⟨hC.1, ?_, ?_, ⟨y, hsub⟩⟩
  · rw [hG, gd.2]; rfl
  · simp only [hg]
    exact hC.2
