-- Prove2me | solution 1 for Erdos592.specker_omega_pow_nat_not
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:29:15.057395+00:00
-- url     : https://prove2.me/submissions/d27b4494-1011-4102-adc0-d735b25e3f6e

import Definitions.Def_Erdos592_Defs
import Mathlib

set_option autoImplicit false
open Cardinal Ordinal

universe u

namespace Erdos592Sol

section tools
variable {S : Type u} [LinearOrder S] [WellFoundedLT S]

/-- The order type of a union of two sets, the first lying below the second. -/
lemma type_union_le {A B : Set S} (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    typeLT ↥(A ∪ B) ≤ typeLT ↥A + typeLT ↥B := by
  rw [← type_sum_lex, type_le_iff']
  classical
  refine ⟨RelEmbedding.ofMonotone
    (fun x : ↥(A ∪ B) => if hx : x.1 ∈ A then (Sum.inl ⟨x.1, hx⟩ : ↥A ⊕ ↥B)
      else Sum.inr ⟨x.1, x.2.resolve_left hx⟩) ?_⟩
  intro x y hxy
  by_cases hx : x.1 ∈ A <;> by_cases hy : y.1 ∈ A
  · simpa [hx, hy] using hxy
  · simp [hx, hy]
  · exact absurd (h _ hy _ (x.2.resolve_left hx)) (not_lt.2 hxy.le)
  · simpa [hx, hy] using hxy


/-- Level sets of a monotone `ℕ`-valued grading with fibres of order type `< γ` have order type
`< γ`, for `γ` additively principal. -/
lemma graded_lt {γ : Ordinal} (hγ : IsPrincipal (· + ·) γ) (A : Set S) (f : S → ℕ)
    (hf : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → f x ≤ f y)
    (hfib : ∀ k : ℕ, typeLT ↥(A ∩ {x | f x = k}) < γ) :
    ∀ m : ℕ, typeLT ↥(A ∩ {x | f x < m}) < γ := by
  intro m
  induction m with
  | zero =>
    have hemp : IsEmpty ↥(A ∩ {x | f x < 0}) := ⟨fun x => absurd x.2.2 (by simp)⟩
    have h0 : typeLT ↥(A ∩ {x | f x < 0}) = 0 := type_eq_zero_of_empty _
    rw [h0]
    exact lt_of_le_of_lt zero_le (hfib 0)
  | succ m ih =>
    have hset : A ∩ {x | f x < m + 1} = (A ∩ {x | f x < m}) ∪ (A ∩ {x | f x = m}) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨hxA, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hx with h | h
        · exact Or.inl ⟨hxA, h⟩
        · exact Or.inr ⟨hxA, h⟩
      · rintro (⟨hxA, hx⟩ | ⟨hxA, hx⟩)
        · exact ⟨hxA, by omega⟩
        · exact ⟨hxA, by omega⟩
    rw [hset]
    refine lt_of_le_of_lt (type_union_le ?_) (hγ ih (hfib m))
    rintro a ⟨haA, ha⟩ b ⟨hbA, hb⟩
    simp only [Set.mem_ofPred_eq] at ha hb
    by_contra hab
    have := hf b hbA a haA (not_lt.1 hab)
    omega

/-- A monotone `ℕ`-grading with all fibres of order type `< γ` gives order type `≤ γ`. -/
lemma graded_le {γ : Ordinal} (hγ : IsPrincipal (· + ·) γ) (A : Set S) (f : S → ℕ)
    (hf : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → f x ≤ f y)
    (hfib : ∀ k : ℕ, typeLT ↥(A ∩ {x | f x = k}) < γ) : typeLT ↥A ≤ γ := by
  refine le_of_forall_lt fun o ho => ?_
  obtain ⟨x, rfl⟩ := typein_surj (α := ↥A) (· < ·) ho
  have h1 : typein (α := ↥A) (· < ·) x = typeLT ↥(Set.Iio x) := rfl
  rw [h1]
  refine lt_of_le_of_lt ?_ (graded_lt hγ A f hf hfib (f x.1 + 1))
  rw [type_le_iff']
  refine ⟨RelEmbedding.ofMonotone
    (fun y : ↥(Set.Iio x) => (⟨y.1.1, y.1.2, ?_⟩ : ↥(A ∩ {z | f z < f x.1 + 1}))) ?_⟩
  · have := hf y.1.1 y.1.2 x.1 x.2 (le_of_lt y.2)
    show f y.1.1 < f x.1 + 1
    omega
  · intro a b hab
    exact hab

end tools

lemma principal_pow (n : ℕ) : IsPrincipal (· + ·) ((ω : Ordinal.{u}) ^ n) := by
  rw [← opow_natCast]
  exact isPrincipal_add_omega0_opow _

lemma type_lt_nat : typeLT ℕ = ω := type_nat_lt

lemma type_lex_nat_nat : typeLT (ℕ ×ₗ ℕ) = ω ^ 2 := by
  have := Ordinal.type_prod_lex (· < · : ℕ → ℕ → Prop) (· < · : ℕ → ℕ → Prop)
  rw [type_nat_lt] at this
  rw [pow_two]
  exact this

/-- Finite sets have finite order type. -/
lemma type_finite_lt_omega {S : Type u} [LinearOrder S] [WellFoundedLT S] {A : Set S}
    (hA : A.Finite) : typeLT ↥A < ω := by
  have : Fintype ↥A := hA.fintype
  rw [type_fintype]
  exact natCast_lt_omega0 _

/-! ### The base case: a triangle-free graph on `ω ^ 3` without independent sets of type `ω ^ 3` -/

/-- A witness that `W` carries a triangle-free graph with no independent set of order type `γ`. -/
def TF (W : Type u) [LinearOrder W] [WellFoundedLT W] (γ : Ordinal.{u}) : Prop :=
  ∃ B : W → W → Prop, (∀ x y, B x y → B y x) ∧ (∀ x, ¬ B x x) ∧
    (∀ x y z, B x y → B y z → B x z → False) ∧
    ∀ s : Set W, (∀ x ∈ s, ∀ y ∈ s, ¬ B x y) → typeLT ↥s ≠ γ

abbrev T3 : Type := ℕ ×ₗ (ℕ ×ₗ ℕ)

def co1 (x : T3) : ℕ := (ofLex x).1
def co2 (x : T3) : ℕ := (ofLex (ofLex x).2).1
def co3 (x : T3) : ℕ := (ofLex (ofLex x).2).2

lemma T3_lt_iff {x y : T3} :
    x < y ↔ co1 x < co1 y ∨ (co1 x = co1 y ∧ (co2 x < co2 y ∨ (co2 x = co2 y ∧ co3 x < co3 y))) := by
  rw [Prod.Lex.lt_iff, Prod.Lex.lt_iff]
  rfl

lemma co1_mono {x y : T3} (h : x ≤ y) : co1 x ≤ co1 y := by
  rcases h.lt_or_eq with h | h
  · rcases T3_lt_iff.1 h with h | h <;> omega
  · rw [h]

lemma co2_mono {x y : T3} (h : x ≤ y) (h1 : co1 x = co1 y) : co2 x ≤ co2 y := by
  rcases h.lt_or_eq with h | h
  · rcases T3_lt_iff.1 h with h | ⟨_, h | h⟩ <;> omega
  · rw [h]

lemma T3_ext {x y : T3} (h1 : co1 x = co1 y) (h2 : co2 x = co2 y) (h3 : co3 x = co3 y) : x = y := by
  have : ofLex x = ofLex y := by
    refine Prod.ext h1 ?_
    have : ofLex (ofLex x).2 = ofLex (ofLex y).2 := Prod.ext h2 h3
    exact ofLex.injective this
  exact ofLex.injective this

def mk3 (a b c : ℕ) : T3 := toLex (a, toLex (b, c))

@[simp] lemma co1_mk3 (a b c : ℕ) : co1 (mk3 a b c) = a := rfl
@[simp] lemma co2_mk3 (a b c : ℕ) : co2 (mk3 a b c) = b := rfl
@[simp] lemma co3_mk3 (a b c : ℕ) : co3 (mk3 a b c) = c := rfl

lemma mk3_co (x : T3) : mk3 (co1 x) (co2 x) (co3 x) = x := T3_ext rfl rfl rfl

/-- `x → y`: `x₂ < y₁ < x₃ < y₂`. -/
def arr (x y : T3) : Prop := co2 x < co1 y ∧ co1 y < co3 x ∧ co3 x < co2 y

lemma typeLT_T3 : typeLT T3 = ω ^ 3 := by
  have := Ordinal.type_prod_lex (· < · : ℕ ×ₗ ℕ → ℕ ×ₗ ℕ → Prop) (· < · : ℕ → ℕ → Prop)
  have h3 : (ω : Ordinal.{0}) ^ 3 = ω ^ 2 * ω := pow_succ _ _
  rw [h3, ← type_lex_nat_nat, ← type_nat_lt]
  exact this


lemma omega_lt_pow (m n : ℕ) (h : m < n) : (ω : Ordinal.{u}) ^ m < ω ^ n := by
  rw [← opow_natCast, ← opow_natCast]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 (by exact_mod_cast h)

lemma fibre1_le (s : Set T3) (k : ℕ) : typeLT ↥(s ∩ {x | co1 x = k}) ≤ ω ^ 2 := by
  rw [← type_lex_nat_nat, type_le_iff']
  refine ⟨RelEmbedding.ofMonotone
    (fun x : ↥(s ∩ {x | co1 x = k}) => (ofLex x.1).2) ?_⟩
  intro x y hxy
  have h1 := T3_lt_iff.1 hxy
  have hx : co1 x.1 = k := x.2.2
  have hy : co1 y.1 = k := y.2.2
  rw [Prod.Lex.lt_iff]
  show co2 x.1 < co2 y.1 ∨ (co2 x.1 = co2 y.1 ∧ co3 x.1 < co3 y.1)
  omega

lemma fibre2_le (A : Set T3) (k m : ℕ) (hA : ∀ x ∈ A, co1 x = k ∧ co2 x = m) :
    typeLT ↥A ≤ ω := by
  rw [← type_nat_lt, type_le_iff']
  refine ⟨RelEmbedding.ofMonotone (fun x : ↥A => co3 x.1) ?_⟩
  intro x y hxy
  have h1 := T3_lt_iff.1 hxy
  have hx := hA x.1 x.2
  have hy := hA y.1 y.2
  show co3 x.1 < co3 y.1
  omega

lemma base_indep (s : Set T3) (hs : ∀ x ∈ s, ∀ y ∈ s, ¬ arr x y) : typeLT ↥s < ω ^ 3 := by
  have hp2 : IsPrincipal (· + ·) ((ω : Ordinal.{0}) ^ 2) := principal_pow 2
  have hp3 : IsPrincipal (· + ·) ((ω : Ordinal.{0}) ^ 3) := principal_pow 3
  have hpω : IsPrincipal (· + ·) (ω : Ordinal.{0}) := by simpa using principal_pow.{0} 1
  have hω1 : (ω : Ordinal.{0}) < ω ^ 2 := by simpa using omega_lt_pow.{0} 1 2 (by norm_num)
  have hω2 : (ω : Ordinal.{0}) ^ 2 < ω ^ 3 := omega_lt_pow 2 3 (by norm_num)
  have hco1 : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → co1 x ≤ co1 y := fun x _ y _ h => co1_mono h
  by_cases hR2 : ∀ M : ℕ, ∃ a, M < a ∧ {b | ∃ c, mk3 a b c ∈ s}.Infinite
  · by_cases hR1 : ∃ a b, {c | mk3 a b c ∈ s}.Infinite
    · exfalso
      obtain ⟨a₀, b₀, hC⟩ := hR1
      obtain ⟨a₁, ha₁, hB⟩ := hR2 b₀
      obtain ⟨c, hc, hca⟩ := hC.exists_gt a₁
      obtain ⟨b', ⟨c', hc'⟩, hbc⟩ := hB.exists_gt c
      exact hs (mk3 a₀ b₀ c) hc (mk3 a₁ b' c') hc' ⟨ha₁, hca, hbc⟩
    · have hfin : ∀ a b, {c | mk3 a b c ∈ s}.Finite := fun a b => by
        by_contra h
        exact hR1 ⟨a, b, h⟩
      have hfib : ∀ k : ℕ, typeLT ↥(s ∩ {x | co1 x = k}) < ω ^ 2 := by
        intro k
        refine lt_of_le_of_lt (graded_le hpω (s ∩ {x | co1 x = k}) co2 ?_ ?_) hω1
        · rintro x ⟨-, hx⟩ y ⟨-, hy⟩ hxy
          exact co2_mono hxy (by simp only [Set.mem_ofPred_eq] at hx hy; omega)
        · intro m
          refine type_finite_lt_omega ?_
          refine ((hfin k m).image (mk3 k m)).subset ?_
          rintro x ⟨⟨hxs, hx1⟩, hx2⟩
          simp only [Set.mem_ofPred_eq] at hx1 hx2
          refine ⟨co3 x, ?_, ?_⟩
          · show mk3 k m (co3 x) ∈ s
            rw [← hx1, ← hx2, mk3_co]; exact hxs
          · rw [← hx1, ← hx2, mk3_co]
      exact lt_of_le_of_lt (graded_le hp2 s co1 hco1 hfib) hω2
  · push Not at hR2
    obtain ⟨M, hM⟩ := hR2
    have hfinB : ∀ a, M < a → {b | ∃ c, mk3 a b c ∈ s}.Finite := hM
    have hfibk : ∀ k, M < k → typeLT ↥(s ∩ {x | co1 x = k}) < ω ^ 2 := by
      intro k hk
      obtain ⟨N, hN⟩ := (hfinB k hk).bddAbove
      have hlt := graded_lt hp2 (s ∩ {x | co1 x = k}) co2
        (fun x ⟨_, hx⟩ y ⟨_, hy⟩ hxy => co2_mono hxy (by simp only [Set.mem_ofPred_eq] at hx hy; omega))
        (fun m => lt_of_le_of_lt (fibre2_le _ k m (by
          rintro x ⟨⟨_, hx1⟩, hx2⟩
          exact ⟨hx1, hx2⟩)) hω1) (N + 1)
      have hsub : s ∩ {x | co1 x = k} ∩ {x | co2 x < N + 1} = s ∩ {x | co1 x = k} := by
        refine Set.inter_eq_left.2 ?_
        rintro x ⟨hxs, hx1⟩
        simp only [Set.mem_ofPred_eq] at hx1 ⊢
        have : co2 x ∈ {b | ∃ c, mk3 k b c ∈ s} := ⟨co3 x, by rw [← hx1, mk3_co]; exact hxs⟩
        have := hN this
        omega
      rwa [hsub] at hlt
    have hP : typeLT ↥(s ∩ {x | co1 x < M + 1}) < ω ^ 3 :=
      graded_lt hp3 s co1 hco1 (fun k => lt_of_le_of_lt (fibre1_le s k) hω2) (M + 1)
    have hT : typeLT ↥(s ∩ {x | M < co1 x}) ≤ ω ^ 2 := by
      refine graded_le hp2 (s ∩ {x | M < co1 x}) co1
        (fun x ⟨_, _⟩ y ⟨_, _⟩ h => co1_mono h) ?_
      intro k
      by_cases hk : M < k
      · have : s ∩ {x | M < co1 x} ∩ {x | co1 x = k} = s ∩ {x | co1 x = k} := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨⟨a, _⟩, c⟩; exact ⟨a, c⟩
          · rintro ⟨a, c⟩; exact ⟨⟨a, by omega⟩, c⟩
        rw [this]
        exact hfibk k hk
      · have hemp : s ∩ {x | M < co1 x} ∩ {x | co1 x = k} = ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨⟨_, h1⟩, h2⟩
          omega
        rw [hemp]
        have h0 : typeLT ↥(∅ : Set T3) = 0 := by
          have : IsEmpty ↥(∅ : Set T3) := inferInstance
          exact type_eq_zero_of_empty _
        rw [h0]
        exact lt_of_le_of_lt zero_le (lt_of_lt_of_le hω1 le_rfl)
    have hs_eq : s = (s ∩ {x | co1 x < M + 1}) ∪ (s ∩ {x | M < co1 x}) := by
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hx
        by_cases h : co1 x < M + 1
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, by omega⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    rw [hs_eq]
    refine lt_of_le_of_lt (type_union_le ?_) (hp3 hP (lt_of_le_of_lt hT hω2))
    rintro a ⟨_, ha⟩ b ⟨_, hb⟩
    simp only [Set.mem_ofPred_eq] at ha hb
    exact T3_lt_iff.2 (Or.inl (by omega))

lemma TF_T3 : TF T3 (ω ^ 3) := by
  refine ⟨fun x y => arr x y ∨ arr y x, fun x y h => h.symm, ?_, ?_, ?_⟩
  · intro x h
    rcases h with h | h <;> (simp only [arr] at h; omega)
  · intro x y z h1 h2 h3
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      (simp only [arr] at h1 h2 h3; omega)
  · intro s hs
    exact ne_of_lt (base_indep s fun x hx y hy h => hs x hx y hy (Or.inl h))


universe v

/-- Transport of a witness along an order isomorphism. -/
lemma TF_of_iso {W : Type u} {W' : Type v} [LinearOrder W] [WellFoundedLT W]
    [LinearOrder W'] [WellFoundedLT W'] {γ : Ordinal.{u}} {γ' : Ordinal.{v}} (e : W ≃o W')
    (hγ : Ordinal.lift.{v} γ = Ordinal.lift.{u} γ') (h : TF W γ) : TF W' γ' := by
  obtain ⟨B, hsym, hirr, htri, hind⟩ := h
  refine ⟨fun x y => B (e.symm x) (e.symm y), fun x y h => hsym _ _ h, fun x => hirr _,
    fun x y z h1 h2 h3 => htri _ _ _ h1 h2 h3, ?_⟩
  intro s' hs' hty
  let s : Set W := e ⁻¹' s'
  let f : ↥s ≃o ↥s' :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun y => ⟨e.symm y.1, by simp [s, y.2]⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp
      map_rel_iff' := fun {a b} => by
        show e a.1 ≤ e b.1 ↔ a ≤ b
        exact e.le_iff_le }
  have h1 : Ordinal.lift.{v} (typeLT ↥s) = Ordinal.lift.{u} (typeLT ↥s') :=
    f.toRelIsoLT.ordinal_lift_type_eq
  refine hind s ?_ ?_
  · intro x hx y hy hB
    exact hs' (e x) hx (e y) hy (by simpa using hB)
  · have : Ordinal.lift.{v} (typeLT ↥s) = Ordinal.lift.{v} γ := by rw [h1, hty, ← hγ]
    exact Ordinal.lift_inj.1 this


/-- Stacking `ω` copies of a witness for an additively indecomposable `γ` gives a witness for
`γ * ω`: inside each block use the witness, all cross pairs are red. -/
lemma TF_step {W : Type} [LinearOrder W] [WellFoundedLT W] {γ : Ordinal.{0}}
    (hγ : IsPrincipal (· + ·) γ) (hγ0 : 0 < γ) (hW : typeLT W = γ) (h : TF W γ) :
    TF (ℕ ×ₗ W) (γ * ω) := by
  obtain ⟨B₀, hsym, hirr, htri, hind⟩ := h
  refine ⟨fun x y => (ofLex x).1 = (ofLex y).1 ∧ B₀ (ofLex x).2 (ofLex y).2,
    fun x y ⟨h1, h2⟩ => ⟨h1.symm, hsym _ _ h2⟩, fun x ⟨_, h⟩ => hirr _ h, ?_, ?_⟩
  · rintro x y z ⟨h1, h2⟩ ⟨h3, h4⟩ ⟨_, h6⟩
    exact htri _ _ _ h2 h4 h6
  · intro s hs
    have hfib : ∀ k : ℕ, typeLT ↥(s ∩ {x | (ofLex x).1 = k}) < γ := by
      intro k
      let t : Set W := {w | toLex (k, w) ∈ s}
      have h1 : typeLT ↥(s ∩ {x | (ofLex x).1 = k}) ≤ typeLT ↥t := by
        rw [type_le_iff']
        refine ⟨RelEmbedding.ofMonotone
          (fun x : ↥(s ∩ {x | (ofLex x).1 = k}) => (⟨(ofLex x.1).2, ?_⟩ : ↥t)) ?_⟩
        · have hx : (ofLex x.1).1 = k := x.2.2
          show toLex (k, (ofLex x.1).2) ∈ s
          have : ofLex x.1 = (k, (ofLex x.1).2) := Prod.ext hx rfl
          have h' : toLex (k, (ofLex x.1).2) = x.1 := (congrArg toLex this).symm
          rw [h']; exact x.2.1
        · intro x y hxy
          have hx : (ofLex x.1).1 = k := x.2.2
          have hy : (ofLex y.1).1 = k := y.2.2
          have := Prod.Lex.lt_iff.1 hxy
          show (ofLex x.1).2 < (ofLex y.1).2
          rcases this with h | ⟨_, h⟩
          · omega
          · exact h
      have h2 : typeLT ↥t ≠ γ := hind t (by
        intro a ha b hb hB
        exact hs _ ha _ hb ⟨rfl, hB⟩)
      have h3 : typeLT ↥t ≤ γ := hW ▸ type_set_le t
      exact lt_of_le_of_lt h1 (lt_of_le_of_ne h3 h2)
    have hle : typeLT ↥s ≤ γ :=
      graded_le hγ s (fun x => (ofLex x).1)
        (fun x _ y _ h => Prod.Lex.monotone_fst _ _ h) hfib
    have hlt : γ < γ * ω := by
      have := mul_lt_mul_of_pos_left one_lt_omega0 hγ0
      simpa using this
    exact ne_of_lt (lt_of_le_of_lt hle hlt)

/-- Witnesses for all `ω ^ n`, `n ≥ 3`. -/
lemma exists_TF (n : ℕ) (hn : 3 ≤ n) :
    ∃ (W : Type) (_ : LinearOrder W) (_ : WellFoundedLT W),
      typeLT W = ω ^ n ∧ TF W (ω ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨T3, inferInstance, inferInstance, typeLT_T3, TF_T3⟩
  | succ n hn ih =>
    obtain ⟨W, i1, i2, hW, hTF⟩ := ih
    refine ⟨ℕ ×ₗ W, inferInstance, inferInstance, ?_, ?_⟩
    · have := Ordinal.type_prod_lex (· < · : W → W → Prop) (· < · : ℕ → ℕ → Prop)
      rw [pow_succ, ← hW, ← type_nat_lt]
      exact this
    · rw [pow_succ]
      exact TF_step (principal_pow n) (by
        have := omega_lt_pow.{0} 0 n (by omega)
        simpa using this) hW hTF


/-- A witness on `α.ToType` refutes `α → (α, 3)²`. -/
lemma not_ramsey_of_TF {α : Ordinal.{u}} (h : TF α.ToType α) :
    ¬ Erdos592.OrdinalCardinalRamsey.{u} α α 3 := by
  intro hR
  obtain ⟨B, hsym, hirr, htri, hind⟩ := h
  let G : SimpleGraph α.ToType := SimpleGraph.fromRel B
  have hadj : ∀ x y, G.Adj x y ↔ B x y := fun x y => by
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, h | h⟩
      · exact h
      · exact hsym _ _ h
    · intro h
      exact ⟨fun e => hirr x (e ▸ h), Or.inl h⟩
  rcases hR Gᶜ G isCompl_compl.symm with ⟨s, hs1, hs2⟩ | ⟨s, hs1, hs2⟩
  · refine hind s ?_ hs2
    intro x hx y hy hB
    by_cases hxy : x = y
    · subst hxy
      exact hirr _ hB
    · exact ((SimpleGraph.compl_adj _ _ _).1 (hs1 hx hy hxy)).2 ((hadj x y).2 hB)
  · obtain ⟨t, ht, hc⟩ := Cardinal.mk_set_eq_nat_iff_finset.1
      (by exact_mod_cast hs2 : #s = ((3 : ℕ) : Cardinal))
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hc
    have hx : x ∈ s := by rw [← ht]; simp
    have hy : y ∈ s := by rw [← ht]; simp
    have hz : z ∈ s := by rw [← ht]; simp
    exact htri x y z ((hadj _ _).1 (hs1 hx hy hxy)) ((hadj _ _).1 (hs1 hy hz hyz))
      ((hadj _ _).1 (hs1 hx hz hxz))

end Erdos592Sol

theorem solution (n : ℕ) (hn : 3 ≤ n) :
    ¬ Erdos592.OrdinalCardinalRamsey.{u} (ω ^ (n : Ordinal.{u})) (ω ^ (n : Ordinal.{u})) 3 := by
  obtain ⟨W, i1, i2, hW, hTF⟩ := Erdos592Sol.exists_TF n hn
  have hlift : Ordinal.lift.{u} (ω ^ n : Ordinal.{0}) =
      Ordinal.lift.{0} (ω ^ (n : Ordinal.{u}) : Ordinal.{u}) := by
    have hl : ∀ m : ℕ, Ordinal.lift.{u} ((ω : Ordinal.{0}) ^ m) = (ω : Ordinal.{u}) ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ k ih => rw [pow_succ, pow_succ, Ordinal.lift_mul, ih, Ordinal.lift_omega0]
    have hl2 : Ordinal.lift.{0} ((ω : Ordinal.{u}) ^ n) = (ω : Ordinal.{u}) ^ n :=
      Ordinal.lift_id' _
    rw [opow_natCast, hl, hl2]
  have hlift' : Ordinal.lift.{u} (typeLT W) =
      Ordinal.lift.{0} (typeLT (ω ^ (n : Ordinal.{u}) : Ordinal.{u}).ToType) := by
    rw [hW, type_toType]; exact hlift
  obtain ⟨e⟩ := Ordinal.lift_type_eq.1 hlift'
  exact Erdos592Sol.not_ramsey_of_TF
    (Erdos592Sol.TF_of_iso (OrderIso.ofRelIsoLT e) hlift hTF)
