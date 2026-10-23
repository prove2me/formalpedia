-- Prove2me | solution 1 for CircletTSP.Facet.stsp_dim
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:06:45.959425+00:00
-- url     : https://prove2.me/submissions/df2a7beb-04e0-4306-9e25-e65caf7f2707

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_CircletTSP_Facet_Setting
import Theorems.Thm_CircletTSP_Facet_stsp_vectorSpan_eq_degree_zero

open scoped BigOperators

namespace CircletTSP.Facet.DimensionProof

noncomputable section

abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def symmZero (n : ℕ) : Submodule ℝ (Fin n → Fin n → ℝ) where
  carrier := {X | (∀ i j, X i j = X j i) ∧ ∀ i, X i i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    constructor
    · intro i j
      simp only [Pi.add_apply, hX.1 i j, hY.1 i j]
    · intro i
      simp [hX.2 i, hY.2 i]
  smul_mem' := by
    intro a X hX
    constructor
    · intro i j
      simp only [Pi.smul_apply, hX.1 i j]
    · intro i
      simp [hX.2 i]

def edgeMatrix {n : ℕ} (f : Edge n → ℝ) (i j : Fin n) : ℝ :=
  if h : i < j then f ⟨(i, j), h⟩ else if h : j < i then f ⟨(j, i), h⟩ else 0

lemma edgeMatrix_symm {n : ℕ} (f : Edge n → ℝ) (i j : Fin n) :
    edgeMatrix f i j = edgeMatrix f j i := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [edgeMatrix, h, not_lt_of_gt h]
  · rfl
  · simp [edgeMatrix, h, not_lt_of_gt h]

lemma edgeMatrix_diag {n : ℕ} (f : Edge n → ℝ) (i : Fin n) : edgeMatrix f i i = 0 := by
  simp [edgeMatrix]

def edgeEquiv (n : ℕ) : (Edge n → ℝ) ≃ₗ[ℝ] symmZero n where
  toFun f := ⟨edgeMatrix f, ⟨edgeMatrix_symm f, edgeMatrix_diag f⟩⟩
  invFun X p := X.val p.val.1 p.val.2
  left_inv f := by
    funext p
    simp [edgeMatrix, p.property]
  right_inv X := by
    apply Subtype.ext
    funext i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [edgeMatrix, h]
    · simp [edgeMatrix, X.property.2 i]
    · simp [edgeMatrix, h, not_lt_of_gt h, X.property.1 i j]
  map_add' f g := by
    apply Subtype.ext
    funext i j
    change edgeMatrix (f + g) i j = edgeMatrix f i j + edgeMatrix g i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [edgeMatrix, h]
    · simp [edgeMatrix]
    · simp [edgeMatrix, h, not_lt_of_gt h]
  map_smul' a f := by
    apply Subtype.ext
    funext i j
    change edgeMatrix (a • f) i j = a • edgeMatrix f i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [edgeMatrix, h]
    · simp [edgeMatrix]
    · simp [edgeMatrix, h, not_lt_of_gt h]

lemma symmZero_finrank (n : ℕ) : Module.finrank ℝ (symmZero n) = n.choose 2 := by
  rw [← (edgeEquiv n).finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp only [Edge, Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin n))

def degree (n : ℕ) : symmZero n →ₗ[ℝ] (Fin n → ℝ) where
  toFun X i := ∑ j, X.val i j
  map_add' X Y := by ext i; simp [Finset.sum_add_distrib]
  map_smul' a X := by ext i; simp [Finset.mul_sum]

lemma degree_surjective (n : ℕ) (hn : 3 ≤ n) : Function.Surjective (degree n) := by
  intro b
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) - 2 ≠ 0 := by linarith
  let s : ℝ := ∑ i, b i
  let f : Fin n → Fin n → ℝ := fun i j => (b i + b j - s / ((n : ℝ) - 1)) / ((n : ℝ) - 2)
  let X : Fin n → Fin n → ℝ := fun i j => if i = j then 0 else f i j
  have hX : X ∈ symmZero n := by
    constructor
    · intro i j
      by_cases h : i = j
      · subst j; rfl
      · simp [X, f, h, Ne.symm h, add_comm]
    · intro i; simp [X]
  refine ⟨⟨X, hX⟩, ?_⟩
  funext i
  change (∑ j, X i j) = b i
  have he (j : Fin n) : X i j = f i j - if i = j then f i i else 0 := by
    by_cases h : i = j
    · subst j; simp [X]
    · simp [X, h]
  simp_rw [he]
  simp only [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [f, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change ((n : ℝ) * b i + s - n * s / ((n : ℝ) - 1)) / ((n : ℝ) - 2) -
    (b i + b i - s / ((n : ℝ) - 1)) / ((n : ℝ) - 2) = b i
  field_simp
  ring

lemma degree_ker_finrank (n : ℕ) (hn : 3 ≤ n) :
    Module.finrank ℝ (LinearMap.ker (degree n)) = n * (n - 3) / 2 := by
  have hr := (degree n).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (degree_surjective n hn), finrank_top,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin, symmZero_finrank] at hr
  rw [Nat.choose_two_right] at hr
  have he : n - 1 = (n - 3) + 2 := by omega
  rw [he, Nat.mul_add] at hr
  omega

def spanKerEquiv (n : ℕ)
    (hspan : (vectorSpan ℝ (STSP n) : Set (Fin n → Fin n → ℝ)) =
      {x | (∀ i j, x i j = x j i) ∧ (∀ i, x i i = 0) ∧ ∀ i, ∑ j, x i j = 0}) :
    vectorSpan ℝ (STSP n) ≃ₗ[ℝ] LinearMap.ker (degree n) where
  toFun x := by
    have hx := (Set.ext_iff.mp hspan x.val).mp x.property
    refine ⟨⟨x.val, hx.1, hx.2.1⟩, ?_⟩
    exact funext hx.2.2
  invFun x := by
    refine ⟨x.val.val, (Set.ext_iff.mp hspan x.val.val).mpr ?_⟩
    refine ⟨x.val.property.1, x.val.property.2, ?_⟩
    intro i
    exact congrFun x.property i
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

lemma stsp_dim_of_span_characterization (n : ℕ) (hn : 3 ≤ n)
    (hspan : (vectorSpan ℝ (STSP n) : Set (Fin n → Fin n → ℝ)) =
      {x | (∀ i j, x i j = x j i) ∧ (∀ i, x i i = 0) ∧ ∀ i, ∑ j, x i j = 0}) :
    Disjunctive.Polarity.PolyDim (STSP n) = ((n * (n - 3) / 2 : ℕ) : ℤ) := by
  have hne : (STSP n).Nonempty := by
    refine ⟨MetricTSP.tourVec (Equiv.refl (Fin n)), ?_⟩
    exact subset_convexHull ℝ _ (Set.mem_range_self _)
  simp only [Disjunctive.Polarity.PolyDim, if_pos hne]
  congr 1
  rw [(spanKerEquiv n hspan).finrank_eq, degree_ker_finrank n hn]

end
end CircletTSP.Facet.DimensionProof


/-- The STSP dimension follows from its affine direction space and the unsigned degree map. -/
theorem solution (n : ℕ) (hn : 3 ≤ n) :
    Disjunctive.Polarity.PolyDim (CircletTSP.Facet.STSP n) = ((n * (n - 3) / 2 : ℕ) : ℤ) := by
  exact CircletTSP.Facet.DimensionProof.stsp_dim_of_span_characterization n hn
    (CircletTSP.Facet.stsp_vectorSpan_eq_degree_zero n hn)
