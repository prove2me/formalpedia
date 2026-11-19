-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_2_step
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:24:48.397317+00:00
-- url     : https://prove2.me/submissions/ef0033d2-6b33-4b78-a0ca-b3efb5ba4844

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_matrix_exists_rank_normal_form
import Theorems.Thm_DiazModulus_dalag_prop_12_2_det

open Complex ComplexConjugate

/-! # DALAG Prop. 12.2, the induction step

Put `N` in rank normal form: `P₀NQ₀ = (I_{r₀} 0; 0 0)` with `P₀`, `Q₀` invertible over `k`. Since `M − xN` has
entries in the `k`-subspace `F₁` and `P₀`, `Q₀` have entries in `k`, the matrix `M̃ = P₀MQ₀` is
`x·(I_{r₀} 0; 0 0)` plus a matrix over `F₁`. If `F₁ = 0`, then `M̃ = x·(I_{r₀} 0; 0 0)`, whose leading block
`x·I_{r₀}` has determinant `x^{r₀} ≠ 0`. Otherwise write `M̃ = (xI + A, B; C, D)` with `A, B, C, D` over `F₁`.
The hypothesis on `F₁`, applied to `D`, gives invertible `P'`, `Q'` over `k` and `r'` such that `P'DQ'` vanishes
outside its leading `r' × r'` block `D'`, and `det D'` is a unit. Multiplying `M̃` by `diag(I, P')` on the left and
`diag(I, Q')` on the right gives `(xI + A, BQ'; P'C, P'DQ')`: its entries with both indices at least `r₀ + r'`
vanish, and its leading `(r₀ + r')`-block is `(xI + A, B'; C', D')` with `A, B', C', D'` over `F₁ ⊆ k(F₁)`. As
`x` is transcendental over `k(F₁)` and `det D'` is a unit, the determinant of that block is a unit. So
`r = r₀ + r'`, `P = diag(I, P')·P₀` and `Q = Q₀·diag(I, Q')` work. -/

namespace RC8B_D4

open DiazModulus

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem mul_left_mem (F : Submodule k K) {a b c : Type*} [Fintype b]
    (P : Matrix a b k) (M : Matrix b c K) (hM : ∀ i j, M i j ∈ F) :
    ∀ i j, (P.map (algebraMap k K) * M) i j ∈ F := fun i j => by
  simp only [Matrix.mul_apply, Matrix.map_apply, ← Algebra.smul_def]
  exact F.sum_mem fun l _ => F.smul_mem _ (hM l j)

theorem mul_right_mem (F : Submodule k K) {a b c : Type*} [Fintype b]
    (M : Matrix a b K) (Q : Matrix b c k) (hM : ∀ i j, M i j ∈ F) :
    ∀ i j, (M * Q.map (algebraMap k K)) i j ∈ F := fun i j => by
  simp only [Matrix.mul_apply, Matrix.map_apply, mul_comm (M i _), ← Algebra.smul_def]
  exact F.sum_mem fun l _ => F.smul_mem _ (hM i l)

end RC8B_D4

open DiazModulus RC8B_D4 in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] (F₁ : Submodule k K)
    (hF₁ : ∀ (s t : ℕ) (M : Matrix (Fin s) (Fin t) K), (∀ i j, M i j ∈ F₁) →
      ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det)
    (x : K) (hx : x ≠ 0)
    (hxF₁ : F₁ = ⊥ ∨ Transcendental (IntermediateField.adjoin k (F₁ : Set K)) x)
    {s t : ℕ} (M : Matrix (Fin s) (Fin t) K) (N : Matrix (Fin s) (Fin t) k)
    (hMN : ∀ i j, M i j - x * algebraMap k K (N i j) ∈ F₁) :
    ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det := by
  classical
  obtain ⟨r₀, P₀, Q₀, hr₀s, hr₀t, hP₀, hQ₀, hN⟩ := DiazModulus.matrix_exists_rank_normal_form N
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le hr₀s
  obtain ⟨t', rfl⟩ := Nat.exists_eq_add_of_le hr₀t
  set ι := algebraMap k K with hι
  set Mt := P₀.map ι * M * Q₀.map ι with hMt
  -- step 2: Mt = x • (I_r 0; 0 0) + (entries in F₁)
  have hMt_mem : ∀ i j, Mt i j - x * (if i.val = j.val ∧ i.val < r₀ then 1 else 0) ∈ F₁ := by
    have h1 : ∀ i j, (M - x • N.map ι) i j ∈ F₁ := fun i j => by
      simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using hMN i j
    have h3 : P₀.map ι * (M - x • N.map ι) * Q₀.map ι = Mt - x • (P₀ * N * Q₀).map ι := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul,
        hMt]
    intro i j
    have h4 := mul_right_mem F₁ _ Q₀ (mul_left_mem F₁ P₀ _ h1) i j
    rw [h3, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, hN, smul_eq_mul] at h4
    simpa [apply_ite ι] using h4
  rcases hxF₁ with hF | htr
  · -- case F₁ = ⊥ (the printed n = 1)
    subst hF
    have hMt_eq : ∀ i j, Mt i j = x * (if i.val = j.val ∧ i.val < r₀ then 1 else 0) :=
      fun i j => sub_eq_zero.1 ((Submodule.mem_bot k).1 (hMt_mem i j))
    refine ⟨r₀, hr₀s, hr₀t, P₀, Q₀, hP₀, hQ₀, fun i j hi _ => ?_, ?_⟩
    · rw [← hMt, hMt_eq, if_neg (by omega), mul_zero]
    · have : Mt.submatrix (Fin.castLE hr₀s) (Fin.castLE hr₀t) = x • (1 : Matrix (Fin r₀) (Fin r₀) K) := by
        ext a b
        simp only [Matrix.submatrix_apply, hMt_eq, Fin.val_castLE, Matrix.smul_apply, Matrix.one_apply,
          Fin.ext_iff, smul_eq_mul, a.isLt, and_true]
      rw [← hMt, this, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
      exact (pow_ne_zero _ hx).isUnit
  -- case x transcendental over L = k(F₁)
  set L := IntermediateField.adjoin k (F₁ : Set K)
  have hFL : ∀ z ∈ F₁, z ∈ L := fun z hz => IntermediateField.subset_adjoin k _ hz
  let es : Fin r₀ ⊕ Fin s' ≃ Fin (r₀ + s') := finSumFinEquiv
  let et : Fin r₀ ⊕ Fin t' ≃ Fin (r₀ + t') := finSumFinEquiv
  let Mt' := Mt.submatrix es et
  have hD₁ : ∀ i j, Mt'.toBlocks₂₂ i j ∈ F₁ := fun i j => by
    simpa [Mt', es, et, Matrix.toBlocks₂₂] using hMt_mem (Fin.natAdd r₀ i) (Fin.natAdd r₀ j)
  have hB₀ : ∀ i j, Mt'.toBlocks₁₂ i j ∈ F₁ := fun i j => by
    have := hMt_mem (Fin.castAdd s' i) (Fin.natAdd r₀ j)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    rw [if_neg (by omega), mul_zero, sub_zero] at this
    simpa [Mt', es, et, Matrix.toBlocks₁₂] using this
  have hC₀ : ∀ i j, Mt'.toBlocks₂₁ i j ∈ F₁ := fun i j => by
    have := hMt_mem (Fin.natAdd r₀ i) (Fin.castAdd t' j)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    rw [if_neg (by omega), mul_zero, sub_zero] at this
    simpa [Mt', es, et, Matrix.toBlocks₂₁] using this
  have hA₀ : ∀ i j, (Mt'.toBlocks₁₁ - x • (1 : Matrix (Fin r₀) (Fin r₀) K)) i j ∈ F₁ := fun i j => by
    have := hMt_mem (Fin.castAdd s' i) (Fin.castAdd t' j)
    simp only [Fin.val_castAdd, i.isLt, and_true] at this
    simpa [Mt', es, et, Matrix.toBlocks₁₁, Matrix.one_apply, Fin.ext_iff] using this
  obtain ⟨r', hr's, hr't, P', Q', hP', hQ', hz', hA'⟩ := hF₁ s' t' Mt'.toBlocks₂₂ hD₁
  let Ph : Matrix (Fin (r₀ + s')) (Fin (r₀ + s')) k := Matrix.reindex es es (Matrix.fromBlocks 1 0 0 P')
  let Qh : Matrix (Fin (r₀ + t')) (Fin (r₀ + t')) k := Matrix.reindex et et (Matrix.fromBlocks 1 0 0 Q')
  -- the block identity
  have key : ((Ph * P₀).map ι * M * (Q₀ * Qh).map ι).submatrix es et =
      Matrix.fromBlocks Mt'.toBlocks₁₁ (Mt'.toBlocks₁₂ * Q'.map ι) (P'.map ι * Mt'.toBlocks₂₁)
        (P'.map ι * Mt'.toBlocks₂₂ * Q'.map ι) := by
    have e1 : (Ph * P₀).map ι * M * (Q₀ * Qh).map ι = Ph.map ι * Mt * Qh.map ι := by
      simp only [Matrix.map_mul, hMt, Matrix.mul_assoc]
    rw [e1, ← Matrix.submatrix_mul_equiv _ _ _ et, ← Matrix.submatrix_mul_equiv _ _ _ es]
    have eP : (Ph.map ι).submatrix es es = Matrix.fromBlocks 1 0 0 (P'.map ι) := by
      ext (u | u) (v | v) <;> simp [Ph, Matrix.one_apply, apply_ite ι]
    have eQ : (Qh.map ι).submatrix et et = Matrix.fromBlocks 1 0 0 (Q'.map ι) := by
      ext (u | u) (v | v) <;> simp [Qh, Matrix.one_apply, apply_ite ι]
    rw [eP, eQ, ← Matrix.fromBlocks_toBlocks (Mt.submatrix es et), Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp [Mt', Matrix.mul_assoc]
  refine ⟨r₀ + r', by omega, by omega, Ph * P₀, Q₀ * Qh, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ hP₀
    simpa [Ph, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁] using hP'
  · rw [Matrix.det_mul]
    refine IsUnit.mul hQ₀ ?_
    simpa [Qh, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁] using hQ'
  · -- the zero block
    intro i j hi hj
    have hi' : i = es (Sum.inr ⟨i.val - r₀, by omega⟩) := Fin.ext (by simp [es]; omega)
    have hj' : j = et (Sum.inr ⟨j.val - r₀, by omega⟩) := Fin.ext (by simp [et]; omega)
    have := congrFun (congrFun key (Sum.inr ⟨i.val - r₀, by omega⟩)) (Sum.inr ⟨j.val - r₀, by omega⟩)
    rw [Matrix.submatrix_apply, ← hi', ← hj', Matrix.fromBlocks_apply₂₂] at this
    rw [this]
    exact hz' _ _ (by simp; omega) (by simp; omega)
  · -- the new A: reindex the top-left block by Fin r₀ ⊕ Fin r'
    set G := (Ph * P₀).map ι * M * (Q₀ * Qh).map ι
    rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv : Fin r₀ ⊕ Fin r' ≃ Fin (r₀ + r'))]
    have hcs : (Fin.castLE (show r₀ + r' ≤ r₀ + s' by omega)) ∘ (finSumFinEquiv : Fin r₀ ⊕ Fin r' ≃ _)
        = es ∘ Sum.map id (Fin.castLE hr's) := by
      funext u; rcases u with u | u <;> exact Fin.ext (by simp [es])
    have hct : (Fin.castLE (show r₀ + r' ≤ r₀ + t' by omega)) ∘ (finSumFinEquiv : Fin r₀ ⊕ Fin r' ≃ _)
        = et ∘ Sum.map id (Fin.castLE hr't) := by
      funext u; rcases u with u | u <;> exact Fin.ext (by simp [et])
    rw [Matrix.submatrix_submatrix, hcs, hct, ← Matrix.submatrix_submatrix, key]
    have hblk : (Matrix.fromBlocks Mt'.toBlocks₁₁ (Mt'.toBlocks₁₂ * Q'.map ι) (P'.map ι * Mt'.toBlocks₂₁)
        (P'.map ι * Mt'.toBlocks₂₂ * Q'.map ι)).submatrix (Sum.map id (Fin.castLE hr's))
          (Sum.map id (Fin.castLE hr't)) =
        Matrix.fromBlocks (x • 1 + (Mt'.toBlocks₁₁ - x • 1))
          ((Mt'.toBlocks₁₂ * Q'.map ι).submatrix id (Fin.castLE hr't))
          ((P'.map ι * Mt'.toBlocks₂₁).submatrix (Fin.castLE hr's) id)
          ((P'.map ι * Mt'.toBlocks₂₂ * Q'.map ι).submatrix (Fin.castLE hr's) (Fin.castLE hr't)) := by
      rw [add_sub_cancel]
      ext (u | u) (v | v) <;> rfl
    rw [hblk]
    exact DiazModulus.dalag_prop_12_2_det L x htr _ _ _ _ (fun i j => hFL _ (hA₀ i j))
      (fun i j => hFL _ (mul_right_mem F₁ _ Q' hB₀ i _))
      (fun i j => hFL _ (mul_left_mem F₁ P' _ hC₀ _ j))
      (fun i j => hFL _ (mul_right_mem F₁ _ Q' (mul_left_mem F₁ P' _ hD₁) _ _)) hA'
