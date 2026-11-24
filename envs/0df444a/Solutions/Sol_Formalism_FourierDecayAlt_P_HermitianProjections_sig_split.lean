-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.sig_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:17:07.513211+00:00
-- url     : https://prove2.me/submissions/0c44b648-85dd-4819-b2e9-6e03a8797094

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_star_mul_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections
namespace Formalism.FourierDecayAlt.P.HermitianProjections
theorem _root_.solution {p q : ℕ} (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hG : G.IsHermitian) (hdet : G.det ≠ 0)
    (ψ₁ : (Fin p ⊕ Fin q → ℂ) →ₗ[ℂ] (Fin p → ℂ)) (h₁ : ∀ c, ψ₁ c = 0 → (star c ⬝ᵥ (G *ᵥ c)).re ≤ 0)
    (ψ₂ : (Fin p ⊕ Fin q → ℂ) →ₗ[ℂ] (Fin q → ℂ)) (h₂ : ∀ c, ψ₂ c = 0 → 0 ≤ (star c ⬝ᵥ (G *ᵥ c)).re) :
    ∃ Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, IsUnit Q.det ∧ Qᴴ * G * Q = fromBlocks 1 0 0 (-1) := by
  classical
  set U : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ↑hG.eigenvectorUnitary with hUd
  set lam := hG.eigenvalues with hlam
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2
  have hspec : G = U * diagonal (RCLike.ofReal ∘ lam) * star U := by
    have := hG.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at this
  have hD : Uᴴ * G * U = diagonal (fun i => (lam i : ℂ)) := by
    rw [← Matrix.star_eq_conjTranspose]
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [hUU, Matrix.mul_one, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rfl
  have hform : ∀ c, star (U *ᵥ c) ⬝ᵥ (G *ᵥ (U *ᵥ c)) = ∑ i, star (c i) * ((lam i : ℂ) * c i) := by
    intro c
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  have hlam0 : ∀ i, lam i ≠ 0 := by
    have h1 : Uᴴ.det * U.det = 1 := by
      rw [← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, hUU, Matrix.det_one]
    have hdD : (diagonal (fun i => (lam i : ℂ))).det ≠ 0 := by
      rw [← hD, Matrix.det_mul, Matrix.det_mul, mul_comm (Uᴴ.det), mul_assoc, h1, mul_one]
      exact hdet
    rw [Matrix.det_diagonal] at hdD
    intro i
    have := (Finset.prod_ne_zero_iff.mp hdD) i (Finset.mem_univ i)
    exact_mod_cast this

  have hext : ∀ (P : Fin p ⊕ Fin q → Prop) [DecidablePred P] (c : {i // P i} → ℂ) (d : Fin p ⊕ Fin q → ℂ),
      (∀ i, d i = if h : P i then c ⟨i, h⟩ else 0) →
      ∑ i, star (d i) * ((lam i : ℂ) * d i) = ∑ j : {i // P i}, star (c j) * ((lam j.1 : ℂ) * c j) := by
    intro P _ c d hd
    rw [← Fintype.sum_subtype_add_sum_subtype P (fun i => star (d i) * ((lam i : ℂ) * d i))]
    have h0 : ∑ i : {x // ¬ P x}, star (d i.1) * ((lam i.1 : ℂ) * d i.1) = 0 := by
      apply Finset.sum_eq_zero; intro i _; rw [hd, dif_neg i.2]; simp
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [hd, dif_pos i.2]
  have hEv : ∀ (P : Fin p ⊕ Fin q → Prop) [DecidablePred P] (c : {i // P i} → ℂ) (i : Fin p ⊕ Fin q),
      ((Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // P i}) => if i = j.1 then (1 : ℂ) else 0) *ᵥ c) i =
        if h : P i then c ⟨i, h⟩ else 0 := by
    intro P _ c i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i, h⟩]
      · simp
      · intro b _ hb; rw [if_neg]; intro e; exact hb (Subtype.ext e.symm)
      · simp
    · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; intro e; exact h (e ▸ b.2)
  have hcardP : Fintype.card {i // 0 < lam i} ≤ p := by
    by_contra hlt0
    have hlt := not_le.mp hlt0
    set E := Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // 0 < lam i}) => if i = j.1 then (1 : ℂ) else 0
    set L : ({i // 0 < lam i} → ℂ) →ₗ[ℂ] (Fin p → ℂ) := ψ₁ ∘ₗ Matrix.mulVecLin (U * E)
    have hne : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hlt)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hL : ψ₁ (U *ᵥ (E *ᵥ c)) = 0 := by
      have : L c = 0 := hc
      simpa [L, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using this
    have hle := h₁ _ hL
    rw [hform, hext _ c _ (hEv _ c)] at hle
    rw [Complex.re_sum] at hle
    simp only [star_mul_real] at hle
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra hall; exact hc0 (funext fun j => not_not.mp (fun h => hall ⟨j, h⟩))
    have hpos : 0 < ∑ j : {i // 0 < lam i}, lam j.1 * Complex.normSq (c j) := by
      apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun j : {i // 0 < lam i} => lam j.1 * Complex.normSq (c j))
        (fun j _ => mul_nonneg j.2.le (Complex.normSq_nonneg _)) (Finset.mem_univ j))
      exact mul_pos j.2 (Complex.normSq_pos.mpr hj)
    linarith
  have hcardN : Fintype.card {i // ¬ 0 < lam i} ≤ q := by
    by_contra hlt0
    have hlt := not_le.mp hlt0
    set E := Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // ¬ 0 < lam i}) => if i = j.1 then (1 : ℂ) else 0
    set L : ({i // ¬ 0 < lam i} → ℂ) →ₗ[ℂ] (Fin q → ℂ) := ψ₂ ∘ₗ Matrix.mulVecLin (U * E)
    have hne : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hlt)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hL : ψ₂ (U *ᵥ (E *ᵥ c)) = 0 := by
      have : L c = 0 := hc
      simpa [L, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using this
    have hle := h₂ _ hL
    rw [hform, hext _ c _ (hEv _ c)] at hle
    rw [Complex.re_sum] at hle
    simp only [star_mul_real] at hle
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra hall; exact hc0 (funext fun j => not_not.mp (fun h => hall ⟨j, h⟩))
    have hneg : ∀ j : {i // ¬ 0 < lam i}, lam j.1 < 0 := fun j => lt_of_le_of_ne (not_lt.mp j.2) (hlam0 j.1)
    have hpos : 0 < ∑ j : {i // ¬ 0 < lam i}, (-lam j.1) * Complex.normSq (c j) := by
      apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun j : {i // ¬ 0 < lam i} => (-lam j.1) * Complex.normSq (c j))
        (fun j _ => mul_nonneg (neg_nonneg.mpr (hneg j).le) (Complex.normSq_nonneg _)) (Finset.mem_univ j))
      exact mul_pos (neg_pos.mpr (hneg j)) (Complex.normSq_pos.mpr hj)
    have e : ∑ j : {i // ¬ 0 < lam i}, (-lam j.1) * Complex.normSq (c j) =
        -∑ j : {i // ¬ 0 < lam i}, lam j.1 * Complex.normSq (c j) := by
      rw [← Finset.sum_neg_distrib]; simp only [neg_mul]
    linarith
  have hsum : Fintype.card {i // 0 < lam i} + Fintype.card {i // ¬ 0 < lam i} = p + q := by
    rw [← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl fun i => 0 < lam i), Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  have hp : Fintype.card {i // 0 < lam i} = p := by omega
  have hq : Fintype.card {i // ¬ 0 < lam i} = q := by omega
  set e₁ := Fintype.equivFinOfCardEq hp
  set e₂ := Fintype.equivFinOfCardEq hq
  set e : Fin p ⊕ Fin q ≃ Fin p ⊕ Fin q := (Equiv.sumCongr e₁.symm e₂.symm).trans (Equiv.sumCompl fun i => 0 < lam i)
  have he1 : ∀ j, 0 < lam (e (Sum.inl j)) := by
    intro j; simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact (e₁.symm j).2
  have he2 : ∀ j, lam (e (Sum.inr j)) < 0 := by
    intro j; simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact lt_of_le_of_ne (not_lt.mp (e₂.symm j).2) (hlam0 _)
  set s : Fin p ⊕ Fin q → ℂ := fun i => (((Real.sqrt |lam i|)⁻¹ : ℝ) : ℂ)
  set A := U * diagonal s
  have hA : Aᴴ * G * A = diagonal (fun i => ((lam i / |lam i| : ℝ) : ℂ)) := by
    have : Aᴴ * G * A = (diagonal s)ᴴ * (Uᴴ * G * U) * diagonal s := by
      simp only [A, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have hab : 0 < |lam i| := abs_pos.mpr (hlam0 i)
    have hsq : Real.sqrt |lam i| * Real.sqrt |lam i| = |lam i| := Real.mul_self_sqrt hab.le
    have hsne : Real.sqrt |lam i| ≠ 0 := (Real.sqrt_pos.mpr hab).ne'
    simp only [s, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
    rw [Real.sq_sqrt hab.le]
    ring
  have hQ : (A.submatrix id e)ᴴ * G * A.submatrix id e = fromBlocks 1 0 0 (-1) := by
    have : (A.submatrix id e)ᴴ * G * A.submatrix id e = (Aᴴ * G * A).submatrix e e := by
      ext a b; rfl
    rw [this, hA, Matrix.submatrix_diagonal_equiv]
    have h1 : ∀ j, ((lam (e (Sum.inl j)) / |lam (e (Sum.inl j))| : ℝ) : ℂ) = 1 := by
      intro j; rw [abs_of_pos (he1 j), div_self (he1 j).ne']; simp
    have h2 : ∀ j, ((lam (e (Sum.inr j)) / |lam (e (Sum.inr j))| : ℝ) : ℂ) = -1 := by
      intro j; rw [abs_of_neg (he2 j), div_neg, div_self (he2 j).ne]; simp
    have hfe : (fun i => ((lam i / |lam i| : ℝ) : ℂ)) ∘ e = Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ)) := by
      funext x
      cases x with
      | inl j => exact h1 j
      | inr j => exact h2 j
    rw [hfe, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_one]
    congr 1
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨A.submatrix id e, ?_, hQ⟩
  have hdB : (fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one,
      Fintype.card_fin]
    exact pow_ne_zero _ (by norm_num)
  rw [← hQ, Matrix.det_mul, Matrix.det_mul] at hdB
  exact isUnit_iff_ne_zero.mpr (fun h => hdB (by rw [h, mul_zero]))
end Formalism.FourierDecayAlt.P.HermitianProjections
