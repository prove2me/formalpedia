-- Prove2me | solution 1 for ConleyZehnder.complexLinearDet_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T15:55:12.212654+00:00
-- url     : https://prove2.me/submissions/d9b44f7b-d342-4b61-9a7e-c84162f86023

import Definitions.Def_ConleyZehnder_Setting

open ConleyZehnder Matrix

theorem solution {n : ℕ} (A : Mat n) (hA : IsSymplectic A) :
    complexLinearDet A ≠ 0 := by
  classical
  set J := J₀ n with hJdef
  have hJJ : J * J = -1 := Matrix.J_squared (Fin n) ℝ
  have hJt : Jᵀ = -J := Matrix.J_transpose (Fin n) ℝ
  have hAt : Aᵀ * J * A = J := (SymplecticGroup.mem_iff').1 hA
  -- injectivity of `A - J A J` on real vectors
  have hker : ∀ v : Fin n ⊕ Fin n → ℝ, (A - J * A * J) *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h1 : A *ᵥ v = (J * A * J) *ᵥ v := by
      rw [Matrix.sub_mulVec] at hv; exact sub_eq_zero.1 hv
    set w := A *ᵥ v with hw
    have hm : J * (J * A * J) = -(A * J) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ]; simp
    have hJw : J *ᵥ w = -(A *ᵥ (J *ᵥ v)) := by
      rw [h1, Matrix.mulVec_mulVec, hm, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
    have h2 : A *ᵥ (J *ᵥ v) = -(J *ᵥ w) := by rw [hJw, neg_neg]
    have h3 : v ⬝ᵥ ((Aᵀ * J * A) *ᵥ (J *ᵥ v)) = w ⬝ᵥ w := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose, ← hw, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hJJ]
      simp [Matrix.neg_mulVec]
    have h4 : v ⬝ᵥ ((Aᵀ * J * A) *ᵥ (J *ᵥ v)) = -(v ⬝ᵥ v) := by
      rw [hAt, Matrix.mulVec_mulVec, hJJ]
      simp [Matrix.neg_mulVec]
    have h5 : w ⬝ᵥ w + v ⬝ᵥ v = 0 := by linarith
    have hw0 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
    have hv0 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    exact dotProduct_self_eq_zero.1 (by linarith)
  -- block structure of `C_A`
  set C := complexLinearPart A with hCdef
  have hC : C = (1 / 2 : ℝ) • (A - J * A * J) := rfl
  have hC12 : ∀ i j, C (Sum.inl i) (Sum.inr j) = - C (Sum.inr i) (Sum.inl j) := by
    intro i j
    simp [hC, hJdef, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    ring
  have hC22 : ∀ i j, C (Sum.inr i) (Sum.inr j) = C (Sum.inl i) (Sum.inl j) := by
    intro i j
    simp [hC, hJdef, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    ring
  intro hdet
  obtain ⟨z, hz0, hz⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  set v : Fin n ⊕ Fin n → ℝ := Sum.elim (fun j => (z j).re) (fun j => (z j).im) with hv
  have hCv : C *ᵥ v = 0 := by
    funext k
    rcases k with i | i
    · have := congrArg Complex.re (congrFun hz i)
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Complex.re_sum, Complex.zero_re] at this
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hv, Sum.elim_inl,
        Sum.elim_inr, Pi.zero_apply, hC12]
      rw [← Finset.sum_add_distrib]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) this
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Complex.mul_re]
      ring
    · have := congrArg Complex.im (congrFun hz i)
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Complex.im_sum, Complex.zero_im] at this
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hv, Sum.elim_inl,
        Sum.elim_inr, Pi.zero_apply, hC22]
      rw [← Finset.sum_add_distrib]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) this
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Complex.mul_im]
      ring
  have hv0 : v = 0 := by
    apply hker
    have : (A - J * A * J) = (2 : ℝ) • C := by
      rw [hC, smul_smul]; norm_num
    rw [this, Matrix.smul_mulVec, hCv, smul_zero]
  apply hz0
  funext j
  have hre := congrFun hv0 (Sum.inl j)
  have him := congrFun hv0 (Sum.inr j)
  simp [hv] at hre him
  exact Complex.ext hre him
