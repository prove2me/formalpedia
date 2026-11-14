-- Prove2me | solution 1 for BosonicLearn.loewner_eigenvalue_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:55:03.993773+00:00
-- url     : https://prove2.me/submissions/2610a251-0fe3-4dac-9fb0-39393f8c0ef3

import Mathlib

open scoped Matrix ComplexOrder

noncomputable section

private lemma quad_form {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n : ℕ} (x : OrthonormalBasis (Fin n) ℂ E) (S : E →ₗ[ℂ] E) (a : Fin n → ℝ)
    (hS : ∀ i, S (x i) = (a i : ℂ) • x i) (v : E) :
    (inner ℂ v (S v)).re = ∑ i, a i * ‖inner ℂ (x i) v‖ ^ 2 := by
  have hv : S v = ∑ i, (inner ℂ (x i) v * (a i : ℂ)) • x i := by
    conv_lhs => rw [← x.sum_repr' v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hS, smul_smul]
  rw [hv, inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, mul_comm (inner ℂ (x i) v), mul_assoc, mul_comm (inner ℂ (x i) v),
    Complex.re_ofReal_mul, ← inner_conj_symm v (x i), Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.ofReal_re]

private lemma weyl_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {n : ℕ} (x y : OrthonormalBasis (Fin n) ℂ E) (S T : E →ₗ[ℂ] E) (a b : Fin n → ℝ)
    (hS : ∀ i, S (x i) = (a i : ℂ) • x i) (hT : ∀ i, T (y i) = (b i : ℂ) • y i)
    (ha : Monotone a) (hb : Monotone b)
    (hST : ∀ v, (inner ℂ v (S v)).re ≤ (inner ℂ v (T v)).re) (k : Fin n) : a k ≤ b k := by
  -- the linear conditions
  let f : E →ₗ[ℂ] ({i : Fin n // i ≠ k} → ℂ) :=
    LinearMap.pi fun i => if i.1 < k then innerₛₗ ℂ (x i.1) else innerₛₗ ℂ (y i.1)
  have hrank : Module.finrank ℂ ({i : Fin n // i ≠ k} → ℂ) < Module.finrank ℂ E := by
    rw [Module.finrank_pi, Module.finrank_eq_card_basis x.toBasis, Fintype.card_subtype_compl,
      Fintype.card_fin, Fintype.card_subtype_eq]
    have := k.pos
    omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := f) hrank
  obtain ⟨v, hvker, hv0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hvx : ∀ i, i < k → inner ℂ (x i) v = 0 := by
    intro i hi
    have := congrFun (LinearMap.mem_ker.mp hvker) ⟨i, hi.ne⟩
    simpa [f, hi] using this
  have hvy : ∀ i, k < i → inner ℂ (y i) v = 0 := by
    intro i hi
    have := congrFun (LinearMap.mem_ker.mp hvker) ⟨i, hi.ne'⟩
    simpa [f, not_lt.mpr hi.le] using this
  have h1 : a k * ‖v‖ ^ 2 ≤ (inner ℂ v (S v)).re := by
    rw [quad_form x S a hS, ← x.sum_sq_norm_inner_right v, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rcases lt_or_ge i k with hi | hi
    · rw [hvx i hi]; simp
    · exact mul_le_mul_of_nonneg_right (ha hi) (by positivity)
  have h2 : (inner ℂ v (T v)).re ≤ b k * ‖v‖ ^ 2 := by
    rw [quad_form y T b hT, ← y.sum_sq_norm_inner_right v, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rcases lt_or_ge k i with hi | hi
    · rw [hvy i hi]; simp
    · exact mul_le_mul_of_nonneg_right (hb hi) (by positivity)
  have h3 := (h1.trans (hST v)).trans h2
  have hpos : 0 < ‖v‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right h3 hpos

private lemma form_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (h : (B - A).PosSemidef)
    (v : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ v (Matrix.toEuclideanLin A v)).re ≤ (inner ℂ v (Matrix.toEuclideanLin B v)).re := by
  have h1 := (Matrix.isPositive_toEuclideanLin_iff.mpr h).2 v
  rw [map_sub, LinearMap.sub_apply, inner_sub_left, map_sub, inner_re_symm,
    inner_re_symm (Matrix.toEuclideanLin A v)] at h1
  exact sub_nonneg.mp h1

private lemma sorted_data {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    ∃ (l : Fin n → ℝ) (x : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))),
      Monotone l ∧ (∀ i, Matrix.toEuclideanLin A (x i) = (l i : ℂ) • x i) ∧
      (∀ t : ℝ, (1 + ((t : ℝ) : ℂ) • A).det = ∏ i, ((1 + t * l i : ℝ) : ℂ)) ∧
      A.trace = ((∑ i, l i : ℝ) : ℂ) ∧ (A * A).trace = ((∑ i, l i ^ 2 : ℝ) : ℂ) := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin n) (Fin n) ℂ,
      U = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hU1 : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hUdef]
    exact Unitary.coe_star_mul_self _
  have hU2 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hUdef]
    exact Unitary.coe_mul_star_self _
  have hspec : A = U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact h
  set d := hA.eigenvalues with hd
  set σ : Equiv.Perm (Fin n) := Tuple.sort d with hσ
  refine ⟨d ∘ σ, hA.eigenvectorBasis.reindex σ.symm, Tuple.monotone_sort d, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm, Matrix.toLpLin_apply,
      hA.mulVec_eigenvectorBasis]
    rfl
  · intro t
    have h1 : 1 + ((t : ℝ) : ℂ) • A
        = U * Matrix.diagonal (fun i => ((1 + t * d i : ℝ) : ℂ)) * Uᴴ := by
      have : Matrix.diagonal (fun i => ((1 + t * d i : ℝ) : ℂ))
          = 1 + (t : ℂ) • Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
      rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU2, Matrix.mul_smul,
        Matrix.smul_mul, ← hspec]
    rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_right_comm,
      ← Matrix.det_mul, hU2, Matrix.det_one, one_mul]
    exact (Equiv.prod_comp σ (fun i => ((1 + t * d i : ℝ) : ℂ))).symm
  · rw [hA.trace_eq_sum_eigenvalues, Complex.ofReal_sum]
    exact (Equiv.sum_comp σ (fun i => ((d i : ℝ) : ℂ))).symm
  · have h2 : A * A = U * Matrix.diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ)) * Uᴴ := by
      have : Matrix.diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ))
          = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        ext i
        push_cast
        ring
      conv_lhs => rw [hspec]
      rw [this]
      calc U * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * Uᴴ
            * (U * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * Uᴴ)
          = U * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * (Uᴴ * U)
            * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * Uᴴ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU1, Matrix.mul_one, Matrix.mul_assoc U]
    rw [h2, Matrix.trace_mul_cycle, hU1, Matrix.one_mul, Matrix.trace_diagonal, Complex.ofReal_sum]
    exact (Equiv.sum_comp σ (fun i => ((d i ^ 2 : ℝ) : ℂ))).symm

theorem solution {n : ℕ} (Bm Bp : Matrix (Fin n) (Fin n) ℂ) (hm : Bm.PosSemidef)
    (hd : (Bp - Bm).PosSemidef) (Λ : ℝ)
    (hΛ : (((Λ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Bp).PosSemidef) :
    ∃ lp lm : Fin n → ℝ, (∀ i, 0 ≤ lm i) ∧ (∀ i, lm i ≤ lp i) ∧ (∀ i, lp i ≤ Λ) ∧
      (∀ t : ℝ, (1 + ((t : ℝ) : ℂ) • Bp).det = ∏ i, ((1 + t * lp i : ℝ) : ℂ)) ∧
      (∀ t : ℝ, (1 + ((t : ℝ) : ℂ) • Bm).det = ∏ i, ((1 + t * lm i : ℝ) : ℂ)) ∧
      Bp.trace = ((∑ i, lp i : ℝ) : ℂ) ∧ Bm.trace = ((∑ i, lm i : ℝ) : ℂ) ∧
      (Bm * Bm).trace = ((∑ i, lm i ^ 2 : ℝ) : ℂ) := by
  have hp : Bp.IsHermitian := by
    have h := hd.1.add hm.1
    rwa [sub_add_cancel] at h
  obtain ⟨lm, x, hlm_mono, hx, hdetm, htrm, htrm2⟩ := sorted_data Bm hm.1
  obtain ⟨lp, y, hlp_mono, hy, hdetp, htrp, -⟩ := sorted_data Bp hp
  refine ⟨lp, lm, ?_, ?_, ?_, hdetp, hdetm, htrp, htrm, htrm2⟩
  · intro i
    have h := form_le 0 Bm (by rw [sub_zero]; exact hm) (x i)
    rw [hx, map_zero, LinearMap.zero_apply, inner_zero_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, x.orthonormal.1 i] at h
    simpa using h
  · exact weyl_core x y _ _ lm lp hx hy hlm_mono hlp_mono (form_le Bm Bp hd)
  · intro i
    have h := form_le Bp (((Λ : ℝ) : ℂ) • 1) hΛ (y i)
    rw [hy, map_smul, LinearMap.smul_apply, Matrix.toLpLin_one, LinearMap.id_apply,
      inner_smul_right, inner_smul_right, inner_self_eq_norm_sq_to_K, y.orthonormal.1 i] at h
    simpa using h
