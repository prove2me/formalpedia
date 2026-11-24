-- Prove2me | solution 1 for DepthOneQExp.lemma_2_12
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T06:16:08.760837+00:00
-- url     : https://prove2.me/submissions/0371544f-c14a-4642-a42e-4d431da20ec0

import Mathlib
import Definitions.Def_DepthOneQExp_blockElem
import Definitions.Def_DepthOneQExp_sigma
import Definitions.Def_ConstGapCircuits_spectralGap

open DepthOneQExp Matrix

namespace DepthOneQExp.BlockAux

variable {s : ℕ}

/-- the off-diagonal block `r` in block position `(a, b)` -/
def Nb (s : ℕ) (a b : Fin 3) (r : Matrix (Fin s) (Fin s) (ZMod 2)) :
    Matrix (Fin 3 × Fin s) (Fin 3 × Fin s) (ZMod 2) :=
  Matrix.of fun p q => if p.1 = a ∧ q.1 = b then r p.2 q.2 else 0

theorem Nb_mul_Nb (a b c d : Fin 3) (r t : Matrix (Fin s) (Fin s) (ZMod 2)) :
    Nb s a b r * Nb s c d t = if b = c then Nb s a d (r * t) else 0 := by
  ext p q
  simp only [Nb, mul_apply, of_apply]
  split_ifs with hbc
  · subst hbc
    simp only [of_apply, Matrix.mul_apply]
    by_cases hpa : p.1 = a <;> by_cases hqd : q.1 = d
    · simp only [hpa, hqd, true_and, and_true]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hc; simp [hc]
      · simp
    all_goals simp [hpa, hqd]
  · simp only [Matrix.zero_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h1 : x.1 = b
    · have : ¬ (x.1 = c) := fun h => hbc (h1.symm.trans h)
      simp [this]
    · simp [h1]

theorem Nb_add_self (a b : Fin 3) (r : Matrix (Fin s) (Fin s) (ZMod 2)) : Nb s a b r + Nb s a b r = 0 := by
  ext p q
  simp only [Matrix.add_apply, Matrix.zero_apply]
  generalize Nb s a b r p q = c
  revert c; decide

theorem blockElem_eq (a b : Fin 3) (r : Matrix (Fin s) (Fin s) (ZMod 2)) :
    blockElem s a b r = reindex finProdFinEquiv finProdFinEquiv (1 + Nb s a b r) := rfl

/-- the relation `x y x y z = 1` of Lemma 2.12 with `x = E₁₂(I)`, `y = E₂₃(I)`, `z = E₁₃(I)` -/
theorem rel_xyxyz :
    blockElem s 0 1 1 * blockElem s 1 2 1 * blockElem s 0 1 1 * blockElem s 1 2 1 * blockElem s 0 2 1 = 1 := by
  simp only [blockElem_eq, reindex_apply, submatrix_mul_equiv, ← submatrix_one_equiv finProdFinEquiv.symm]
  congr 1
  set N1 := Nb s 0 1 1
  set N2 := Nb s 1 2 1
  set N3 := Nb s 0 2 1
  have h11 : N1 * N1 = 0 := by rw [Nb_mul_Nb, if_neg (by decide)]
  have h12 : N1 * N2 = N3 := by rw [Nb_mul_Nb, if_pos rfl, mul_one]
  have h21 : N2 * N1 = 0 := by rw [Nb_mul_Nb, if_neg (by decide)]
  have h22 : N2 * N2 = 0 := by rw [Nb_mul_Nb, if_neg (by decide)]
  have h31 : N3 * N1 = 0 := by rw [Nb_mul_Nb, if_neg (by decide)]
  have h32 : N3 * N2 = 0 := by rw [Nb_mul_Nb, if_neg (by decide)]
  have h33 : N3 * N3 = 0 := by rw [Nb_mul_Nb, if_neg (by decide)]
  have a1 : N1 + N1 = 0 := Nb_add_self _ _ _
  have a2 : N2 + N2 = 0 := Nb_add_self _ _ _
  have a3 : N3 + N3 = 0 := Nb_add_self _ _ _
  have s1 : (1 + N1) * (1 + N2) = 1 + N1 + N2 + N3 := by
    rw [mul_add, add_mul, add_mul, one_mul, one_mul, mul_one, h12]; abel
  have s2 : (1 + N1 + N2 + N3) * (1 + N1) = 1 + N2 + N3 := by
    calc (1 + N1 + N2 + N3) * (1 + N1) = 1 + N2 + N3 + (N1 + N1) := by
          simp only [mul_add, add_mul, one_mul, mul_one, h11, h21, h31]; abel
      _ = 1 + N2 + N3 := by rw [a1, add_zero]
  have s3 : (1 + N2 + N3) * (1 + N2) = 1 + N3 := by
    calc (1 + N2 + N3) * (1 + N2) = 1 + N3 + (N2 + N2) := by
          simp only [mul_add, add_mul, one_mul, mul_one, h22, h32]; abel
      _ = 1 + N3 := by rw [a2, add_zero]
  have s4 : (1 + N3) * (1 + N3) = 1 := by
    calc (1 + N3) * (1 + N3) = 1 + (N3 + N3) := by
          simp only [mul_add, add_mul, one_mul, mul_one, h33]; abel
      _ = 1 := by rw [a3, add_zero]
  rw [s1, s2, s3, s4]

end DepthOneQExp.BlockAux

open scoped InnerProductSpace

namespace DepthOneQExp.L212Aux

theorem unitary_isometry {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (hM : M ∈ unitaryGroup (Fin d) ℂ)
    (w : EuclideanSpace ℂ (Fin d)) : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M w‖ = ‖w‖ := by
  have h : ⟪Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M w, Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M w⟫_ℂ =
      ⟪w, w⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
      ← ContinuousLinearMap.mul_apply, ← map_mul, (mem_unitaryGroup_iff'.1 hM), map_one,
      ContinuousLinearMap.one_apply]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M w‖ ^ 2 = ‖w‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

set_option maxHeartbeats 1000000 in
theorem lemma_2_12' (s : ℕ)
    (ρ : ConstGapCircuits.UnitaryRep (Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)))
    (v : EuclideanSpace ℂ (Fin ρ.dim)) :
    (-1 + 1 / 63 : ℝ) * ‖v‖ ^ 2 ≤
      RCLike.re ⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((1 / 14 : ℂ) • ∑ i : Fin 14, (ρ.hom (sigma s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)) v⟫_ℂ := by
  set U : Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) →
      (EuclideanSpace ℂ (Fin ρ.dim) →L[ℂ] EuclideanSpace ℂ (Fin ρ.dim)) :=
    fun g => Matrix.toEuclideanCLM (n := Fin ρ.dim) (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)
    with hU
  have hUmul : ∀ g h w, U (g * h) w = U g (U h w) := by
    intro g h w
    simp only [hU, map_mul]
    rw [Submonoid.coe_mul, map_mul]; rfl
  have hUone : ∀ w, U 1 w = w := by
    intro w; simp [hU]
  have hUiso : ∀ g w, ‖U g w‖ = ‖w‖ := fun g w => unitary_isometry _ (ρ.hom g).2 w
  set a : Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) → ℝ := fun g => ‖U g v + v‖ with ha
  have ha2 : ∀ g, a g ^ 2 = 2 * ‖v‖ ^ 2 + 2 * RCLike.re ⟪v, U g v⟫_ℂ := by
    intro g
    simp only [ha]
    rw [@norm_add_sq ℂ, hUiso, ← inner_re_symm (𝕜 := ℂ)]
    ring
  -- the relation
  set x := sigma s 0
  set y := sigma s 3
  set z := sigma s 1
  have hrel : x * y * x * y * z = 1 := by
    apply Subtype.ext
    exact DepthOneQExp.BlockAux.rel_xyxyz
  have htel : (2 : ℂ) • v = U (x * y * x * y) (U z v + v) - U (x * y * x) (U y v + v) +
      U (x * y) (U x v + v) - U x (U y v + v) + (U x v + v) := by
    have e1 : U (x * y * x * y) (U z v) = v := by rw [← hUmul, hrel, hUone]
    have e2 : U (x * y * x) (U y v) = U (x * y * x * y) v := by rw [← hUmul]
    have e3 : U (x * y) (U x v) = U (x * y * x) v := by rw [← hUmul]
    have e4 : U x (U y v) = U (x * y) v := by rw [← hUmul]
    simp only [map_add, e1, e2, e3, e4]
    rw [two_smul]; abel
  have hnorm : 2 * ‖v‖ ≤ 2 * a x + 2 * a y + a z := by
    have := congrArg norm htel
    rw [norm_smul] at this
    simp only [Complex.norm_ofNat] at this
    rw [this]
    calc _ ≤ ‖U (x * y * x * y) (U z v + v)‖ + ‖U (x * y * x) (U y v + v)‖ +
          ‖U (x * y) (U x v + v)‖ + ‖U x (U y v + v)‖ + ‖U x v + v‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ = 2 * a x + 2 * a y + a z := by simp only [hUiso, ha]; ring
  -- sum over all generators
  have hsum : RCLike.re ⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((1 / 14 : ℂ) • ∑ i : Fin 14, (ρ.hom (sigma s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)) v⟫_ℂ =
      (1 / 14) * ∑ i : Fin 14, RCLike.re ⟪v, U (sigma s i) v⟫_ℂ := by
    rw [map_smul, map_sum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      inner_smul_right, inner_sum]
    rw [show (1 / 14 : ℂ) = ((1 / 14 : ℝ) : ℂ) by norm_num, RCLike.re_to_complex, Complex.re_ofReal_mul,
      Complex.re_sum]
    rfl
  have hsq : ∑ i : Fin 14, a (sigma s i) ^ 2 = 28 * ‖v‖ ^ 2 + 2 * ∑ i : Fin 14, RCLike.re ⟪v, U (sigma s i) v⟫_ℂ := by
    simp only [ha2, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hthree : a x ^ 2 + a y ^ 2 + a z ^ 2 ≤ ∑ i : Fin 14, a (sigma s i) ^ 2 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({0, 1, 3} : Finset (Fin 14)))
      (fun i _ _ => sq_nonneg (a (sigma s i)))
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h
    have : a x ^ 2 + a y ^ 2 + a z ^ 2 = a (sigma s 0) ^ 2 + (a (sigma s 1) ^ 2 + a (sigma s 3) ^ 2) := by
      simp only [x, y, z]; ring
    rw [this]; exact h
  have hcs : (2 * a x + 2 * a y + a z) ^ 2 ≤ 9 * (a x ^ 2 + a y ^ 2 + a z ^ 2) := by
    nlinarith [sq_nonneg (a x - a y), sq_nonneg (a x - 2 * a z), sq_nonneg (a y - 2 * a z)]
  clear htel hrel hUmul hUone
  have hv0 : 0 ≤ 2 * ‖v‖ := mul_nonneg (by norm_num) (norm_nonneg v)
  have h4 : (2 * ‖v‖) ^ 2 ≤ (2 * a x + 2 * a y + a z) ^ 2 := pow_le_pow_left₀ hv0 hnorm 2
  rw [hsum]
  have h5 : (2 * ‖v‖) ^ 2 = 4 * ‖v‖ ^ 2 := by ring
  generalize ∑ i : Fin 14, RCLike.re ⟪v, U (sigma s i) v⟫_ℂ = S at hsq ⊢
  generalize ∑ i : Fin 14, a (sigma s i) ^ 2 = T at hsq hthree
  generalize ‖v‖ ^ 2 = N at h5 hsq ⊢
  linarith only [h4, h5, hcs, hthree, hsq]

end DepthOneQExp.L212Aux


open DepthOneQExp.L212Aux in
theorem solution (s : ℕ) (hs : 1 ≤ s)
    (ρ : ConstGapCircuits.UnitaryRep (Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)))
    (v : EuclideanSpace ℂ (Fin ρ.dim)) :
    (-1 + 1 / 63 : ℝ) * ‖v‖ ^ 2 ≤
      RCLike.re ⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((1 / 14 : ℂ) • ∑ i : Fin 14, (ρ.hom (sigma s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)) v⟫_ℂ :=
  lemma_2_12' s ρ v
