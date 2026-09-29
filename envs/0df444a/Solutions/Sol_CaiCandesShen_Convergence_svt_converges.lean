-- Prove2me | solution 1 for CaiCandesShen.Convergence.svt_converges
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:29:58.13264+00:00
-- url     : https://prove2.me/submissions/8f5f2084-3fd8-4cfd-80cf-c890207acc42

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Iterations
open Filter Topology

namespace CaiCandesShen.Convergence

open Matrix

section aux

variable {n₁ n₂ : ℕ}

lemma aux_svt_fi_comm (A B : Mat n₁ n₂) : frobInner A B = frobInner B A := by
  unfold frobInner; simp [mul_comm]

lemma aux_svt_fi_add_left (A B C : Mat n₁ n₂) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  unfold frobInner; simp [add_mul, Finset.sum_add_distrib]

lemma aux_svt_fi_sub_left (A B C : Mat n₁ n₂) :
    frobInner (A - B) C = frobInner A C - frobInner B C := by
  unfold frobInner; simp [sub_mul, Finset.sum_sub_distrib]

lemma aux_svt_fi_smul_left (c : ℝ) (A B : Mat n₁ n₂) :
    frobInner (c • A) B = c * frobInner A B := by
  unfold frobInner; simp [Finset.mul_sum, mul_assoc]

lemma aux_svt_fi_add_right (A B C : Mat n₁ n₂) :
    frobInner A (B + C) = frobInner A B + frobInner A C := by
  rw [aux_svt_fi_comm, aux_svt_fi_add_left, aux_svt_fi_comm B, aux_svt_fi_comm C]

lemma aux_svt_fi_sub_right (A B C : Mat n₁ n₂) :
    frobInner A (B - C) = frobInner A B - frobInner A C := by
  rw [aux_svt_fi_comm, aux_svt_fi_sub_left, aux_svt_fi_comm B, aux_svt_fi_comm C]

lemma aux_svt_fi_smul_right (c : ℝ) (A B : Mat n₁ n₂) :
    frobInner A (c • B) = c * frobInner A B := by
  rw [aux_svt_fi_comm, aux_svt_fi_smul_left, aux_svt_fi_comm]

lemma aux_svt_fi_zero_right (A : Mat n₁ n₂) : frobInner A 0 = 0 := by
  unfold frobInner; simp

lemma aux_svt_fi_self_nonneg (A : Mat n₁ n₂) : 0 ≤ frobInner A A :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_self_nonneg _))

lemma aux_svt_frobNorm_sq (A : Mat n₁ n₂) : frobNorm A ^ 2 = frobInner A A :=
  Real.sq_sqrt (aux_svt_fi_self_nonneg A)

lemma aux_svt_fi_trace (A B : Mat n₁ n₂) : frobInner A B = trace (Aᵀ * B) := by
  unfold frobInner
  simp only [trace, diag, mul_apply, transpose_apply]
  rw [Finset.sum_comm]

lemma aux_svt_entry_sq_le (A : Mat n₁ n₂) (i : Fin n₁) (j : Fin n₂) :
    A i j * A i j ≤ frobInner A A := by
  unfold frobInner
  calc A i j * A i j ≤ ∑ j', A i j' * A i j' :=
        Finset.single_le_sum (f := fun j' => A i j' * A i j') (fun _ _ => mul_self_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', A i' j' * A i' j' :=
        Finset.single_le_sum (f := fun i' => ∑ j', A i' j' * A i' j')
          (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)) (Finset.mem_univ i)

lemma aux_svt_fi_self_eq_zero {A : Mat n₁ n₂} (h : frobInner A A = 0) : A = 0 := by
  ext i j
  have h1 := aux_svt_entry_sq_le A i j
  have : A i j * A i j = 0 := le_antisymm (h ▸ h1) (mul_self_nonneg _)
  simpa using this

/-- operator-norm bound `‖G v‖ ≤ c ‖v‖`. -/
def aux_svt_opLe (c : ℝ) (G : Mat n₁ n₂) : Prop :=
  ∀ v : Fin n₂ → ℝ, (G *ᵥ v) ⬝ᵥ (G *ᵥ v) ≤ c ^ 2 * (v ⬝ᵥ v)

lemma aux_svt_dot_mulVec {m : ℕ} (A : Matrix (Fin n₁) (Fin m) ℝ) (x y : Fin m → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = ((Aᵀ * A) *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]

lemma aux_svt_iso {m : ℕ} {U : Matrix (Fin n₁) (Fin m) ℝ} (hU : Uᵀ * U = 1) (x y : Fin m → ℝ) :
    (U *ᵥ x) ⬝ᵥ (U *ᵥ y) = x ⬝ᵥ y := by
  rw [aux_svt_dot_mulVec, hU, Matrix.one_mulVec]

lemma aux_svt_dot_sub_self {m : ℕ} (u w : Fin m → ℝ) :
    (u - w) ⬝ᵥ (u - w) = u ⬝ᵥ u - 2 * (u ⬝ᵥ w) + w ⬝ᵥ w := by
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm w u]; ring

lemma aux_svt_dot_self_nonneg {m : ℕ} (u : Fin m → ℝ) : 0 ≤ u ⬝ᵥ u :=
  Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

lemma aux_svt_L3 {r : ℕ} {U : Matrix (Fin n₁) (Fin r) ℝ} {V : Matrix (Fin n₂) (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {c : ℝ} {g : Fin r → ℝ}
    (hg : ∀ i, 0 ≤ g i ∧ g i ≤ c) : aux_svt_opLe c (U * diagonal g * Vᵀ) := by
  intro v
  set w := Vᵀ *ᵥ v with hw
  have e1 : (U * diagonal g * Vᵀ) *ᵥ v = U *ᵥ (diagonal g *ᵥ w) := by
    simp [hw, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e1, aux_svt_iso hU]
  have e2 : (diagonal g *ᵥ w) ⬝ᵥ (diagonal g *ᵥ w) ≤ c ^ 2 * (w ⬝ᵥ w) := by
    simp only [Matrix.mulVec_diagonal, dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    obtain ⟨h0, h1⟩ := hg i
    have : g i * g i ≤ c ^ 2 := by nlinarith
    nlinarith [mul_self_nonneg (w i)]
  have e3 : w ⬝ᵥ w ≤ v ⬝ᵥ v := by
    have h0 := aux_svt_dot_self_nonneg (v - V *ᵥ w)
    rw [aux_svt_dot_sub_self, aux_svt_iso hV] at h0
    have : v ⬝ᵥ (V *ᵥ w) = w ⬝ᵥ w := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    linarith
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  nlinarith

lemma aux_svt_L4 {r : ℕ} {U : Matrix (Fin n₁) (Fin r) ℝ} {V : Matrix (Fin n₂) (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {G : Mat n₁ n₂} (hG : aux_svt_opLe 1 G)
    {d : Fin r → ℝ} (hd : ∀ i, 0 ≤ d i) :
    frobInner G (U * diagonal d * Vᵀ) ≤ ∑ k, d k := by
  have expand : frobInner G (U * diagonal d * Vᵀ) =
      ∑ k, d k * ((fun i => U i k) ⬝ᵥ (G *ᵥ fun j => V j k)) := by
    unfold frobInner
    simp only [mul_apply, diagonal_apply, transpose_apply, dotProduct, mulVec, Finset.mul_sum,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    ring
  rw [expand]
  apply Finset.sum_le_sum
  intro k _
  have hu : (fun i => U i k) ⬝ᵥ (fun i => U i k) = 1 := by
    have := congrFun (congrFun hU k) k
    simpa [mul_apply, dotProduct] using this
  have hv : (fun j => V j k) ⬝ᵥ (fun j => V j k) = 1 := by
    have := congrFun (congrFun hV k) k
    simpa [mul_apply, dotProduct] using this
  have hw := hG (fun j => V j k)
  rw [hv] at hw
  have h0 := aux_svt_dot_self_nonneg ((fun i => U i k) - (G *ᵥ fun j => V j k))
  rw [aux_svt_dot_sub_self, hu] at h0
  have : (fun i => U i k) ⬝ᵥ (G *ᵥ fun j => V j k) ≤ 1 := by nlinarith
  nlinarith [hd k]

lemma aux_svt_trace_diag {r : ℕ} {U : Matrix (Fin n₁) (Fin r) ℝ} {V : Matrix (Fin n₂) (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (a b : Fin r → ℝ) :
    frobInner (U * diagonal a * Vᵀ) (U * diagonal b * Vᵀ) = ∑ i, a i * b i := by
  rw [aux_svt_fi_trace]
  have : (U * diagonal a * Vᵀ)ᵀ * (U * diagonal b * Vᵀ) = V * (diagonal a * diagonal b * Vᵀ) := by
    simp only [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, hV, Matrix.mul_one, diagonal_mul_diagonal,
    trace_diagonal]

end aux

section eucl

variable {n₁ n₂ : ℕ}

lemma aux_svt_norm_sq_eq {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ 2 = WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

lemma aux_svt_toE_apply (A : Mat n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    WithLp.ofLp (toEuclideanLin A x) = A *ᵥ WithLp.ofLp x := rfl

lemma aux_svt_opLe_iff (c : ℝ) (hc : 0 ≤ c) (G : Mat n₁ n₂) :
    aux_svt_opLe c G ↔ ∀ x : EuclideanSpace ℝ (Fin n₂), ‖toEuclideanLin G x‖ ≤ c * ‖x‖ := by
  constructor
  · intro h x
    have h1 := h (WithLp.ofLp x)
    rw [← aux_svt_toE_apply, ← aux_svt_norm_sq_eq, ← aux_svt_norm_sq_eq] at h1
    have : ‖toEuclideanLin G x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by rw [mul_pow]; exact h1
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp this
  · intro h v
    have h1 := h (WithLp.toLp 2 v)
    have h2 : ‖toEuclideanLin G (WithLp.toLp 2 v)‖ ^ 2 ≤ (c * ‖WithLp.toLp 2 v‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, aux_svt_norm_sq_eq, aux_svt_norm_sq_eq, aux_svt_toE_apply] at h2
    simpa using h2

lemma aux_svt_K {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ (Fin n₂)))
    (A B : Mat n₁ n₂) :
    frobInner A B = ∑ i, inner ℝ (toEuclideanLin A (b i)) (toEuclideanLin B (b i)) := by
  have hrow : ∀ (C : Mat n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) (k : Fin n₁),
      (C *ᵥ WithLp.ofLp x) k = inner ℝ (WithLp.toLp 2 (C k)) x := by
    intro C x k
    rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [mulVec, dotProduct_comm]
  have hin : ∀ x : EuclideanSpace ℝ (Fin n₂), inner ℝ (toEuclideanLin A x) (toEuclideanLin B x)
      = ∑ k, inner ℝ (WithLp.toLp 2 (A k)) x * inner ℝ x (WithLp.toLp 2 (B k)) := by
    intro x
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [aux_svt_toE_apply, star_trivial, dotProduct]
    apply Finset.sum_congr rfl; intro k _
    rw [hrow, hrow, real_inner_comm x]; ring
  simp_rw [hin]
  rw [Finset.sum_comm]
  unfold frobInner
  apply Finset.sum_congr rfl; intro k _
  rw [b.sum_inner_mul_inner, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

lemma aux_svt_nuc_eq (Z : Mat n₁ n₂) :
    nuclearNorm Z = ∑ i : Fin n₂, ‖toEuclideanLin Z
      ((toEuclideanLin Z).isSymmetric_adjoint_comp_self.eigenvectorBasis
        finrank_euclideanSpace_fin i)‖ := by
  set T := toEuclideanLin Z
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n₂)) = n₂ := finrank_euclideanSpace_fin
  have hsub : T.singularValues.support ⊆ Finset.range n₂ := by
    intro i hi
    rw [Finset.mem_range]
    by_contra h
    push Not at h
    rw [Finsupp.mem_support_iff, T.singularValues_of_finrank_le (by rw [hn]; exact h)] at hi
    exact hi rfl
  unfold nuclearNorm
  rw [Finsupp.sum_of_support_subset _ hsub _ (fun _ _ => rfl), Finset.sum_range]
  apply Finset.sum_congr rfl; intro i _
  rw [T.singularValues_fin hn i]
  set hT := T.isSymmetric_adjoint_comp_self
  set b := hT.eigenvectorBasis hn
  have h1 : ‖T (b i)‖ ^ 2 = hT.eigenvalues hn i := by
    rw [← real_inner_self_eq_norm_sq, ← LinearMap.adjoint_inner_left]
    have := hT.apply_eigenvectorBasis hn i
    simp only [LinearMap.comp_apply] at this
    rw [this, real_inner_smul_left, real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    simp
  rw [← h1, Real.sqrt_sq (norm_nonneg _)]

lemma aux_svt_L1 {c : ℝ} (hc : 0 ≤ c) {G : Mat n₁ n₂} (hG : aux_svt_opLe c G) (Z : Mat n₁ n₂) :
    frobInner G Z ≤ c * nuclearNorm Z := by
  rw [aux_svt_opLe_iff c hc] at hG
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n₂)) = n₂ := finrank_euclideanSpace_fin
  set b := (toEuclideanLin Z).isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  rw [aux_svt_K b, aux_svt_nuc_eq, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  calc _ ≤ ‖toEuclideanLin G (b i)‖ * ‖toEuclideanLin Z (b i)‖ := real_inner_le_norm _ _
    _ ≤ c * ‖toEuclideanLin Z (b i)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have := hG (b i); rwa [b.orthonormal.1 i, mul_one] at this

lemma aux_svt_L2 (Z : Mat n₁ n₂) :
    ∃ G : Mat n₁ n₂, aux_svt_opLe 1 G ∧ nuclearNorm Z ≤ frobInner G Z := by
  set T := toEuclideanLin Z with hTdef
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n₂)) = n₂ := finrank_euclideanSpace_fin
  set hT := T.isSymmetric_adjoint_comp_self
  set b := hT.eigenvectorBasis hn
  set p : Fin n₂ → EuclideanSpace ℝ (Fin n₁) := fun i => ‖T (b i)‖⁻¹ • T (b i) with hp
  set G' := b.toBasis.constr ℝ p
  have hG'b : ∀ i, G' (b i) = p i := by
    intro i
    have := b.toBasis.constr_basis ℝ p i
    rwa [OrthonormalBasis.coe_toBasis] at this
  have horth : ∀ i j, i ≠ j → inner ℝ (T (b i)) (T (b j)) = 0 := by
    intro i j hij
    rw [← LinearMap.adjoint_inner_left]
    have := hT.apply_eigenvectorBasis hn i
    simp only [LinearMap.comp_apply] at this
    rw [this, real_inner_smul_left, b.orthonormal.2 hij, mul_zero]
  have hp_orth : ∀ i j, i ≠ j → inner ℝ (p i) (p j) = 0 := by
    intro i j hij
    simp only [hp, real_inner_smul_left, real_inner_smul_right, horth i j hij, mul_zero]
  have hp_norm : ∀ i, inner ℝ (p i) (p i) ≤ 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq]
    simp only [hp, norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖T (b i)‖ 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ h]; norm_num
  refine ⟨toEuclideanLin.symm G', ?_, ?_⟩
  · rw [aux_svt_opLe_iff 1 zero_le_one]
    intro x
    rw [LinearEquiv.apply_symm_apply, one_mul]
    have hx : G' x = ∑ i, inner ℝ (b i) x • p i := by
      conv_lhs => rw [← b.sum_repr' x]
      rw [map_sum]; simp [map_smul, hG'b]
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, hx, ← b.sum_inner_mul_inner x x]
    simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_le_sum; intro i _
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [hp_orth j i hj]; ring) (by simp),
      real_inner_comm x (b i)]
    have h1 := hp_norm i
    have h2 := mul_self_nonneg (inner ℝ (b i) x)
    nlinarith
  · have hN : nuclearNorm Z = ∑ i, ‖T (b i)‖ := aux_svt_nuc_eq Z
    rw [aux_svt_K b, hN, ← hTdef]
    apply le_of_eq
    apply Finset.sum_congr rfl; intro i _
    rw [LinearEquiv.apply_symm_apply, hG'b]
    simp only [hp, real_inner_smul_left]
    rw [real_inner_self_eq_norm_sq]
    rcases eq_or_ne ‖T (b i)‖ 0 with h | h
    · simp [h]
    · field_simp

end eucl


section prox

variable {n₁ n₂ : ℕ}

lemma aux_svt_prox {τ : ℝ} (hτ : 0 < τ) {Y X : Mat n₁ n₂} (h : IsShrink τ Y X) (Z : Mat n₁ n₂) :
    fτ τ X - frobInner Y X + 1 / 2 * frobInner (Z - X) (Z - X) ≤ fτ τ Z - frobInner Y Z := by
  obtain ⟨r, U, σ, V, ⟨hU, hV, hσ, hY⟩, hX⟩ := h
  set d : Fin r → ℝ := fun i => max (σ i - τ) 0 with hd
  set g : Fin r → ℝ := fun i => σ i - d i with hg
  have hW : Y - X = U * diagonal g * Vᵀ := by
    rw [hY, hX, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  have hgb : ∀ i, 0 ≤ g i ∧ g i ≤ τ := by
    intro i; simp only [hg, hd]; constructor
    · have := hσ i
      rcases le_total (σ i - τ) 0 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    · have := le_max_left (σ i - τ) 0; linarith
  have hdn : ∀ i, 0 ≤ d i := fun i => le_max_right _ _
  have hi : frobInner (Y - X) Z ≤ τ * nuclearNorm Z := by
    rw [hW]; exact aux_svt_L1 hτ.le (aux_svt_L3 hU hV hgb) Z
  have hii : τ * nuclearNorm X ≤ frobInner (Y - X) X := by
    obtain ⟨G, hG, hNG⟩ := aux_svt_L2 X
    have h1 : nuclearNorm X ≤ ∑ k, d k := by
      refine hNG.trans ?_
      rw [hX]; exact aux_svt_L4 hU hV hG hdn
    have h2 : frobInner (Y - X) X = ∑ k, τ * d k := by
      rw [hW, hX, aux_svt_trace_diag hU hV]
      apply Finset.sum_congr rfl; intro k _
      simp only [hg, hd]
      rcases le_total (σ k - τ) 0 with h | h
      · rw [max_eq_right h]; ring
      · rw [max_eq_left h]; ring
    rw [h2, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h1 hτ.le
  have e : frobInner (Z - X) (Z - X) = frobInner Z Z - 2 * frobInner X Z + frobInner X X := by
    rw [aux_svt_fi_sub_left, aux_svt_fi_sub_right, aux_svt_fi_sub_right, aux_svt_fi_comm Z X]; ring
  rw [aux_svt_fi_sub_left] at hi hii
  unfold fτ
  rw [aux_svt_frobNorm_sq, aux_svt_frobNorm_sq, e]
  linarith

end prox

section main

variable {n₁ n₂ : ℕ}

lemma aux_svt_proj_add (Ω : Finset (Fin n₁ × Fin n₂)) (A B : Mat n₁ n₂) :
    projΩ Ω (A + B) = projΩ Ω A + projΩ Ω B := by
  ext i j; simp only [projΩ, Matrix.add_apply]; split_ifs <;> simp

lemma aux_svt_proj_sub (Ω : Finset (Fin n₁ × Fin n₂)) (A B : Mat n₁ n₂) :
    projΩ Ω (A - B) = projΩ Ω A - projΩ Ω B := by
  ext i j; simp only [projΩ, Matrix.sub_apply]; split_ifs <;> simp

lemma aux_svt_proj_smul (Ω : Finset (Fin n₁ × Fin n₂)) (c : ℝ) (A : Mat n₁ n₂) :
    projΩ Ω (c • A) = c • projΩ Ω A := by
  ext i j; simp only [projΩ, Matrix.smul_apply]; split_ifs <;> simp

lemma aux_svt_proj_proj (Ω : Finset (Fin n₁ × Fin n₂)) (A : Mat n₁ n₂) :
    projΩ Ω (projΩ Ω A) = projΩ Ω A := by
  ext i j; simp only [projΩ]; split_ifs <;> simp

lemma aux_svt_proj_zero (Ω : Finset (Fin n₁ × Fin n₂)) : projΩ Ω (0 : Mat n₁ n₂) = 0 := by
  ext i j; simp [projΩ]

lemma aux_svt_fi_proj (Ω : Finset (Fin n₁ × Fin n₂)) (A B : Mat n₁ n₂) :
    frobInner (projΩ Ω A) B = frobInner A (projΩ Ω B) := by
  unfold frobInner projΩ
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  split_ifs <;> simp

lemma aux_svt_fi_proj_self (Ω : Finset (Fin n₁ × Fin n₂)) (W : Mat n₁ n₂) :
    frobInner (projΩ Ω W) W = frobInner (projΩ Ω W) (projΩ Ω W) := by
  have h1 := aux_svt_fi_proj Ω W W
  have h2 := aux_svt_fi_proj Ω W (projΩ Ω W)
  rw [aux_svt_proj_proj] at h2
  linarith

lemma aux_svt_cont_fi_gen {α : Type*} [TopologicalSpace α] {f g : α → Mat n₁ n₂}
    (hf : ∀ i j, Continuous fun x => f x i j) (hg : ∀ i j, Continuous fun x => g x i j) :
    Continuous fun x => frobInner (f x) (g x) := by
  unfold frobInner
  exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
    (hf i j).mul (hg i j)))

lemma aux_svt_compact (M : Mat n₁ n₂) (R : ℝ) :
    IsCompact {Z : Mat n₁ n₂ | frobInner (M - Z) (M - Z) ≤ R} := by
  have hbox : IsCompact (Set.pi Set.univ (fun i : Fin n₁ => Set.pi Set.univ
      (fun j : Fin n₂ => Set.Icc (M i j - Real.sqrt R) (M i j + Real.sqrt R)))) :=
    isCompact_univ_pi (fun i => isCompact_univ_pi (fun j => isCompact_Icc))
  refine IsCompact.of_isClosed_subset hbox ?_ ?_
  · refine isClosed_le ?_ continuous_const
    have hc : ∀ i j, Continuous fun Z : Mat n₁ n₂ => (M - Z) i j := fun i j => by
      simp only [Matrix.sub_apply]
      exact continuous_const.sub (continuous_id.matrix_elem i j)
    exact aux_svt_cont_fi_gen hc hc
  · intro Z hZ
    refine Set.mem_univ_pi.2 (fun i => Set.mem_univ_pi.2 (fun j => ?_))
    rw [Set.mem_Icc]
    have h1 := aux_svt_entry_sq_le (M - Z) i j
    have h2 : |M i j - Z i j| ≤ Real.sqrt R :=
      Real.abs_le_sqrt (by simp only [Matrix.sub_apply] at h1; nlinarith [hZ.out])
    rw [abs_le] at h2; constructor <;> linarith

lemma aux_svt_tendsto_of_fi {A : ℕ → Mat n₁ n₂} {B : Mat n₁ n₂}
    (h : Tendsto (fun k => frobInner (B - A k) (B - A k)) atTop (𝓝 0)) :
    Tendsto A atTop (𝓝 B) := by
  refine tendsto_pi_nhds.2 (fun i => tendsto_pi_nhds.2 (fun j => ?_))
  rw [← tendsto_sub_nhds_zero_iff]
  have h2 : Tendsto (fun k => Real.sqrt (frobInner (B - A k) (B - A k))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h
    rw [Real.sqrt_zero] at this
    exact this
  refine squeeze_zero_norm (fun k => ?_) h2
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  have := aux_svt_entry_sq_le (B - A k) i j
  simp only [Matrix.sub_apply] at this
  nlinarith

end main

theorem aux_svt_core {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ) (Ω : Finset (Fin n₁ × Fin n₂))
    (M : Mat n₁ n₂) (δ : ℕ → ℝ)
    (hδ : ∃ a C : ℝ, 0 < a ∧ C < 2 ∧ ∀ k : ℕ, 1 ≤ k → a ≤ δ k ∧ δ k ≤ C)
    (X Y : ℕ → Mat n₁ n₂) (hXY : IsSVTSeq τ Ω M δ X Y) :
    (∃ Xb, IsSol28 τ Ω M Xb) ∧
      ∀ Xs : Mat n₁ n₂, IsSol28 τ Ω M Xs → Tendsto X atTop (𝓝 Xs) := by
  obtain ⟨a, C, ha, hC, hδb⟩ := hδ
  obtain ⟨hY0, hstep⟩ := hXY
  set r : ℕ → Mat n₁ n₂ := fun k => projΩ Ω (M - X k) with hr
  have hYs : ∀ k, Y (k + 1) = Y k + δ (k + 1) • r (k + 1) := fun k => (hstep k).2
  have hsh : ∀ k, IsShrink τ (Y k) (X (k + 1)) := fun k => (hstep k).1
  have hsupp : ∀ k, projΩ Ω (Y k) = Y k := by
    intro k
    induction k with
    | zero => rw [hY0]; exact aux_svt_proj_zero Ω
    | succ k ih =>
      rw [hYs, aux_svt_proj_add, aux_svt_proj_smul, ih]
      simp only [hr, aux_svt_proj_proj]
  set Gk : ℕ → ℝ := fun k => fτ τ (X (k + 1)) - frobInner (Y k) (X (k + 1) - M) with hGk
  have hprox : ∀ k Z, Gk k + 1 / 2 * frobInner (Z - X (k + 1)) (Z - X (k + 1)) ≤
      fτ τ Z - frobInner (Y k) (Z - M) := by
    intro k Z
    have := aux_svt_prox hτ (hsh k) Z
    simp only [hGk]
    rw [aux_svt_fi_sub_right (Y k) Z M, aux_svt_fi_sub_right (Y k) (X (k + 1)) M]
    linarith
  have hfeas : ∀ k Z, projΩ Ω Z = projΩ Ω M → frobInner (Y k) (Z - M) = 0 := by
    intro k Z hZ
    rw [← hsupp k, aux_svt_fi_proj, aux_svt_proj_sub, hZ, sub_self, aux_svt_fi_zero_right]
  have hweak : ∀ k Z, projΩ Ω Z = projΩ Ω M →
      Gk k + 1 / 2 * frobInner (Z - X (k + 1)) (Z - X (k + 1)) ≤ fτ τ Z := by
    intro k Z hZ
    have := hprox k Z
    rw [hfeas k Z hZ, sub_zero] at this
    exact this
  have hGle : ∀ k Z, projΩ Ω Z = projΩ Ω M → Gk k ≤ fτ τ Z := by
    intro k Z hZ
    have := hweak k Z hZ
    have := aux_svt_fi_self_nonneg (Z - X (k + 1))
    linarith
  set c₀ := a * (1 - C / 2) with hc₀
  have hc₀pos : 0 < c₀ := by apply mul_pos ha; linarith
  have hrr : ∀ k, frobInner (r k) (M - X k) = frobInner (r k) (r k) := fun k =>
    aux_svt_fi_proj_self Ω (M - X k)
  have hasc : ∀ k, Gk k + c₀ * frobInner (r (k + 1)) (r (k + 1)) ≤ Gk (k + 1) := by
    intro k
    obtain ⟨hδa, hδC⟩ := hδb (k + 1) (by omega)
    set dk := δ (k + 1) with hdk
    set e := X (k + 1 + 1) - X (k + 1) with he
    have h1 : Gk k + 1 / 2 * frobInner e e ≤
        fτ τ (X (k + 1 + 1)) - frobInner (Y k) (X (k + 1 + 1) - M) := hprox k (X (k + 1 + 1))
    have h2 : Gk (k + 1) = fτ τ (X (k + 1 + 1)) - frobInner (Y k) (X (k + 1 + 1) - M) -
        dk * frobInner (r (k + 1)) (X (k + 1 + 1) - M) := by
      simp only [hGk]
      rw [hYs k, aux_svt_fi_add_left, aux_svt_fi_smul_left]
      ring
    have h3 : frobInner (r (k + 1)) (X (k + 1 + 1) - M) =
        frobInner (r (k + 1)) e - frobInner (r (k + 1)) (r (k + 1)) := by
      have : X (k + 1 + 1) - M = e - (M - X (k + 1)) := by simp only [he]; abel
      rw [this, aux_svt_fi_sub_right, hrr (k + 1)]
    have h4 : 0 ≤ frobInner (e - dk • r (k + 1)) (e - dk • r (k + 1)) :=
      aux_svt_fi_self_nonneg _
    have h4' : frobInner (e - dk • r (k + 1)) (e - dk • r (k + 1)) =
        frobInner e e - 2 * dk * frobInner (r (k + 1)) e +
          dk ^ 2 * frobInner (r (k + 1)) (r (k + 1)) := by
      simp only [aux_svt_fi_sub_left, aux_svt_fi_sub_right, aux_svt_fi_smul_left,
        aux_svt_fi_smul_right]
      rw [aux_svt_fi_comm e (r (k + 1))]
      ring
    have hrnn := aux_svt_fi_self_nonneg (r (k + 1))
    have h5 : c₀ ≤ dk - dk ^ 2 / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hδa) (by linarith : (0:ℝ) ≤ 1 - C / 2),
        mul_nonneg (by linarith : (0:ℝ) ≤ dk) (sub_nonneg.2 hδC)]
    have h6 := mul_le_mul_of_nonneg_right h5 hrnn
    rw [h2, h3]
    nlinarith
  have hmono : Monotone Gk := monotone_nat_of_le_succ (fun k => by
    have := hasc k
    have := mul_nonneg hc₀pos.le (aux_svt_fi_self_nonneg (r (k + 1)))
    linarith)
  have hbdd : BddAbove (Set.range Gk) := ⟨fτ τ M, by
    rintro _ ⟨k, rfl⟩; exact hGle k M rfl⟩
  set Ginf := ⨆ k, Gk k with hGinf
  have hGk_le : ∀ k, Gk k ≤ Ginf := fun k => le_ciSup hbdd k
  have hGtend : Tendsto Gk atTop (𝓝 Ginf) := tendsto_atTop_ciSup hmono hbdd
  have hGinf_le : ∀ Z, projΩ Ω Z = projΩ Ω M → Ginf ≤ fτ τ Z := fun Z hZ =>
    ciSup_le (fun k => hGle k Z hZ)
  have hsum : ∀ m, c₀ * ∑ k ∈ Finset.range m, frobInner (r (k + 1)) (r (k + 1)) ≤
      Gk m - Gk 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := hasc m
      linarith
  have hsummable : Summable (fun k => frobInner (r (k + 1)) (r (k + 1))) := by
    apply summable_of_sum_range_le (c := (fτ τ M - Gk 0) / c₀)
      (fun k => aux_svt_fi_self_nonneg _)
    intro m
    rw [le_div_iff₀ hc₀pos]
    have := hsum m
    have := hGle m M rfl
    linarith
  have hr0 : Tendsto (fun k => frobInner (r (k + 1)) (r (k + 1))) atTop (𝓝 0) :=
    hsummable.tendsto_atTop_zero
  have hYid : ∀ k, frobInner (Y (k + 1)) (Y (k + 1)) = frobInner (Y k) (Y k) +
      2 * δ (k + 1) * (Gk k - fτ τ (X (k + 1))) +
      δ (k + 1) ^ 2 * frobInner (r (k + 1)) (r (k + 1)) := by
    intro k
    have hYr : frobInner (Y k) (r (k + 1)) = Gk k - fτ τ (X (k + 1)) := by
      simp only [hr, hGk]
      rw [← aux_svt_fi_proj, hsupp k, aux_svt_fi_sub_right, aux_svt_fi_sub_right]
      ring
    rw [hYs k]
    simp only [aux_svt_fi_add_left, aux_svt_fi_add_right, aux_svt_fi_smul_left,
      aux_svt_fi_smul_right]
    rw [aux_svt_fi_comm (r (k + 1)) (Y k), hYr]
    ring
  have hliminf : ∀ η > 0, ∀ K, ∃ k ≥ K, fτ τ (X (k + 1)) < Ginf + η := by
    intro η hη K
    by_contra hcon
    push Not at hcon
    set Ψ : ℕ → ℝ := fun k => c₀ * frobInner (Y k) (Y k) - 4 * Gk k with hΨ
    have hstepΨ : ∀ k ≥ K, Ψ (k + 1) ≤ Ψ k - 2 * c₀ * a * η := by
      intro k hk
      obtain ⟨hδa, hδC⟩ := hδb (k + 1) (by omega)
      have h1 := hYid k
      have h2 := hasc k
      have h3 := hcon k hk
      have h4 := hGk_le k
      have hrnn := aux_svt_fi_self_nonneg (r (k + 1))
      have hdk2 : δ (k + 1) ^ 2 ≤ 4 := by nlinarith
      have e1 : c₀ * (δ (k + 1) ^ 2 * frobInner (r (k + 1)) (r (k + 1))) ≤
          4 * (c₀ * frobInner (r (k + 1)) (r (k + 1))) := by
        have := mul_le_mul_of_nonneg_left hdk2 (mul_nonneg hc₀pos.le hrnn)
        nlinarith
      have e2 : δ (k + 1) * (Gk k - fτ τ (X (k + 1))) ≤ a * (-η) := by
        have hb : Gk k - fτ τ (X (k + 1)) ≤ -η := by linarith
        nlinarith
      have e3 := mul_le_mul_of_nonneg_left e2 (by positivity : (0:ℝ) ≤ 2 * c₀)
      simp only [hΨ]
      rw [h1]
      nlinarith
    have hiter : ∀ m : ℕ, Ψ (K + m) ≤ Ψ K - 2 * c₀ * a * η * m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have := hstepΨ (K + m) (by omega)
        rw [show K + (m + 1) = K + m + 1 by omega]
        push_cast
        linarith
    have hlow : ∀ k, -4 * fτ τ M ≤ Ψ k := by
      intro k
      simp only [hΨ]
      have := hGle k M rfl
      have := mul_nonneg hc₀pos.le (aux_svt_fi_self_nonneg (Y k))
      linarith
    have hpos : 0 < 2 * c₀ * a * η := by positivity
    obtain ⟨m, hm⟩ := exists_nat_gt ((Ψ K + 4 * fτ τ M) / (2 * c₀ * a * η))
    rw [div_lt_iff₀ hpos] at hm
    have := hiter m
    have := hlow (K + m)
    nlinarith
  have hfreq : ∀ n : ℕ, ∃ᶠ k in atTop, fτ τ (X (k + 1)) < Ginf + 1 / ((n : ℝ) + 1) := by
    intro n
    rw [Filter.frequently_atTop]
    intro K
    exact hliminf _ (by positivity) K
  obtain ⟨φ, hφmono, hφ⟩ := Filter.extraction_forall_of_frequently hfreq
  set B := 2 * (fτ τ M - Gk 0) with hB
  have hXbd : ∀ k, X (k + 1) ∈ {Z : Mat n₁ n₂ | frobInner (M - Z) (M - Z) ≤ B} := by
    intro k
    have h1 := hweak k M rfl
    have h2 := hmono (Nat.zero_le k)
    show frobInner (M - X (k + 1)) (M - X (k + 1)) ≤ B
    linarith
  have : FirstCountableTopology (Mat n₁ n₂) :=
    inferInstanceAs (FirstCountableTopology (Fin n₁ → Fin n₂ → ℝ))
  obtain ⟨Xb, -, ψ, hψmono, hψ⟩ := (aux_svt_compact M B).tendsto_subseq (fun n => hXbd (φ n))
  have hcont_e : ∀ i j, Continuous fun Z : Mat n₁ n₂ => projΩ Ω (M - Z) i j := by
    intro i j
    simp only [projΩ, Matrix.sub_apply]
    split_ifs
    · exact continuous_const.sub (continuous_id.matrix_elem i j)
    · exact continuous_const
  have hcontF : Continuous (fun Z : Mat n₁ n₂ =>
      frobInner (projΩ Ω (M - Z)) (projΩ Ω (M - Z))) := aux_svt_cont_fi_gen hcont_e hcont_e
  have hF1 : Tendsto (fun n => frobInner (projΩ Ω (M - X (φ (ψ n) + 1)))
      (projΩ Ω (M - X (φ (ψ n) + 1)))) atTop
      (𝓝 (frobInner (projΩ Ω (M - Xb)) (projΩ Ω (M - Xb)))) :=
    (hcontF.tendsto Xb).comp hψ
  have hF2 : Tendsto (fun n => frobInner (projΩ Ω (M - X (φ (ψ n) + 1)))
      (projΩ Ω (M - X (φ (ψ n) + 1)))) atTop (𝓝 0) :=
    hr0.comp ((hφmono.comp hψmono).tendsto_atTop)
  have hF := tendsto_nhds_unique hF1 hF2
  have hXbfeas : projΩ Ω Xb = projΩ Ω M := by
    have := aux_svt_fi_self_eq_zero hF
    rw [aux_svt_proj_sub, sub_eq_zero] at this
    exact this.symm
  obtain ⟨G₀, hG₀, hNG₀⟩ := aux_svt_L2 Xb
  set Φ : Mat n₁ n₂ → ℝ := fun Z => τ * frobInner G₀ Z + 1 / 2 * frobInner Z Z with hΦ
  have hΦle : ∀ Z, Φ Z ≤ fτ τ Z := by
    intro Z
    simp only [hΦ]
    unfold fτ
    rw [aux_svt_frobNorm_sq]
    have := aux_svt_L1 zero_le_one hG₀ Z
    nlinarith
  have hΦXb : fτ τ Xb ≤ Φ Xb := by
    simp only [hΦ]
    unfold fτ
    rw [aux_svt_frobNorm_sq]
    nlinarith
  have hid : ∀ i j, Continuous fun Z : Mat n₁ n₂ => Z i j := fun i j =>
    continuous_id.matrix_elem i j
  have hc0 : ∀ i j, Continuous fun _ : Mat n₁ n₂ => G₀ i j := fun _ _ => continuous_const
  have hΦcont : Continuous Φ :=
    (continuous_const.mul (aux_svt_cont_fi_gen hc0 hid)).add
      (continuous_const.mul (aux_svt_cont_fi_gen hid hid))
  have hlim1 : Tendsto (fun n => Φ (X (φ (ψ n) + 1))) atTop (𝓝 (Φ Xb)) :=
    (hΦcont.tendsto Xb).comp hψ
  have hlim2 : Tendsto (fun n => Ginf + 1 / ((ψ n : ℝ) + 1)) atTop (𝓝 Ginf) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hψmono.tendsto_atTop
    have := (tendsto_const_nhds (x := Ginf)).add this
    rw [add_zero] at this
    exact this
  have hXbopt : fτ τ Xb ≤ Ginf := by
    refine hΦXb.trans (le_of_tendsto_of_tendsto' hlim1 hlim2 (fun n => ?_))
    exact (hΦle _).trans (hφ (ψ n)).le
  have hXbsol : IsSol28 τ Ω M Xb := ⟨hXbfeas, fun Z hZ => hXbopt.trans (hGinf_le Z hZ)⟩
  refine ⟨⟨Xb, hXbsol⟩, fun Xs hXs => ?_⟩
  have hfXs : fτ τ Xs ≤ Ginf := (hXs.2 Xb hXbfeas).trans hXbopt
  have h1 : Tendsto (fun k => frobInner (Xs - X (k + 1)) (Xs - X (k + 1))) atTop (𝓝 0) := by
    have hup : Tendsto (fun k => 2 * (Ginf - Gk k)) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := Ginf)).sub hGtend).const_mul 2
      rw [sub_self, mul_zero] at this
      exact this
    refine squeeze_zero (fun k => aux_svt_fi_self_nonneg _) (fun k => ?_) hup
    have := hweak k Xs hXs.1
    linarith
  exact (tendsto_add_atTop_iff_nat 1).mp (aux_svt_tendsto_of_fi h1)

theorem aux_svt_final {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ) (Ω : Finset (Fin n₁ × Fin n₂))
    (M : Mat n₁ n₂) (δ : ℕ → ℝ)
    (hδ : ∃ a C : ℝ, 0 < a ∧ C < 2 ∧ ∀ k : ℕ, 1 ≤ k → a ≤ δ k ∧ δ k ≤ C)
    (X Y : ℕ → Mat n₁ n₂) (hXY : IsSVTSeq τ Ω M δ X Y) :
    (∃! Xs : Mat n₁ n₂, IsSol28 τ Ω M Xs) ∧
      ∀ Xs : Mat n₁ n₂, IsSol28 τ Ω M Xs → Tendsto X atTop (𝓝 Xs) := by
  obtain ⟨⟨Xb, hXb⟩, hconv⟩ := aux_svt_core τ hτ Ω M δ hδ X Y hXY
  exact ⟨⟨Xb, hXb, fun Xs hXs => tendsto_nhds_unique (hconv Xs hXs) (hconv Xb hXb)⟩, hconv⟩

end CaiCandesShen.Convergence

open CaiCandesShen.Convergence

theorem solution {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ) (Ω : Finset (Fin n₁ × Fin n₂))
    (M : Mat n₁ n₂) (δ : ℕ → ℝ)
    (hδ : ∃ a C : ℝ, 0 < a ∧ C < 2 ∧ ∀ k : ℕ, 1 ≤ k → a ≤ δ k ∧ δ k ≤ C)
    (X Y : ℕ → Mat n₁ n₂) (hXY : IsSVTSeq τ Ω M δ X Y) :
    (∃! Xs : Mat n₁ n₂, IsSol28 τ Ω M Xs) ∧
      ∀ Xs : Mat n₁ n₂, IsSol28 τ Ω M Xs → Tendsto X atTop (𝓝 Xs) :=
  aux_svt_final τ hτ Ω M δ hδ X Y hXY
