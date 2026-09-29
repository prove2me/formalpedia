-- Prove2me | solution 1 for CaiCandesShen.GeneralConvex.svt_general_converges
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:02:00.210047+00:00
-- url     : https://prove2.me/submissions/b866f462-6324-4c01-a5c2-fafb59a35e03

import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Problem
open Filter Topology

namespace CaiCandesShen.GeneralConvex

open Module InnerProductSpace

section nuc
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable abbrev aux_sgc_b (T : E →ₗ[ℝ] F) : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

lemma aux_sgc_inner (T : E →ₗ[ℝ] F) (i j : Fin (finrank ℝ E)) :
    ⟪T (aux_sgc_b T i), T (aux_sgc_b T j)⟫_ℝ =
      T.isSymmetric_adjoint_comp_self.eigenvalues rfl j * ⟪aux_sgc_b T i, aux_sgc_b T j⟫_ℝ := by
  rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply,
    LinearMap.IsSymmetric.apply_eigenvectorBasis, real_inner_smul_right]
  simp

lemma aux_sgc_sum_eq (T : E →ₗ[ℝ] F) :
    T.singularValues.sum (fun _ s => s) = ∑ i : Fin (finrank ℝ E), ‖T (aux_sgc_b T i)‖ := by
  rw [LinearMap.singularValues, Finsupp.sum_embDomain, Finsupp.sum_fintype _ _ (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finsupp.ofSupportFinite_coe]
  have h1 : ‖T (aux_sgc_b T i)‖ ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues rfl i := by
    rw [← real_inner_self_eq_norm_sq, aux_sgc_inner, real_inner_self_eq_norm_sq,
      (aux_sgc_b T).orthonormal.1 i]
    simp
  rw [← h1, Real.sqrt_sq (norm_nonneg _)]

omit [FiniteDimensional ℝ F] in
lemma aux_sgc_normsq {ι : Type*} [Fintype ι] (u : ι → F)
    (hu : Pairwise fun i j => ⟪u i, u j⟫_ℝ = 0) (hu1 : ∀ i, ‖u i‖ ≤ 1) (c : ι → ℝ) :
    ‖∑ i, c i • u i‖ ^ 2 ≤ ∑ i, c i * c i := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have h0 : ‖u i‖ ^ 2 ≤ 1 := by
      have := hu1 i
      have := norm_nonneg (u i)
      nlinarith
    have := mul_self_nonneg (c i)
    nlinarith
  · intro k _ hk
    rw [real_inner_smul_left, real_inner_smul_right, hu (Ne.symm hk)]
    simp
  · simp

lemma aux_sgc_le (T : E →ₗ[ℝ] F) {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E) (u : ι → F)
    (hu : Pairwise fun i j => ⟪u i, u j⟫_ℝ = 0) (hu1 : ∀ i, ‖u i‖ ≤ 1) :
    ∑ i, ⟪T (e i), u i⟫_ℝ ≤ T.singularValues.sum (fun _ s => s) := by
  rw [aux_sgc_sum_eq]
  set b := aux_sgc_b T
  have key : ∀ i, T (e i) = ∑ j, ⟪b j, e i⟫_ℝ • T (b j) := by
    intro i
    conv_lhs => rw [← b.sum_repr' (e i)]
    simp [map_sum, map_smul]
  have h2 : ∑ i, ⟪T (e i), u i⟫_ℝ = ∑ j, ⟪T (b j), ∑ i, ⟪b j, e i⟫_ℝ • u i⟫_ℝ := by
    simp_rw [key, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    rw [Finset.sum_comm]
  rw [h2]
  refine Finset.sum_le_sum fun j _ => ?_
  refine (real_inner_le_norm _ _).trans ?_
  have hw : ‖∑ i, ⟪b j, e i⟫_ℝ • u i‖ ≤ 1 := by
    have h3 := aux_sgc_normsq u hu hu1 (fun i => ⟪b j, e i⟫_ℝ)
    have h4 : ∑ i, ⟪b j, e i⟫_ℝ * ⟪b j, e i⟫_ℝ = 1 := by
      have := e.sum_inner_mul_inner (b j) (b j)
      simp_rw [real_inner_comm (b j) (e _)] at this
      rw [this, real_inner_self_eq_norm_sq, b.orthonormal.1 j]
      simp
    rw [h4] at h3
    have := norm_nonneg (∑ i, ⟪b j, e i⟫_ℝ • u i)
    nlinarith
  calc _ ≤ ‖T (b j)‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = _ := mul_one _

lemma aux_sgc_eq (T : E →ₗ[ℝ] F) :
    T.singularValues.sum (fun _ s => s) =
      ∑ i, ⟪T (aux_sgc_b T i), ‖T (aux_sgc_b T i)‖⁻¹ • T (aux_sgc_b T i)⟫_ℝ := by
  rw [aux_sgc_sum_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  rcases eq_or_ne ‖T (aux_sgc_b T i)‖ 0 with h | h
  · simp [h]
  · field_simp

lemma aux_sgc_orth (T : E →ₗ[ℝ] F) :
    Pairwise fun i j => ⟪‖T (aux_sgc_b T i)‖⁻¹ • T (aux_sgc_b T i),
      ‖T (aux_sgc_b T j)‖⁻¹ • T (aux_sgc_b T j)⟫_ℝ = 0 := by
  intro i j hij
  rw [real_inner_smul_left, real_inner_smul_right, aux_sgc_inner,
    (aux_sgc_b T).orthonormal.2 hij]
  simp

omit [FiniteDimensional ℝ F] in
lemma aux_sgc_norm_le (x : F) : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with h | h
  · simp [h]
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

lemma aux_sgc_convex (A B : E →ₗ[ℝ] F) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (a • A + c • B).singularValues.sum (fun _ s => s) ≤
      a * A.singularValues.sum (fun _ s => s) + c * B.singularValues.sum (fun _ s => s) := by
  rw [aux_sgc_eq (a • A + c • B)]
  have hA := aux_sgc_le A (aux_sgc_b (a • A + c • B)) _ (aux_sgc_orth (a • A + c • B))
    (fun _ => aux_sgc_norm_le _)
  have hB := aux_sgc_le B (aux_sgc_b (a • A + c • B)) _ (aux_sgc_orth (a • A + c • B))
    (fun _ => aux_sgc_norm_le _)
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, real_inner_smul_left,
    Finset.sum_add_distrib, ← Finset.mul_sum] at hA hB ⊢
  nlinarith [mul_le_mul_of_nonneg_left hA ha, mul_le_mul_of_nonneg_left hB hc]

end nuc

section mat

lemma aux_sgc_nuc_convex {n₁ n₂ : ℕ} (X Y : Mat n₁ n₂) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    nuclearNorm (a • X + c • Y) ≤ a * nuclearNorm X + c * nuclearNorm Y := by
  unfold nuclearNorm
  rw [map_add, map_smul, map_smul]
  exact aux_sgc_convex _ _ a c ha hc

lemma aux_sgc_fI_self_nonneg {n₁ n₂ : ℕ} (X : Mat n₁ n₂) : 0 ≤ frobInner X X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

lemma aux_sgc_frobNorm_sq {n₁ n₂ : ℕ} (X : Mat n₁ n₂) : frobNorm X ^ 2 = frobInner X X :=
  Real.sq_sqrt (aux_sgc_fI_self_nonneg X)

lemma aux_sgc_fI_expand {n₁ n₂ : ℕ} (X D : Mat n₁ n₂) (t : ℝ) :
    frobInner (X + t • D) (X + t • D) =
      frobInner X X + 2 * t * frobInner X D + t ^ 2 * frobInner D D := by
  simp only [frobInner, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma aux_sgc_fI_neg {n₁ n₂ : ℕ} (D : Mat n₁ n₂) :
    frobInner (-D) (-D) = frobInner D D := by
  simp [frobInner]

lemma aux_sgc_lim {a b c : ℝ} (hc : 0 ≤ c) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → a ≤ b + t * c) :
    a ≤ b := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have ht : 0 < min 1 (ε / (c + 1)) := lt_min one_pos (div_pos hε (by linarith))
  have h1 := h _ ht (min_le_left _ _)
  have h2 : min 1 (ε / (c + 1)) * c ≤ ε := by
    calc min 1 (ε / (c + 1)) * c ≤ ε / (c + 1) * c :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hc
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- Strong convexity at a minimizer of the Lagrangian with nonnegative multipliers. -/
lemma aux_sgc_sc {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (Xm : Mat n₁ n₂) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hmin : ∀ X' : Mat n₁ n₂, lagr τ f Xm y ≤ lagr τ f X' y) (D : Mat n₁ n₂) :
    lagr τ f Xm y + 1 / 2 * frobInner D D ≤ lagr τ f (Xm + D) y := by
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      τ * nuclearNorm Xm + dot y (constraintMap f Xm) ≤
        (τ * nuclearNorm (Xm + D) + dot y (constraintMap f (Xm + D)) + frobInner Xm D) +
          t * (1 / 2 * frobInner D D) := by
    intro t ht0 ht1
    have h := hmin (Xm + t • D)
    have hcv : Xm + t • D = (1 - t) • Xm + t • (Xm + D) := by
      rw [sub_smul, one_smul, smul_add]; abel
    have hN := aux_sgc_nuc_convex Xm (Xm + D) (1 - t) t (by linarith) ht0.le
    rw [← hcv] at hN
    have hF : dot y (constraintMap f (Xm + t • D)) ≤
        (1 - t) * dot y (constraintMap f Xm) + t * dot y (constraintMap f (Xm + D)) := by
      unfold dot constraintMap
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hc := (hconv i).2 (Set.mem_univ Xm) (Set.mem_univ (Xm + D)) (sub_nonneg.2 ht1)
        ht0.le (by ring)
      rw [← hcv] at hc
      simp only [smul_eq_mul] at hc
      nlinarith [mul_le_mul_of_nonneg_left hc (hy i)]
    unfold lagr fτ at h
    rw [aux_sgc_frobNorm_sq, aux_sgc_frobNorm_sq, aux_sgc_fI_expand] at h
    have hmain : t * (τ * nuclearNorm Xm + dot y (constraintMap f Xm)) ≤
        t * ((τ * nuclearNorm (Xm + D) + dot y (constraintMap f (Xm + D)) + frobInner Xm D) +
          t * (1 / 2 * frobInner D D)) := by
      nlinarith [mul_le_mul_of_nonneg_left hN hτ.le]
    exact le_of_mul_le_mul_left hmain ht0
  have hlim := aux_sgc_lim (by have := aux_sgc_fI_self_nonneg D; positivity) key
  unfold lagr fτ
  rw [aux_sgc_frobNorm_sq, aux_sgc_frobNorm_sq]
  have hfrob2 := aux_sgc_fI_expand Xm D 1
  rw [one_smul] at hfrob2
  rw [hfrob2]
  nlinarith

end mat

lemma aux_sgc_fejer {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ X Y : Mat n₁ n₂, eucNorm (constraintMap f X - constraintMap f Y) ≤ L * frobNorm (X - Y))
    (δ : ℕ → ℝ) (β : ℝ) (hβ : 0 < β) (hδβ : ∀ k : ℕ, 1 ≤ k → β ≤ 2 * δ k - δ k ^ 2 * L ^ 2)
    (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) (hseq : IsGeneralSVTSeq τ f δ X y)
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys) :
    ∀ k : ℕ, eucNorm (y (k + 1) - ys) ^ 2 ≤
      eucNorm (y k - ys) ^ 2 - β * frobNorm (X (k + 1) - Xs) ^ 2 := by
  intro k
  obtain ⟨hy0, hmin, hupd⟩ := hseq
  obtain ⟨hys0, hsad, hminS⟩ := hopt
  -- nonnegativity of the dual iterates
  have hyk : ∀ j : ℕ, ∀ i, 0 ≤ y j i := by
    intro j i
    cases j with
    | zero => rw [hy0]; exact le_refl _
    | succ j => rw [hupd j i]; exact le_max_right _ _
  -- step size
  have hβk := hδβ (k + 1) (by omega)
  set d := δ (k + 1) with hd
  have hdpos : 0 < d := by
    by_contra hcon
    have hcon : d ≤ 0 := not_lt.mp hcon
    nlinarith [sq_nonneg (d * L)]
  -- complementary slackness: F(Xs) ≤ 0 and ys_i F_i(Xs) = 0
  have hkey : ∀ i (c : ℝ), 0 ≤ ys i + c → c * constraintMap f Xs i ≤ 0 := by
    intro i c hc
    have hnn : ∀ j, 0 ≤ (ys + Pi.single i c : Fin m → ℝ) j := by
      intro j
      by_cases hj : j = i
      · subst hj; simpa using hc
      · simp [hj, hys0 j]
    have h := hsad _ hnn
    unfold lagr at h
    have hdot : dot (ys + Pi.single i c) (constraintMap f Xs) =
        dot ys (constraintMap f Xs) + c * constraintMap f Xs i := by
      unfold dot
      simp [add_mul, Finset.sum_add_distrib, Pi.single_apply]
    rw [hdot] at h
    linarith
  have hfix : ∀ i, ys i = max (ys i + d * constraintMap f Xs i) 0 := by
    intro i
    have hy : 0 ≤ ys i := hys0 i
    have h1 := hkey i 1 (by linarith)
    have h2 := hkey i (-ys i) (by linarith)
    have hF : constraintMap f Xs i ≤ 0 := by linarith
    rcases hy.eq_or_lt with h | h
    · rw [← h]
      have : d * constraintMap f Xs i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hdpos.le hF
      simp only [zero_add]
      exact (max_eq_right this).symm
    · have hF0 : constraintMap f Xs i = 0 := by
        have : 0 ≤ ys i * constraintMap f Xs i := by linarith
        have : 0 ≤ constraintMap f Xs i := by
          by_contra hc
          have hc' : constraintMap f Xs i < 0 := lt_of_not_ge hc
          nlinarith
        linarith
      rw [hF0, mul_zero, add_zero, max_eq_left hy]
  -- strong monotonicity inequality
  set X' := X (k + 1) with hX'
  set D := X' - Xs with hD
  have h1 := aux_sgc_sc τ hτ f hconv X' (y k) (hyk k) (hmin k) (Xs - X')
  have h2 := aux_sgc_sc τ hτ f hconv Xs ys hys0 hminS D
  have e1 : X' + (Xs - X') = Xs := by abel
  have e2 : Xs + D = X' := by rw [hD]; abel
  have e3 : Xs - X' = -D := by rw [hD]; abel
  rw [e1] at h1
  rw [e2] at h2
  rw [e3, aux_sgc_fI_neg] at h1
  unfold lagr at h1 h2
  set u : Fin m → ℝ := fun i => y k i - ys i with hu
  set v : Fin m → ℝ := fun i => f i X' - f i Xs with hv
  have hSuv_eq : ∑ i, u i * v i = dot (y k) (constraintMap f X') - dot (y k) (constraintMap f Xs)
      - dot ys (constraintMap f X') + dot ys (constraintMap f Xs) := by
    simp only [hu, hv, dot, constraintMap, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hSuv : ∑ i, u i * v i ≤ - frobInner D D := by
    rw [hSuv_eq]; linarith
  -- Lipschitz bound
  have hE : ∀ w : Fin m → ℝ, eucNorm w ^ 2 = ∑ i, w i ^ 2 := by
    intro w
    unfold eucNorm dot
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg _)]
    simp [sq]
  have hLip := hL X' Xs
  have hLip2 : eucNorm (constraintMap f X' - constraintMap f Xs) ^ 2 ≤
      (L * frobNorm D) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hLip 2
  rw [hE, mul_pow, aux_sgc_frobNorm_sq] at hLip2
  have hSvv : ∑ i, v i ^ 2 ≤ L ^ 2 * frobInner D D := by
    have : ∀ i, (constraintMap f X' - constraintMap f Xs) i = v i := by
      intro i; simp [hv, constraintMap]
    simp only [this] at hLip2
    exact hLip2
  -- nonexpansiveness of the positive part
  have hproj : ∀ i, (y (k + 1) i - ys i) ^ 2 ≤ (u i + d * v i) ^ 2 := by
    intro i
    rw [hupd k i]
    conv_lhs => rw [hfix i]
    rw [sq_le_sq]
    have := abs_max_sub_max_le_abs (y k i + d * constraintMap f X' i)
      (ys i + d * constraintMap f Xs i) 0
    have heq : y k i + d * constraintMap f X' i - (ys i + d * constraintMap f Xs i) =
        u i + d * v i := by
      simp only [hu, hv, constraintMap]; ring
    rw [heq] at this
    exact this
  have hexp : ∑ i, (u i + d * v i) ^ 2 =
      ∑ i, u i ^ 2 + 2 * d * ∑ i, u i * v i + d ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hLHS : eucNorm (y (k + 1) - ys) ^ 2 ≤ ∑ i, (u i + d * v i) ^ 2 := by
    rw [hE]
    exact Finset.sum_le_sum fun i _ => by simpa using hproj i
  have hRHS : eucNorm (y k - ys) ^ 2 = ∑ i, u i ^ 2 := by
    rw [hE]; simp [hu]
  rw [hRHS, aux_sgc_frobNorm_sq]
  have hFD := aux_sgc_fI_self_nonneg D
  rw [hexp] at hLHS
  nlinarith [mul_le_mul_of_nonneg_left hSuv (by linarith : (0:ℝ) ≤ 2 * d),
    mul_le_mul_of_nonneg_left hSvv (sq_nonneg d), mul_le_mul_of_nonneg_right hβk hFD]

lemma aux_sgc_fI_zero {n₁ n₂ : ℕ} (D : Mat n₁ n₂) (h : frobInner D D ≤ 0) : D = 0 := by
  have h0 : frobInner D D = 0 := le_antisymm h (aux_sgc_fI_self_nonneg D)
  unfold frobInner at h0
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg fun j _ => mul_self_nonneg (D i j))).1 h0 i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (D i j))).1 h1 j
    (Finset.mem_univ _)
  simpa using mul_self_eq_zero.1 h2

lemma aux_sgc_entry_le {n₁ n₂ : ℕ} (D : Mat n₁ n₂) (i : Fin n₁) (j : Fin n₂) :
    |D i j| ≤ frobNorm D := by
  unfold frobNorm
  apply Real.abs_le_sqrt
  unfold frobInner
  have h1 : D i j * D i j ≤ ∑ j', D i j' * D i j' :=
    Finset.single_le_sum (f := fun j' => D i j' * D i j') (fun j' _ => mul_self_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ j', D i j' * D i j' ≤ ∑ i', ∑ j', D i' j' * D i' j' :=
    Finset.single_le_sum (f := fun i' => ∑ j', D i' j' * D i' j')
      (fun i' _ => Finset.sum_nonneg fun j' _ => mul_self_nonneg _) (Finset.mem_univ i)
  nlinarith

/-- Saddle point implies complementary slackness facts. -/
lemma aux_sgc_slack {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys) :
    (∀ i, f i Xs ≤ 0) ∧ dot ys (constraintMap f Xs) = 0 := by
  obtain ⟨hys0, hsad, _⟩ := hopt
  have hkey : ∀ i (c : ℝ), 0 ≤ ys i + c → c * constraintMap f Xs i ≤ 0 := by
    intro i c hc
    have hnn : ∀ j, 0 ≤ (ys + Pi.single i c : Fin m → ℝ) j := by
      intro j
      by_cases hj : j = i
      · subst hj; simpa using hc
      · simp [hj, hys0 j]
    have h := hsad _ hnn
    unfold lagr at h
    have hdot : dot (ys + Pi.single i c) (constraintMap f Xs) =
        dot ys (constraintMap f Xs) + c * constraintMap f Xs i := by
      unfold dot
      simp [add_mul, Finset.sum_add_distrib, Pi.single_apply]
    rw [hdot] at h
    linarith
  have hF : ∀ i, f i Xs ≤ 0 := by
    intro i
    have := hkey i 1 (by linarith [hys0 i])
    simpa [constraintMap] using this
  refine ⟨hF, ?_⟩
  unfold dot
  refine Finset.sum_eq_zero fun i _ => ?_
  have h2 := hkey i (-ys i) (by linarith)
  have h3 : ys i * constraintMap f Xs i ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hys0 i) (by simpa [constraintMap] using hF i)
  linarith

lemma aux_sgc_sol {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys) :
    IsSol34 τ f Xs := by
  obtain ⟨hF, hdot⟩ := aux_sgc_slack τ f Xs ys hopt
  refine ⟨hF, fun X hX => ?_⟩
  have h := hopt.2.2 X
  unfold lagr at h
  have hnp : dot ys (constraintMap f X) ≤ 0 := by
    unfold dot
    exact Finset.sum_nonpos fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (hopt.1 i) (by simpa [constraintMap] using hX i)
  linarith

lemma aux_sgc_uniq {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys)
    (Z : Mat n₁ n₂) (hZ : IsSol34 τ f Z) : Z = Xs := by
  obtain ⟨hF, hdot⟩ := aux_sgc_slack τ f Xs ys hopt
  have h := aux_sgc_sc τ hτ f hconv Xs ys hopt.1 hopt.2.2 (Z - Xs)
  have e : Xs + (Z - Xs) = Z := by abel
  rw [e] at h
  unfold lagr at h
  have hnp : dot ys (constraintMap f Z) ≤ 0 := by
    unfold dot
    exact Finset.sum_nonpos fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (hopt.1 i) (by simpa [constraintMap] using hZ.1 i)
  have hle := hZ.2 Xs hF
  have hD : frobInner (Z - Xs) (Z - Xs) ≤ 0 := by linarith
  have := aux_sgc_fI_zero _ hD
  exact sub_eq_zero.1 this


end CaiCandesShen.GeneralConvex

open CaiCandesShen.GeneralConvex

theorem solution {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ X Y : Mat n₁ n₂, eucNorm (constraintMap f X - constraintMap f Y) ≤ L * frobNorm (X - Y))
    (hdual : ∃ (Xs : Mat n₁ n₂) (ys : Fin m → ℝ), IsPrimalDualOptimal τ f Xs ys)
    (δ : ℕ → ℝ)
    (hδ : ∃ a C : ℝ, 0 < a ∧ C * L ^ 2 < 2 ∧ ∀ k : ℕ, 1 ≤ k → a ≤ δ k ∧ δ k ≤ C)
    (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) (hseq : IsGeneralSVTSeq τ f δ X y) :
    (∃! Xs : Mat n₁ n₂, IsSol34 τ f Xs) ∧
      ∀ Xs : Mat n₁ n₂, IsSol34 τ f Xs → Tendsto X atTop (𝓝 Xs) := by
  obtain ⟨X0, y0, hopt⟩ := hdual
  obtain ⟨a, C, ha, hCL, hδ'⟩ := hδ
  have hsol := aux_sgc_sol τ f X0 y0 hopt
  have huniq := aux_sgc_uniq τ hτ f hconv X0 y0 hopt
  refine ⟨⟨X0, hsol, huniq⟩, fun Xs hXs => ?_⟩
  rw [huniq Xs hXs]
  set β := a * (2 - C * L ^ 2) with hβdef
  have hβ : 0 < β := mul_pos ha (by linarith)
  have hδβ : ∀ k : ℕ, 1 ≤ k → β ≤ 2 * δ k - δ k ^ 2 * L ^ 2 := by
    intro k hk
    obtain ⟨h1, h2⟩ := hδ' k hk
    have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
    have h3 : δ k * L ^ 2 ≤ C * L ^ 2 := mul_le_mul_of_nonneg_right h2 hL2
    have h4 : 0 ≤ (δ k - a) * (2 - δ k * L ^ 2) :=
      mul_nonneg (by linarith) (by linarith)
    have h5 : 0 ≤ (a * L ^ 2) * (C - δ k) :=
      mul_nonneg (mul_nonneg ha.le hL2) (by linarith)
    rw [hβdef]
    nlinarith
  have hfej := aux_sgc_fejer τ hτ f hconv L hL0 hL δ β hβ hδβ X y hseq X0 y0 hopt
  set g : ℕ → ℝ := fun k => β * frobNorm (X (k + 1) - X0) ^ 2 with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => mul_nonneg hβ.le (sq_nonneg _)
  have hsum : ∀ N, ∑ k ∈ Finset.range N, g k ≤
      eucNorm (y 0 - y0) ^ 2 - eucNorm (y N - y0) ^ 2 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := hfej N
      simp only [hg]
      linarith
  have hsum' : ∀ N, ∑ k ∈ Finset.range N, g k ≤ eucNorm (y 0 - y0) ^ 2 := by
    intro N
    have := hsum N
    nlinarith [sq_nonneg (eucNorm (y N - y0))]
  have hsm : Summable g := summable_of_sum_range_le hg0 hsum'
  have hgt : Tendsto g atTop (𝓝 0) := hsm.tendsto_atTop_zero
  have hF2 : Tendsto (fun k => frobInner (X (k + 1) - X0) (X (k + 1) - X0)) atTop (𝓝 0) := by
    have := hgt.const_mul β⁻¹
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    simp only [hg, aux_sgc_frobNorm_sq]
    field_simp
  have hFn : Tendsto (fun k => frobNorm (X (k + 1) - X0)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hF2
    rw [Real.sqrt_zero] at this
    exact this
  have hshift : Tendsto (fun k => X (k + 1)) atTop (𝓝 X0) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hFn
    rw [Real.norm_eq_abs]
    exact aux_sgc_entry_le (X (k + 1) - X0) i j
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 hshift
