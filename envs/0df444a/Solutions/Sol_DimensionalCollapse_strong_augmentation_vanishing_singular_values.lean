-- Prove2me | solution 1 for DimensionalCollapse.strong_augmentation_vanishing_singular_values
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-25T10:03:35.708984+00:00
-- url     : https://prove2.me/submissions/668ade7d-4904-45a2-9d61-b30fb55cc17f

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic

open Matrix Filter Topology
open DimensionalCollapse

namespace DimCollapseAux

open Module InnerProductSpace

/-- The last singular value is a lower bound for `‖T v‖ / ‖v‖`. -/
lemma singularValues_last_mul_norm_le {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) {n : ℕ}
    (hn : finrank ℝ E = n) (hn0 : 0 < n) (v : E) :
    T.singularValues (n - 1) * ‖v‖ ≤ ‖T v‖ := by
  have hA : (LinearMap.adjoint T ∘ₗ T).IsSymmetric := T.isSymmetric_adjoint_comp_self
  set b := hA.eigenvectorBasis hn
  set lam := hA.eigenvalues hn
  have hsq : T.singularValues (n - 1) ^ 2 = lam ⟨n - 1, by omega⟩ :=
    T.sq_singularValues_of_lt hn (by omega)
  have hmin : ∀ i, lam ⟨n - 1, by omega⟩ ≤ lam i := fun i =>
    hA.eigenvalues_antitone hn (show i.val ≤ n - 1 by omega)
  have hAb : ∀ i, (LinearMap.adjoint T ∘ₗ T) (b i) = lam i • b i := by
    intro i
    exact hA.apply_eigenvectorBasis hn i
  have hnorm : ‖T v‖ ^ 2 = inner ℝ ((LinearMap.adjoint T ∘ₗ T) v) v := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  have hexp : inner ℝ ((LinearMap.adjoint T ∘ₗ T) v) v = ∑ i, lam i * inner ℝ (b i) v ^ 2 := by
    rw [← b.sum_inner_mul_inner ((LinearMap.adjoint T ∘ₗ T) v) v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA v (b i), hAb i, inner_smul_right, real_inner_comm v (b i)]
    ring
  have hv : ‖v‖ ^ 2 = ∑ i, inner ℝ (b i) v ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner v v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm v (b i)]
    ring
  have hsq_le : (T.singularValues (n - 1) * ‖v‖) ^ 2 ≤ ‖T v‖ ^ 2 := by
    rw [mul_pow, hsq, hv, hnorm, hexp, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hmin i) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (mul_nonneg (T.singularValues_nonneg _) (norm_nonneg _))
    (norm_nonneg _) two_ne_zero).mp hsq_le

end DimCollapseAux

open DimCollapseAux

theorem solution {n d : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsSymm)
    (hneg : ∃ μ : ℝ, μ < 0 ∧ ∃ v : Fin n → ℝ, v ≠ 0 ∧ X *ᵥ v = μ • v)
    (W : ℝ → Matrix (Fin d) (Fin n) ℝ)
    (hW : ∀ t, 0 ≤ t → ∀ a b,
      HasDerivWithinAt (fun s => W s a b) ((W t * X) a b) (Set.Ici 0) t) :
    Tendsto (fun t => minSingVal (W t)) atTop (𝓝 0) := by
  obtain ⟨μ, hμ, v, hv0, hXv⟩ := hneg
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd (funext fun i => i.elim0) hv0
    · exact h
  -- the trajectory `y(t) = W(t) v` solves `y' = μ y`
  have hderiv : ∀ t, 0 ≤ t → ∀ a,
      HasDerivWithinAt (fun s => (W s *ᵥ v) a) (μ * (W t *ᵥ v) a) (Set.Ici 0) t := by
    intro t ht a
    have h := HasDerivWithinAt.sum (u := Finset.univ) fun b _ => (hW t ht a b).mul_const (v b)
    have heq : (∑ b, (W t * X) a b * v b) = μ * (W t *ᵥ v) a := by
      have : ((W t * X) *ᵥ v) a = μ * (W t *ᵥ v) a := by
        rw [← Matrix.mulVec_mulVec, hXv, Matrix.mulVec_smul]; rfl
      rw [← this]; rfl
    rw [← heq]
    have hfun : (fun s => (W s *ᵥ v) a) = ∑ b, fun s => W s a b * v b := by
      funext s; simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
    rw [hfun]; exact h
  have hconst : ∀ t, 0 ≤ t → ∀ a, (W t *ᵥ v) a = Real.exp (μ * t) * (W 0 *ᵥ v) a := by
    intro t ht a
    set g := fun s => Real.exp (-μ * s) * (W s *ᵥ v) a with hg_def
    have hg : ∀ s, 0 ≤ s → HasDerivWithinAt g 0 (Set.Ici 0) s := by
      intro s hs
      have h1 : HasDerivWithinAt (fun s => Real.exp (-μ * s)) (Real.exp (-μ * s) * (-μ))
          (Set.Ici 0) s := by
        have := ((hasDerivAt_id s).const_mul (-μ)).exp
        simp only [id, mul_one] at this
        exact this.hasDerivWithinAt
      have h2 := h1.mul (hderiv s hs a)
      have h0 : Real.exp (-μ * s) * (-μ) * (W s *ᵥ v) a +
          Real.exp (-μ * s) * (μ * (W s *ᵥ v) a) = 0 := by ring
      rw [h0] at h2
      exact h2
    have hc := constant_of_has_deriv_right_zero (a := 0) (b := t) (f := g)
      (fun s hs => (hg s hs.1).continuousWithinAt.mono Set.Icc_subset_Ici_self)
      (fun s hs => (hg s hs.1).mono (Set.Ici_subset_Ici.mpr hs.1)) t ⟨ht, le_rfl⟩
    simp only [hg_def, mul_zero, Real.exp_zero, one_mul] at hc
    have := congrArg (fun x => Real.exp (μ * t) * x) hc
    simp only [← mul_assoc, ← Real.exp_add] at this
    simpa using this
  -- singular value bound
  set C := ‖(WithLp.toLp 2 (W 0 *ᵥ v) : EuclideanSpace ℝ (Fin d))‖ /
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ with hC
  have hv' : 0 < ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
    rw [norm_pos_iff]
    intro h
    exact hv0 (by simpa using congrArg WithLp.ofLp h)
  have hbound : ∀ t, 0 ≤ t → minSingVal (W t) ≤ Real.exp (μ * t) * C := by
    intro t ht
    have h := singularValues_last_mul_norm_le (Matrix.toEuclideanLin (W t))
      (finrank_euclideanSpace_fin) hn0 (WithLp.toLp 2 v)
    have hWt : W t *ᵥ v = Real.exp (μ * t) • (W 0 *ᵥ v) := by
      funext a; rw [hconst t ht a]; rfl
    have happ : Matrix.toEuclideanLin (W t) (WithLp.toLp 2 v) =
        Real.exp (μ * t) • (WithLp.toLp 2 (W 0 *ᵥ v) : EuclideanSpace ℝ (Fin d)) := by
      change WithLp.toLp 2 (W t *ᵥ v) = _
      rw [hWt, WithLp.toLp_smul]
    rw [happ, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    unfold minSingVal
    rw [hC, ← mul_div_assoc, le_div_iff₀ hv']
    exact h
  have hlim : Tendsto (fun t => Real.exp (μ * t) * C) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => μ * t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg hμ
    simpa using (Real.tendsto_exp_atBot.comp h1).mul_const C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun t => ?_) ?_
  · unfold minSingVal; exact LinearMap.singularValues_nonneg _ _
  · filter_upwards [eventually_ge_atTop 0] with t ht
    exact hbound t ht
