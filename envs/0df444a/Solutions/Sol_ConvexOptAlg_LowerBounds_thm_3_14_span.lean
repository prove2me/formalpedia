-- Prove2me | solution 1 for ConvexOptAlg.LowerBounds.thm_3_14_span
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:57:30.967398+00:00
-- url     : https://prove2.me/submissions/89e28c3c-8a74-4be5-9c0e-cd86a84d7d44

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs
set_option autoImplicit false

open scoped InnerProductSpace
open ConvexOptAlg.LowerBounds

private lemma mem_span_basisVec_Ico_iff {n : ℕ} (s : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ Submodule.span ℝ (basisVec n '' Set.Ico 1 s) ↔
      ∀ j : Fin n, s ≤ (j : ℕ) + 1 → y j = 0 := by
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    { carrier := {y | ∀ j : Fin n, s ≤ (j : ℕ) + 1 → y j = 0}
      add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
      zero_mem' := fun j _ => rfl
      smul_mem' := fun c a ha j hj => by simp [ha j hj] }
  constructor
  · intro hy
    have h_le : Submodule.span ℝ (basisVec n '' Set.Ico 1 s) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨i, ⟨hi1, his⟩, rfl⟩ j hj
      simp only [basisVec, WithLp.ofLp_toLp, if_neg (by omega : ¬(j : ℕ) + 1 = i)]
    exact h_le hy
  · intro hy
    have hy_sum : y = ∑ j : Fin n, (y j) • basisVec n ((j : ℕ) + 1) := by
      ext l
      rw [WithLp.ofLp_sum, Finset.sum_apply]
      have : (∑ j : Fin n, ((y j) • basisVec n ((j : ℕ) + 1)).ofLp l) =
          ∑ j : Fin n, if j = l then y j else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        change y j * (if (l : ℕ) + 1 = (j : ℕ) + 1 then (1 : ℝ) else 0) =
          if j = l then y j else 0
        by_cases hjl : j = l
        · subst hjl; simp
        · have hne : ¬(l : ℕ) + 1 = (j : ℕ) + 1 := by
            intro h
            apply hjl
            ext
            omega
          rw [if_neg hne, if_neg hjl, mul_zero]
      rw [this, Finset.sum_ite_eq', if_pos (Finset.mem_univ l)]
    rw [hy_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : s ≤ (j : ℕ) + 1
    · rw [hy j hj, zero_smul]
      exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨(j : ℕ) + 1, ⟨by omega, by omega⟩, rfl⟩

private lemma fK_directional_deriv {n k : ℕ} {β : ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hg : ∀ y, HasGradientAt (fK n β k) (g y) y)
    (y d : EuclideanSpace ℝ (Fin n)) :
    ⟪g y, d⟫_ℝ =
      β / 8 * (dotProduct y.ofLp ((tridiag n k).mulVec d.ofLp) +
        dotProduct d.ofLp ((tridiag n k).mulVec y.ofLp)) -
      β / 4 * ⟪d, basisVec n 1⟫_ℝ := by
  let A := tridiag n k
  let c0 := fK n β k y
  let c1 := β / 8 * (dotProduct y.ofLp (A.mulVec d.ofLp) +
    dotProduct d.ofLp (A.mulVec y.ofLp)) - β / 4 * ⟪d, basisVec n 1⟫_ℝ
  let c2 := β / 8 * quadForm A d
  have h_id : HasDerivAt (fun r : ℝ => r) 1 0 := hasDerivAt_id 0
  have h_path : HasDerivAt (fun r : ℝ => y + r • d) d 0 := by
    have h1 := (h_id.smul_const d).const_add y
    rwa [one_smul] at h1
  have hf0 : HasFDerivAt (fK n β k)
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (g y)) (y + (0 : ℝ) • d) := by
    rw [zero_smul, add_zero]
    exact (hg y).hasFDerivAt
  have h_fderiv := hf0.comp_hasDerivAt 0 h_path
  have hd1 : HasDerivAt (fun r : ℝ => fK n β k (y + r • d)) ⟪g y, d⟫_ℝ 0 := h_fderiv
  have h_poly : ∀ r : ℝ, fK n β k (y + r • d) = c0 + r * c1 + r ^ 2 * c2 := by
    intro r
    dsimp [c0, c1, c2, fK, quadForm, A]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
      inner_add_left, real_inner_smul_left, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  have hd2 : HasDerivAt (fun r : ℝ => fK n β k (y + r • d)) c1 0 := by
    simp_rw [h_poly]
    have h_lin : HasDerivAt (fun r : ℝ => r * c1) c1 0 := by
      have h1 := h_id.mul_const c1
      rwa [one_mul] at h1
    have h_sq : HasDerivAt (fun r : ℝ => r ^ 2 * c2) 0 0 := by
      have h1 := (hasDerivAt_pow 2 (0 : ℝ)).mul_const c2
      norm_num at h1
      exact h1
    have h_sum := (h_lin.const_add c0).add h_sq
    rwa [add_zero] at h_sum
  exact hd1.unique hd2

theorem solution (n t : ℕ) (β : ℝ) (hβ : 0 < β) (htn : 2 * t + 1 ≤ n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ y, HasGradientAt (fK n β (2 * t + 1)) (g y) y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : SatisfiesSpanCondition g x) :
    (∀ s : ℕ, 1 ≤ s → x s ∈ Submodule.span ℝ (basisVec n '' Set.Ico 1 s)) ∧
      ∀ s : ℕ, 1 ≤ s → s ≤ t →
        (∀ i ∈ Finset.Icc s n, coord (x s) i = 0) ∧
          quadForm (tridiag n (2 * t + 1)) (x s) = quadForm (tridiag n s) (x s) ∧
          fK n β (2 * t + 1) (x s) = fK n β s (x s) := by
  have hg_step : ∀ (s : ℕ), 1 ≤ s → ∀ y ∈ Submodule.span ℝ (basisVec n '' Set.Ico 1 s),
      g y ∈ Submodule.span ℝ (basisVec n '' Set.Ico 1 (s + 1)) := by
    intro s hs y hy
    rw [mem_span_basisVec_Ico_iff] at hy ⊢
    intro j hj
    let d : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun b : Fin n => if b = j then (1 : ℝ) else 0)
    have h_gy_j : ⟪g y, d⟫_ℝ = g y j := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      dsimp [d, dotProduct]
      have : (∑ b : Fin n, (if b = j then (1 : ℝ) else 0) * (g y).ofLp b) =
          ∑ b : Fin n, if b = j then (g y).ofLp b else 0 := by
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> ring
      rw [this, Finset.sum_ite_eq', if_pos (Finset.mem_univ j)]
    have h_d_e1 : ⟪d, basisVec n 1⟫_ℝ = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      dsimp [d, basisVec, dotProduct]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hbj : b = j
      · subst hbj
        rw [if_pos rfl, if_neg (by omega), zero_mul]
      · rw [if_neg hbj, mul_zero]
    let A := tridiag n (2 * t + 1)
    have h_dot1 : dotProduct y.ofLp (A.mulVec d.ofLp) = 0 := by
      dsimp [d, dotProduct, Matrix.mulVec]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases ha : s ≤ (a : ℕ) + 1
      · rw [hy a ha, zero_mul]
      · have h_inner_zero : (∑ b : Fin n, A a b * (if b = j then (1 : ℝ) else 0)) = 0 := by
          refine Finset.sum_eq_zero fun b _ => ?_
          by_cases hbj : b = j
          · subst hbj
            have hA0 : A a b = 0 := by
              dsimp [A, tridiag]
              rw [if_neg (by omega), if_neg (by omega)]
            rw [hA0, zero_mul]
          · rw [if_neg hbj, mul_zero]
        rw [h_inner_zero, mul_zero]
    have h_dot2 : dotProduct d.ofLp (A.mulVec y.ofLp) = 0 := by
      dsimp [d, dotProduct, Matrix.mulVec]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hbj : b = j
      · subst hbj
        have h_inner_zero : (∑ a : Fin n, A b a * y.ofLp a) = 0 := by
          refine Finset.sum_eq_zero fun a _ => ?_
          by_cases ha : s ≤ (a : ℕ) + 1
          · rw [hy a ha, mul_zero]
          · have hA0 : A b a = 0 := by
              dsimp [A, tridiag]
              rw [if_neg (by omega), if_neg (by omega)]
            rw [hA0, zero_mul]
        rw [h_inner_zero, mul_zero]
      · rw [if_neg hbj, zero_mul]
    have h_eq := fK_directional_deriv hg y d
    rw [h_gy_j, h_dot1, h_dot2, h_d_e1] at h_eq
    linarith
  have h_span_all : ∀ s : ℕ, 1 ≤ s → x s ∈ Submodule.span ℝ (basisVec n '' Set.Ico 1 s) := by
    intro s hs
    induction s using Nat.strong_induction_on with
    | h s ih =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hs
      rcases m with _ | m
      · rw [hx.1]
        exact Submodule.zero_mem _
      · have hx_next := hx.2 (m + 1)
        refine Submodule.span_le.mpr ?_ hx_next
        rintro _ ⟨r, ⟨hr1, hrm⟩, rfl⟩
        have hxr := ih r (by omega) hr1
        have hgr := hg_step r hr1 (x r) hxr
        have h_sub : basisVec n '' Set.Ico 1 (r + 1) ⊆ basisVec n '' Set.Ico 1 (m + 1 + 1) :=
          Set.image_mono (Set.Ico_subset_Ico_right (by omega))
        exact Submodule.span_mono h_sub hgr
  refine ⟨h_span_all, fun s hs1 hst => ?_⟩
  have hxs := (mem_span_basisVec_Ico_iff s (x s)).mp (h_span_all s hs1)
  have h_coord : ∀ i ∈ Finset.Icc s n, coord (x s) i = 0 := by
    intro i hi
    rcases Finset.mem_Icc.mp hi with ⟨his, hin⟩
    dsimp [coord]
    split_ifs with h
    · exact hxs ⟨i - 1, by omega⟩ (by simp; omega)
    · rfl
  have h_quad : quadForm (tridiag n (2 * t + 1)) (x s) = quadForm (tridiag n s) (x s) := by
    dsimp [quadForm, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : s ≤ (a : ℕ) + 1
    · rw [hxs a ha, zero_mul, zero_mul]
    · congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : s ≤ (b : ℕ) + 1
      · rw [hxs b hb, mul_zero, mul_zero]
      · congr 1
        dsimp [tridiag]
        have h1 : ((a : ℕ) = (b : ℕ) ∧ (a : ℕ) < 2 * t + 1) ↔
            ((a : ℕ) = (b : ℕ) ∧ (a : ℕ) < s) := by omega
        have h2 : (((b : ℕ) + 1 = (a : ℕ) ∨ (b : ℕ) = (a : ℕ) + 1) ∧
              (a : ℕ) < 2 * t + 1 ∧ (b : ℕ) ≠ 2 * t + 1) ↔
            (((b : ℕ) + 1 = (a : ℕ) ∨ (b : ℕ) = (a : ℕ) + 1) ∧
              (a : ℕ) < s ∧ (b : ℕ) ≠ s) := by omega
        by_cases hc1 : (a : ℕ) = (b : ℕ) ∧ (a : ℕ) < s
        · rw [if_pos (h1.mpr hc1), if_pos hc1]
        · rw [if_neg (mt h1.mp hc1), if_neg hc1]
          by_cases hc2 : ((b : ℕ) + 1 = (a : ℕ) ∨ (b : ℕ) = (a : ℕ) + 1) ∧
              (a : ℕ) < s ∧ (b : ℕ) ≠ s
          · rw [if_pos (h2.mpr hc2), if_pos hc2]
          · rw [if_neg (mt h2.mp hc2), if_neg hc2]
  refine ⟨h_coord, h_quad, ?_⟩
  dsimp [fK]
  rw [h_quad]
