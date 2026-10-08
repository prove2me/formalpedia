-- Prove2me | solution 1 for ConvexOptimization.newton_quadratic_phase_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T10:02:07.338491+00:00
-- url     : https://prove2.me/submissions/690e6f0c-7070-40ef-92ad-6cf5af728674

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

theorem gradient_remainder_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : ℝ) (hL : 0 ≤ L)
    (g : E → E) (H : E → E →L[ℝ] E)
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (hHL : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x d : E) :
    ‖g (x + d) - g x - H x d‖ ≤ L / 2 * ‖d‖ ^ 2 := by
  have hHlip : LipschitzWith ⟨L, hL⟩ H := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro u v
    rw [dist_eq_norm, dist_eq_norm]
    exact hHL u v
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hgline (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ g (x + s • d)) (H (x + t • d) d) t := by
    simpa [Function.comp_def] using
      (hH (x + t • d)).comp_hasDerivAt t (hline t)
  have hqderiv (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ g (x + s • d) - g x - s • H x d)
        ((H (x + t • d) - H x) d) t := by
    exact (((hgline t).sub_const (g x)).sub ((hasDerivAt_id t).smul_const (H x d))).congr_deriv
      (by simp [ContinuousLinearMap.sub_apply])
  have hlinecont : Continuous (fun t : ℝ ↦ x + t • d) := by fun_prop
  have hremcont : Continuous (fun t : ℝ ↦ (H (x + t • d) - H x) d) := by
    exact ((hHlip.continuous.comp hlinecont).sub continuous_const).clm_apply continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (fun t _ ↦ hqderiv t) (hremcont.intervalIntegrable 0 1)
  have hid :
      g (x + d) - g x - H x d =
        ∫ t : ℝ in 0..1, (H (x + t • d) - H x) d := by
    simpa using hFTC.symm
  calc
    ‖g (x + d) - g x - H x d‖ =
        ‖∫ t : ℝ in 0..1, (H (x + t • d) - H x) d‖ := congrArg norm hid
    _ ≤ ∫ t : ℝ in 0..1, L * t * ‖d‖ ^ 2 := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · filter_upwards [] with t ht
        calc
          ‖(H (x + t • d) - H x) d‖ ≤ ‖H (x + t • d) - H x‖ * ‖d‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ ≤ (L * ‖(x + t • d) - x‖) * ‖d‖ :=
            mul_le_mul_of_nonneg_right (hHL (x + t • d) x) (norm_nonneg d)
          _ = L * t * ‖d‖ ^ 2 := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
            ring
      · exact (by fun_prop : Continuous (fun t : ℝ ↦ L * t * ‖d‖ ^ 2)).intervalIntegrable 0 1
    _ = L / 2 * ‖d‖ ^ 2 := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
      ring

theorem objective_second_order_remainder_upper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (L : ℝ) (hL : 0 ≤ L)
    (f : E → ℝ) (g : E → E) (H : E → E →L[ℝ] E)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (hHL : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x d : E) :
    f (x + d) - f x - ⟪g x, d⟫ - (1 / 2 : ℝ) * ⟪H x d, d⟫ ≤
      L / 6 * ‖d‖ ^ 3 := by
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hfline (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ f (x + s • d)) ⟪g (x + t • d), d⟫ t := by
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using
      (hg (x + t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
  let q : ℝ → ℝ := fun t ↦
    f (x + t • d) - f x - t * ⟪g x, d⟫ - t ^ 2 / 2 * ⟪H x d, d⟫
  let q' : ℝ → ℝ := fun t ↦
    ⟪g (x + t • d), d⟫ - ⟪g x, d⟫ - t * ⟪H x d, d⟫
  have hqderiv (t : ℝ) : HasDerivAt q (q' t) t := by
    dsimp [q, q']
    exact ((((hfline t).sub_const (f x)).sub
      ((hasDerivAt_id t).mul_const ⟪g x, d⟫)).sub
        (((hasDerivAt_id t).pow 2).div_const 2 |>.mul_const ⟪H x d, d⟫)).congr_deriv
      (by (try simp only [id_eq]); ring)
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr fun z ↦ (hH z).continuousAt
  have hq'cont : Continuous q' := by
    dsimp [q']
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (fun t _ ↦ hqderiv t) (hq'cont.intervalIntegrable 0 1)
  have hid :
      f (x + d) - f x - ⟪g x, d⟫ - (1 / 2 : ℝ) * ⟪H x d, d⟫ =
        ∫ t : ℝ in 0..1, q' t := by
    simpa [q] using hFTC.symm
  calc
    f (x + d) - f x - ⟪g x, d⟫ - (1 / 2 : ℝ) * ⟪H x d, d⟫ =
        ∫ t : ℝ in 0..1, q' t := hid
    _ ≤ ∫ t : ℝ in 0..1, L / 2 * t ^ 2 * ‖d‖ ^ 3 := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (hq'cont.intervalIntegrable 0 1)
        ((by fun_prop : Continuous (fun t : ℝ ↦ L / 2 * t ^ 2 * ‖d‖ ^ 3)).intervalIntegrable 0 1)
      intro t ht
      have hstep := gradient_remainder_bound L hL g H hH hHL x (t • d)
      have hq'eq : q' t = ⟪g (x + t • d) - g x - t • H x d, d⟫ := by
        dsimp [q']
        simp [inner_sub_left, inner_smul_left]
      rw [hq'eq]
      calc
        ⟪g (x + t • d) - g x - t • H x d, d⟫ ≤
            ‖g (x + t • d) - g x - t • H x d‖ * ‖d‖ := real_inner_le_norm _ _
        _ ≤ (L / 2 * ‖t • d‖ ^ 2) * ‖d‖ := by
          exact mul_le_mul_of_nonneg_right (by simpa using hstep) (norm_nonneg d)
        _ = L / 2 * t ^ 2 * ‖d‖ ^ 3 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
          ring
    _ = L / 6 * ‖d‖ ^ 3 := by
      have hpow : (∫ t : ℝ in 0..1, t ^ 2) = (1 / 3 : ℝ) := by
        norm_num [integral_pow]
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, hpow]
      ring

end ConvexOptimization

theorem solution {n : ℕ} (m M L α β η : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hL : 0 < L)
    (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hη : η = min 1 (3 * (1 - 2 * α)) * m ^ 2 / L)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (hHm : ∀ x v, m * ‖v‖ ^ 2 ≤ ⟪H x v, v⟫)
    (hHM : ∀ x v, ⟪H x v, v⟫ ≤ M * ‖v‖ ^ 2)
    (hHL : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x Δ : EuclideanSpace ℝ (Fin n))
    (hΔ : H x Δ = -g x) (hgx : ‖g x‖ < η) :
    (f (x + Δ) ≤ f x + α * ⟪g x, Δ⟫) ∧
    L / (2 * m ^ 2) * ‖g (x + Δ)‖ ≤ (L / (2 * m ^ 2) * ‖g x‖) ^ 2 := by
  have hL0 : 0 ≤ L := hL.le
  have hstepgrad : m * ‖Δ‖ ≤ ‖g x‖ := by
    by_cases hzero : Δ = 0
    · simp [hzero]
    · have hnorm : 0 < ‖Δ‖ := norm_pos_iff.mpr hzero
      have hcoercive := hHm x Δ
      rw [hΔ] at hcoercive
      have hcauchy : ⟪-g x, Δ⟫ ≤ ‖g x‖ * ‖Δ‖ := by
        calc
          ⟪-g x, Δ⟫ ≤ ‖-g x‖ * ‖Δ‖ := real_inner_le_norm _ _
          _ = ‖g x‖ * ‖Δ‖ := by rw [norm_neg]
      have hmul : (m * ‖Δ‖) * ‖Δ‖ ≤ ‖g x‖ * ‖Δ‖ := by
        calc
          (m * ‖Δ‖) * ‖Δ‖ = m * ‖Δ‖ ^ 2 := by ring
          _ ≤ ⟪-g x, Δ⟫ := hcoercive
          _ ≤ ‖g x‖ * ‖Δ‖ := hcauchy
      exact le_of_mul_le_mul_right hmul hnorm
  have hstepnorm : ‖Δ‖ ≤ ‖g x‖ / m := by
    apply (le_div_iff₀ hm).2
    simpa [mul_comm] using hstepgrad
  have hminle : η ≤ 3 * (1 - 2 * α) * m ^ 2 / L := by
    rw [hη]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right 1 (3 * (1 - 2 * α))) (sq_nonneg m)) hL.le
  have hmdelta_lt : m * ‖Δ‖ < η := lt_of_le_of_lt hstepgrad hgx
  have hsmall0 : m * ‖Δ‖ < 3 * (1 - 2 * α) * m ^ 2 / L :=
    lt_of_lt_of_le hmdelta_lt hminle
  have hsmall1 : ‖Δ‖ < 3 * (1 - 2 * α) * m / L := by
    have hmul : m * ‖Δ‖ < m * (3 * (1 - 2 * α) * m / L) := by
      calc
        m * ‖Δ‖ < 3 * (1 - 2 * α) * m ^ 2 / L := hsmall0
        _ = m * (3 * (1 - 2 * α) * m / L) := by ring
    exact lt_of_mul_lt_mul_left hmul hm.le
  have hsmall2 : L * ‖Δ‖ < 3 * (1 - 2 * α) * m := by
    calc
      L * ‖Δ‖ < L * (3 * (1 - 2 * α) * m / L) :=
        mul_lt_mul_of_pos_left hsmall1 hL
      _ = 3 * (1 - 2 * α) * m := by field_simp [ne_of_gt hL]
  have hcubicCoeff : L / 6 * ‖Δ‖ ≤ (1 / 2 - α) * m := by
    linarith
  have hnewtoninner : ⟪H x Δ, Δ⟫ = -⟪g x, Δ⟫ := by
    rw [hΔ]
    simp
  have hcubic : L / 6 * ‖Δ‖ ^ 3 ≤ -(1 / 2 - α) * ⟪g x, Δ⟫ := by
    calc
      L / 6 * ‖Δ‖ ^ 3 = (L / 6 * ‖Δ‖) * ‖Δ‖ ^ 2 := by ring
      _ ≤ ((1 / 2 - α) * m) * ‖Δ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcubicCoeff (sq_nonneg ‖Δ‖)
      _ = (1 / 2 - α) * (m * ‖Δ‖ ^ 2) := by ring
      _ ≤ (1 / 2 - α) * ⟪H x Δ, Δ⟫ :=
        mul_le_mul_of_nonneg_left (hHm x Δ) (by linarith)
      _ = -(1 / 2 - α) * ⟪g x, Δ⟫ := by rw [hnewtoninner]; ring
  have hobj := ConvexOptimization.objective_second_order_remainder_upper
    L hL0 f g H hg hH hHL x Δ
  rw [hnewtoninner] at hobj
  have harmijo : f (x + Δ) ≤ f x + α * ⟪g x, Δ⟫ := by
    linarith
  have hgradrem := ConvexOptimization.gradient_remainder_bound
    L hL0 g H hH hHL x Δ
  rw [hΔ] at hgradrem
  have hgradnew : ‖g (x + Δ)‖ ≤ L / 2 * ‖Δ‖ ^ 2 := by
    simpa using hgradrem
  have hdivnonneg : 0 ≤ ‖g x‖ / m := div_nonneg (norm_nonneg _) hm.le
  have hsquares : ‖Δ‖ ^ 2 ≤ (‖g x‖ / m) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hdivnonneg).2 hstepnorm
  have hgradnew' : ‖g (x + Δ)‖ ≤ L / 2 * (‖g x‖ / m) ^ 2 := by
    calc
      ‖g (x + Δ)‖ ≤ L / 2 * ‖Δ‖ ^ 2 := hgradnew
      _ ≤ L / 2 * (‖g x‖ / m) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquares (div_nonneg hL.le (by norm_num))
  constructor
  · exact harmijo
  · calc
      L / (2 * m ^ 2) * ‖g (x + Δ)‖ ≤
          L / (2 * m ^ 2) * (L / 2 * (‖g x‖ / m) ^ 2) :=
        mul_le_mul_of_nonneg_left hgradnew'
          (div_nonneg hL.le (mul_nonneg (by norm_num) (sq_nonneg m)))
      _ = (L / (2 * m ^ 2) * ‖g x‖) ^ 2 := by
        field_simp [ne_of_gt hm]
