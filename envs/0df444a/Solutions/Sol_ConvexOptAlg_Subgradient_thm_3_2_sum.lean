-- Prove2me | solution 1 for ConvexOptAlg.Subgradient.thm_3_2_sum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T18:52:15.407321+00:00
-- url     : https://prove2.me/submissions/6e06b13f-6e16-4901-965f-83c70c671bb7

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_Subgradient_Defs
import Theorems.Thm_ConvexOptimization_projection_iff_obtuse_angle

open ConvexOptAlg.Subgradient
open scoped RealInnerProductSpace

namespace CvxAux

theorem proj_sq {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXconv : Convex ℝ X)
    (x y p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X)
    (hp : OnlineConvexOpt.FirstOrder.IsMetricProjection X y p) :
    ‖p - x‖ ^ 2 + ‖y - p‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
  have hvar : ⟪y - p, x - p⟫ ≤ 0 :=
    (ConvexOptimization.projection_iff_obtuse_angle X hXconv y p hp.1).mp
      (fun w hw => by simpa [dist_eq_norm] using hp.2 w hw) x hx
  have h1 : y - x = (y - p) + (p - x) := by abel
  have h2 : ⟪y - p, p - x⟫ = -⟪y - p, x - p⟫ := by
    rw [← inner_neg_right]; congr 1; abel
  have h3 : ‖y - x‖ ^ 2 = ‖y - p‖ ^ 2 + 2 * ⟪y - p, p - x⟫ + ‖p - x‖ ^ 2 := by
    rw [h1, norm_add_sq_real]
  rw [h3, h2]
  nlinarith [hvar]

theorem step_ineq {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (η : ℕ → ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (T : ℕ) (hrun : IsProjSubgradRun X f η x g T) (xstar : EuclideanSpace ℝ (Fin n))
    (hxstar : xstar ∈ X) (s : ℕ) (hs1 : 1 ≤ s) (hsT : s ≤ T) (hη : 0 < η s) :
    f (x s) - f xstar ≤
      1 / (2 * η s) * (‖x s - xstar‖ ^ 2 - ‖(x s - η s • g s) - xstar‖ ^ 2)
        + η s / 2 * ‖g s‖ ^ 2 := by
  have hsub := (hrun.2 s hs1 hsT).1 xstar hxstar
  have hexp : ‖(x s - η s • g s) - xstar‖ ^ 2 =
      ‖x s - xstar‖ ^ 2 - 2 * η s * ⟪g s, x s - xstar⟫ + η s ^ 2 * ‖g s‖ ^ 2 := by
    have : (x s - η s • g s) - xstar = (x s - xstar) - η s • g s := by abel
    rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm]
    ring
  have key : 1 / (2 * η s) * (‖x s - xstar‖ ^ 2 - ‖(x s - η s • g s) - xstar‖ ^ 2)
      + η s / 2 * ‖g s‖ ^ 2 = ⟪g s, x s - xstar⟫ := by
    rw [hexp]
    field_simp
    ring
  rw [key]
  exact hsub

theorem sum_bound {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXconv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (R L η : ℝ) (hη : 0 < η) (t : ℕ)
    (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : IsProjSubgradRun X f (fun _ => η) x g t)
    (hball : X ⊆ Metric.closedBall (x 1) R)
    (hL : ∀ s, 1 ≤ s → s ≤ t → ‖g s‖ ≤ L)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) :
    ∑ s ∈ Finset.Icc 1 t, (f (x s) - f xstar) ≤
      R ^ 2 / (2 * η) + η * L ^ 2 * (t : ℝ) / 2 := by
  have hper : ∀ s, 1 ≤ s → s ≤ t → f (x s) - f xstar ≤
      1 / (2 * η) * (‖x s - xstar‖ ^ 2 - ‖x (s + 1) - xstar‖ ^ 2) + η / 2 * L ^ 2 := by
    intro s hs1 hst
    have h1 := step_ineq X f (fun _ => η) x g t hrun xstar hxstar s hs1 hst hη
    have h2 := proj_sq X hXconv xstar (x s - η • g s) (x (s + 1)) hxstar (hrun.2 s hs1 hst).2
    have h3 : ‖g s‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hL s hs1 hst) 2
    have h4 : ‖x (s + 1) - xstar‖ ^ 2 ≤ ‖(x s - η • g s) - xstar‖ ^ 2 := by
      nlinarith [sq_nonneg ‖(x s - η • g s) - x (s + 1)‖]
    have hη2 : 0 < 1 / (2 * η) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 hη2.le, mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ η / 2)]
  have hind : ∀ t' : ℕ, t' ≤ t → ∑ s ∈ Finset.Icc 1 t', (f (x s) - f xstar) ≤
      1 / (2 * η) * (‖x 1 - xstar‖ ^ 2 - ‖x (t' + 1) - xstar‖ ^ 2) + (t' : ℝ) * (η / 2 * L ^ 2) := by
    intro t'
    induction t' with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [Finset.sum_Icc_succ_top (by omega)]
      have := ih (by omega)
      have h5 := hper (k + 1) (by omega) hk
      push_cast
      nlinarith
  have hfin := hind t le_rfl
  have hx1 : ‖x 1 - xstar‖ ≤ R := by
    have := hball hxstar
    rw [Metric.mem_closedBall, dist_eq_norm] at this
    rwa [norm_sub_rev]
  have hx1sq : ‖x 1 - xstar‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx1 2
  have hnn : 0 ≤ ‖x (t + 1) - xstar‖ ^ 2 := by positivity
  have hη2 : 0 < 1 / (2 * η) := by positivity
  have : 1 / (2 * η) * (‖x 1 - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2) ≤ R ^ 2 / (2 * η) := by
    have := mul_le_mul_of_nonneg_left (by linarith : ‖x 1 - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2 ≤ R ^ 2) hη2.le
    simpa [div_eq_mul_inv, mul_comm] using this
  have e : (t : ℝ) * (η / 2 * L ^ 2) = η * L ^ 2 * (t : ℝ) / 2 := by ring
  linarith

end CvxAux

theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXcpt : IsCompact X) (hXconv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ X f)
    (R L η : ℝ) (hR : 0 < R) (hη : 0 < η) (t : ℕ)
    (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : IsProjSubgradRun X f (fun _ => η) x g t)
    (hball : X ⊆ Metric.closedBall (x 1) R)
    (hL : ∀ s, 1 ≤ s → s ≤ t → ‖g s‖ ≤ L)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y) :
    ∑ s ∈ Finset.Icc 1 t, (f (x s) - f xstar) ≤
      R ^ 2 / (2 * η) + η * L ^ 2 * (t : ℝ) / 2 :=
  CvxAux.sum_bound X hXconv f R L η hη t x g hrun hball hL xstar hxstar
