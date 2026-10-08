-- Prove2me | solution 1 for ConvexOptAlg.Subgradient.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T18:52:16.542448+00:00
-- url     : https://prove2.me/submissions/fdb6246b-0bc2-499a-9978-4e716b461dc6

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
    (R L : ℝ) (hR : 0 < R) (hLpos : 0 < L) (t : ℕ) (ht : 1 ≤ t)
    (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : IsProjSubgradRun X f (fun _ => R / (L * Real.sqrt t)) x g t)
    (hball : X ⊆ Metric.closedBall (x 1) R)
    (hL : ∀ s, 1 ≤ s → s ≤ t → ‖g s‖ ≤ L)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y) :
    f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s) - f xstar ≤ R * L / Real.sqrt t := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  have hη : 0 < R / (L * Real.sqrt t) := by positivity
  have hsum := CvxAux.sum_bound X hXconv f R L (R / (L * Real.sqrt t)) hη t x g hrun hball hL
    xstar hxstar
  -- the right side equals R L √t
  have hsqsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt htpos.le
  have hrhs : R ^ 2 / (2 * (R / (L * Real.sqrt t))) + R / (L * Real.sqrt t) * L ^ 2 * (t : ℝ) / 2
      = R * L * Real.sqrt t := by
    field_simp
    nlinarith [hsqsq]
  rw [hrhs] at hsum
  -- all iterates lie in X
  have hmem : ∀ s, 1 ≤ s → s ≤ t → x s ∈ X := by
    intro s hs1 hst
    induction s, hs1 using Nat.le_induction with
    | base => exact hrun.1
    | succ k hk ih =>
      exact (hrun.2 k hk (by omega)).2.1
  -- Jensen
  have hjen : f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s) ≤
      ∑ s ∈ Finset.Icc 1 t, (1 / (t : ℝ)) • f (x s) := by
    have := hf.map_sum_le (t := Finset.Icc 1 t) (w := fun _ => 1 / (t : ℝ))
      (p := fun s => x s) (fun _ _ => by positivity)
      (by simp [Finset.sum_const, Nat.card_Icc]; field_simp)
      (fun s hs => hmem s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2)
    rwa [← Finset.smul_sum] at this
  have hcard : ∑ s ∈ Finset.Icc 1 t, (1 / (t : ℝ)) • f (x s) =
      (1 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, f (x s) := by
    simp [Finset.mul_sum]
  have hsplit : ∑ s ∈ Finset.Icc 1 t, (f (x s) - f xstar) =
      ∑ s ∈ Finset.Icc 1 t, f (x s) - (t : ℝ) * f xstar := by
    simp [Finset.sum_sub_distrib]
  have hfin : f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s) - f xstar ≤
      (1 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, (f (x s) - f xstar) := by
    rw [hsplit]
    have : (1 / (t : ℝ)) * (∑ s ∈ Finset.Icc 1 t, f (x s) - (t : ℝ) * f xstar) =
        (1 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, f (x s) - f xstar := by
      field_simp
    rw [this]
    linarith
  have hlast : (1 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, (f (x s) - f xstar) ≤
      (1 / (t : ℝ)) * (R * L * Real.sqrt t) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have hend : (1 / (t : ℝ)) * (R * L * Real.sqrt t) = R * L / Real.sqrt t := by
    field_simp
    nlinarith [hsqsq]
  linarith
