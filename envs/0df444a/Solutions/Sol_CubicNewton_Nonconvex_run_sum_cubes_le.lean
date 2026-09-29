-- Prove2me | solution 1 for CubicNewton.Nonconvex.run_sum_cubes_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:45:10.241488+00:00
-- url     : https://prove2.me/submissions/d367e059-7242-44bd-a7bf-db7570ebbd4b

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

open CubicNewton.Shared

lemma aux_rsc_model_line {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x h : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    cubicModel g H M x (x + t • h) =
      t * ⟪g x, h⟫ + (1 / 2) * (t ^ 2 * ⟪H x h, h⟫) + M / 6 * (|t| ^ 3 * ‖h‖ ^ 3) := by
  unfold cubicModel
  simp only [add_sub_cancel_left, map_smul, real_inner_smul_left, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow]
  ring

lemma aux_rsc_model_decrease {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n)) (hT : IsCubicStep g H M x T) :
    cubicModel g H M x T ≤ -(M / 12) * ‖T - x‖ ^ 3 := by
  set h := T - x with hh
  have hxT : T = x + (1 : ℝ) • h := by simp [h]
  set a := ⟪g x, h⟫ with ha_def
  set b := ⟪H x h, h⟫ with hb_def
  set c := M / 6 * ‖h‖ ^ 3 with hc_def
  have hφ : ∀ t : ℝ, cubicModel g H M x (x + t • h) =
      t * a + (1 / 2) * (t ^ 2 * b) + M / 6 * (|t| ^ 3 * ‖h‖ ^ 3) :=
    fun t => aux_rsc_model_line g H M x h t
  have h1 : cubicModel g H M x T = a + (1 / 2) * b + c := by
    rw [hxT, hφ]; simp only [abs_one, one_pow, one_mul, hc_def]
  have hmin : ∀ t : ℝ,
      a + (1 / 2) * b + c ≤ t * a + (1 / 2) * (t ^ 2 * b) + M / 6 * (|t| ^ 3 * ‖h‖ ^ 3) := by
    intro t; rw [← h1, ← hφ]; exact hT _
  have ha : a ≤ 0 := by
    have := hmin (-1)
    simp only [abs_neg, abs_one, one_pow, one_mul, neg_one_sq, neg_mul] at this
    linarith
  have hBt : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a + b / 2 * (t + 1) + c * (t ^ 2 + t + 1) ≤ 0 := by
    intro t ht
    have := hmin t
    rw [abs_of_pos ht.1] at this
    have key : 0 ≤ (t - 1) * (a + b / 2 * (t + 1) + c * (t ^ 2 + t + 1)) := by
      rw [hc_def]; linear_combination this
    nlinarith [ht.2]
  have hB : a + b + 3 * c ≤ 0 := by
    have hcont : Continuous (fun t : ℝ => a + b / 2 * (t + 1) + c * (t ^ 2 + t + 1)) := by
      fun_prop
    have htend : Filter.Tendsto (fun t : ℝ => a + b / 2 * (t + 1) + c * (t ^ 2 + t + 1))
        (nhdsWithin 1 (Set.Iio 1)) (nhds (a + b / 2 * (1 + 1) + c * (1 ^ 2 + 1 + 1))) :=
      (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Iio 1),
        a + b / 2 * (t + 1) + c * (t ^ 2 + t + 1) ≤ 0 :=
      Filter.mem_of_superset (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)) hBt
    have := le_of_tendsto htend hev
    linarith
  rw [h1]
  have : -(M / 12) * ‖h‖ ^ 3 = -c / 2 := by rw [hc_def]; ring
  rw [this]
  linarith

end CubicNewton.Nonconvex

open CubicNewton.Nonconvex
open scoped RealInnerProductSpace

theorem solution {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (L₀ : ℝ) (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L)
    (fstar : ℝ) (hfstar : ∀ y ∈ F, fstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    Summable (fun i => ‖x i - x (i + 1)‖ ^ 3) ∧
      ∑' i, ‖x i - x (i + 1)‖ ^ 3 ≤ 12 / L₀ * (f x₀ - fstar) := by
  have hdec : ∀ k, f (x (k + 1)) ≤ f (x k) - L₀ / 12 * ‖x k - x (k + 1)‖ ^ 3 := by
    intro k
    have h1 := hrun.accept k
    have h2 := aux_rsc_model_decrease g H (M k) (x k) (x (k + 1)) (hrun.step k)
    have h3 := (hrun.param_mem k).1
    rw [norm_sub_rev] at h2
    have h4 : 0 ≤ ‖x k - x (k + 1)‖ ^ 3 := by positivity
    nlinarith
  have hmono : ∀ k, f (x k) ≤ f x₀ := by
    intro k
    induction k with
    | zero => rw [hrun.init]
    | succ k ih =>
      have := hdec k
      have : 0 ≤ ‖x k - x (k + 1)‖ ^ 3 := by positivity
      nlinarith
  have hlow : ∀ k, fstar ≤ f (x k) := fun k => hfstar _ (interior_subset (hlevel (hmono k)))
  have hsum : ∀ N, ∑ i ∈ Finset.range N, ‖x i - x (i + 1)‖ ^ 3 ≤ 12 / L₀ * (f x₀ - f (x N)) := by
    intro N
    induction N with
    | zero => simp [hrun.init]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hd := hdec N
      have hstep : ‖x N - x (N + 1)‖ ^ 3 ≤ 12 / L₀ * (f (x N) - f (x (N + 1))) := by
        calc ‖x N - x (N + 1)‖ ^ 3 = 12 / L₀ * (L₀ / 12 * ‖x N - x (N + 1)‖ ^ 3) := by
              field_simp
          _ ≤ 12 / L₀ * (f (x N) - f (x (N + 1))) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have : 12 / L₀ * (f x₀ - f (x N)) + 12 / L₀ * (f (x N) - f (x (N + 1))) =
          12 / L₀ * (f x₀ - f (x (N + 1))) := by ring
      linarith
  have hbound : ∀ N, ∑ i ∈ Finset.range N, ‖x i - x (i + 1)‖ ^ 3 ≤ 12 / L₀ * (f x₀ - fstar) := by
    intro N
    refine (hsum N).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hlow N]) (by positivity)
  have hnn : ∀ i, 0 ≤ ‖x i - x (i + 1)‖ ^ 3 := fun i => by positivity
  exact ⟨summable_of_sum_range_le hnn hbound, Real.tsum_le_of_sum_range_le hnn hbound⟩
