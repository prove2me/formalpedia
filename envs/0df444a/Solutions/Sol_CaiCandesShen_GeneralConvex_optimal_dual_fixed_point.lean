-- Prove2me | solution 1 for CaiCandesShen.GeneralConvex.optimal_dual_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:51:54.280537+00:00
-- url     : https://prove2.me/submissions/b905e920-80f8-4f03-b9ec-50339a1c3fc5

import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Problem

namespace CaiCandesShen.GeneralConvex

theorem aux_odfp_dot_single {m : ℕ} (ys v : Fin m → ℝ) (i : Fin m) (c : ℝ) :
    dot (ys + Pi.single i c) v = dot ys v + c * v i := by
  unfold dot
  simp [add_mul, Finset.sum_add_distrib, Pi.single_apply]

theorem aux_odfp_key {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ) (Xs : Mat n₁ n₂)
    (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys) (i : Fin m) (c : ℝ)
    (hc : 0 ≤ ys i + c) : c * constraintMap f Xs i ≤ 0 := by
  obtain ⟨hy0, hsad, -⟩ := hopt
  have hnn : ∀ j, 0 ≤ (ys + Pi.single i c : Fin m → ℝ) j := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hc
    · simp [hj, hy0 j]
  have h := hsad _ hnn
  unfold lagr at h
  rw [aux_odfp_dot_single] at h
  linarith

end CaiCandesShen.GeneralConvex

open CaiCandesShen.GeneralConvex

theorem solution {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ i : Fin m, ys i = max (ys i + δ * constraintMap f Xs i) 0 := by
  intro i
  have hy : 0 ≤ ys i := hopt.1 i
  have h1 := aux_odfp_key τ f Xs ys hopt i 1 (by linarith)
  have h2 := aux_odfp_key τ f Xs ys hopt i (-ys i) (by linarith)
  have hF : constraintMap f Xs i ≤ 0 := by linarith
  rcases hy.eq_or_lt with h | h
  · rw [← h]
    have : δ * constraintMap f Xs i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ.le hF
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
