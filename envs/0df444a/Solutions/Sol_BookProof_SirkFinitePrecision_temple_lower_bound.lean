-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.temple_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:20:02.086091+00:00
-- url     : https://prove2.me/submissions/30ad864c-e3bc-4ab9-b4ed-805f489227ab

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.temple_lower_bound
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
import Theorems.Thm_BookProof_SirkFinitePrecision_norm_sq_eq_sum_repr
import Theorems.Thm_BookProof_SirkFinitePrecision_rayleigh_eq_sum_eigenvalues
import Theorems.Thm_BookProof_SirkFinitePrecision_norm_apply_sq_eq_sum_eigenvalues
open BookProof.SirkFinitePrecision







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : ‖x‖ = 1) {lam0 β : ℝ}
    (hsep : ∀ i, hT.eigenvalues hn i = lam0 ∨ β ≤ hT.eigenvalues hn i)
    (hlow : ∀ i, lam0 ≤ hT.eigenvalues hn i)
    (hβ : rayleigh T x < β) :
    rayleigh T x - (‖T x‖ ^ 2 - rayleigh T x ^ 2) / (β - rayleigh T x) ≤ lam0 := by

  classical
  have hpar : (1 : ℝ) = ∑ i, ‖coeff hT hn x i‖ ^ 2 := by
    rw [← norm_sq_eq_sum_repr hT hn x, hx]; norm_num
  have hquad : 0 ≤ ∑ i, (hT.eigenvalues hn i - lam0) * (hT.eigenvalues hn i - β)
      * ‖coeff hT hn x i‖ ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro i _
    have hcoord : (0 : ℝ) ≤ ‖coeff hT hn x i‖ ^ 2 := by positivity
    rcases hsep i with h | h
    · rw [h]; simp
    · have h0 : 0 ≤ hT.eigenvalues hn i - lam0 := by linarith [hlow i]
      have h1 : 0 ≤ hT.eigenvalues hn i - β := by linarith
      exact mul_nonneg (mul_nonneg h0 h1) hcoord
  have hexp : ∑ i, (hT.eigenvalues hn i - lam0) * (hT.eigenvalues hn i - β)
      * ‖coeff hT hn x i‖ ^ 2
      = ‖T x‖ ^ 2 - (lam0 + β) * rayleigh T x + lam0 * β := by
    have hsplit : ∑ i, (hT.eigenvalues hn i - lam0) * (hT.eigenvalues hn i - β)
        * ‖coeff hT hn x i‖ ^ 2
        = (∑ i, hT.eigenvalues hn i ^ 2 * ‖coeff hT hn x i‖ ^ 2)
          - (lam0 + β) * (∑ i, hT.eigenvalues hn i * ‖coeff hT hn x i‖ ^ 2)
          + lam0 * β * (∑ i, ‖coeff hT hn x i‖ ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, ← norm_apply_sq_eq_sum_eigenvalues hT hn x,
      ← rayleigh_eq_sum_eigenvalues hT hn x, ← hpar, mul_one]
  rw [hexp] at hquad
  have hβθ : 0 < β - rayleigh T x := by linarith
  have hdiv : rayleigh T x - lam0
      ≤ (‖T x‖ ^ 2 - rayleigh T x ^ 2) / (β - rayleigh T x) := by
    rw [le_div_iff₀ hβθ]
    nlinarith [hquad]
  linarith
