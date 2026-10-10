-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.inner_polar_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:44.782886+00:00
-- url     : https://prove2.me/submissions/ada1d198-4d3b-4bc7-b883-c8d5593cde48

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.inner_polar_bound
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E} {r : ℝ} (h : NumRadiusLE A r) (x y : E) :
    ‖(⟪A y, x⟫_ℂ)‖ ≤ r * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by

  have hQ : ∀ u : E, ‖(⟪A u, u⟫_ℂ)‖ ≤ r * ‖u‖ ^ 2 := by
    intro u
    have hcs : (⟪A u, u⟫_ℂ) = (starRingEnd ℂ) (⟪u, A u⟫_ℂ) := (inner_conj_symm _ _).symm
    rw [hcs, RCLike.norm_conj]
    exact h u
  have key := inner_map_polarization (A : E →ₗ[ℂ] E) x y
  simp only [ContinuousLinearMap.coe_coe] at key
  rw [key]
  have e1 : ‖(⟪A (x + y), x + y⟫_ℂ)‖ ≤ r * ‖x + y‖ ^ 2 := hQ _
  have e2 : ‖(⟪A (x - y), x - y⟫_ℂ)‖ ≤ r * ‖x - y‖ ^ 2 := hQ _
  have e3 : ‖(⟪A (x + Complex.I • y), x + Complex.I • y⟫_ℂ)‖
      ≤ r * ‖x + Complex.I • y‖ ^ 2 := hQ _
  have e4 : ‖(⟪A (x - Complex.I • y), x - Complex.I • y⟫_ℂ)‖
      ≤ r * ‖x - Complex.I • y‖ ^ 2 := hQ _
  have hpar1 : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    simpa [pow_two] using parallelogram_law_with_norm ℂ x y
  have hpar2 : ‖x + Complex.I • y‖ ^ 2 + ‖x - Complex.I • y‖ ^ 2
      = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    simpa [pow_two, norm_smul] using parallelogram_law_with_norm ℂ x (Complex.I • y)
  have hdiv : ∀ a b c d : ℂ, ‖(a - b + Complex.I * c - Complex.I * d) / 4‖
      ≤ (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) / 4 := by
    intro a b c d
    rw [norm_div]
    simp only [Complex.norm_ofNat]
    gcongr
    calc ‖a - b + Complex.I * c - Complex.I * d‖
        ≤ ‖a - b + Complex.I * c‖ + ‖Complex.I * d‖ := norm_sub_le _ _
      _ ≤ (‖a - b‖ + ‖Complex.I * c‖) + ‖Complex.I * d‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖a‖ + ‖b‖) + ‖Complex.I * c‖) + ‖Complex.I * d‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by simp
  refine le_trans (hdiv _ _ _ _) ?_
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4)]
  have hr1 : r * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) = r * (2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) := by rw [hpar1]
  have hr2 : r * (‖x + Complex.I • y‖ ^ 2 + ‖x - Complex.I • y‖ ^ 2)
      = r * (2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) := by rw [hpar2]
  nlinarith [e1, e2, e3, e4, hr1, hr2]
