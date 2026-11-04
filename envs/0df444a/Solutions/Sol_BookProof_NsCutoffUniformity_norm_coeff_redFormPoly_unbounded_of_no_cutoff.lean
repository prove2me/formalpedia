-- Prove2me | solution 1 for BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_unbounded_of_no_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T02:07:28.815197+00:00
-- url     : https://prove2.me/submissions/3b862ca9-33f6-4663-811e-f997b6f89d83

-- Generated from ChapterNsCutoffUniformity.lean — solution of BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_unbounded_of_no_cutoff
import Mathlib
import Definitions.Def_ChapterNsCutoffUniformity
import Definitions.Def_ChapterNavierStokesFullEulerianFock
open BookProof.NsCutoffUniformity




open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

variable {n : ℕ}
variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (nu : ℝ) (C₀ : ℝ) :
    ∃ (k : Fin 3 → ℝ) (m : Fin (1 * 6) →₀ ℕ) (p : Fin 1) (r : Fin 7),
      C₀ < ‖coeff m (redFormPoly nu k 1 p r)‖ := by

  obtain ⟨t, ht⟩ := exists_gt (max C₀ 0)
  have ht0 : 0 < t := lt_of_le_of_lt (le_max_right C₀ 0) ht
  refine ⟨fun j => if j = 0 then t else 0, Finsupp.single (ruIdx (0 : Fin 1) 0) 1, 0,
    divIdx7, ?_⟩
  rw [redFormPoly_div, redMomentumPoly, coeff_sum]
  have hval : ∀ j : Fin 3,
      coeff (Finsupp.single (ruIdx (0 : Fin 1) 0) 1)
        (C (((if j = 0 then t else 0 : ℝ)) : ℂ) * X (ruIdx (0 : Fin 1) j))
        = if j = 0 then (t : ℂ) else 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      rw [coeff_C_mul, coeff_X']
      simp
    · rw [coeff_C_mul]
      simp [hj]
  rw [Finset.sum_congr rfl fun j _ => hval j, Finset.sum_ite_eq' Finset.univ (0 : Fin 3)
    (fun _ => (t : ℂ))]
  simp only [Finset.mem_univ, if_true, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  exact lt_of_le_of_lt (le_max_left C₀ 0) ht
