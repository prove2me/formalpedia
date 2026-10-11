-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.rademacherMean_scaledDot_sq_of_unit_entries
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:22:47.017986+00:00
-- url     : https://prove2.me/submissions/44b200d7-f012-4f93-8e1d-6c69b082d8bb

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.rademacherMean_scaledDot_sq_of_unit_entries
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
import Theorems.Thm_BookProof_ChapterScaledDotProduct_rademacherMean_dot_sq_of_unit_entries
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterScaledDotProduct



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (hd : 0 < d) {k : Fin d → ℝ}
    (hk : ∀ i, (k i) ^ 2 = 1) :
    rademacherMean (fun x => (scaledDot (signVec x) k) ^ 2) = 1 := by

  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hs : Real.sqrt d ≠ 0 := by positivity
  have hsq : (Real.sqrt d) ^ 2 = (d : ℝ) := Real.sq_sqrt hdpos.le
  have hrw : ∀ x : (Fin d → Bool), (scaledDot (signVec x) k) ^ 2
      = (dot (signVec x) k) ^ 2 / (d : ℝ) := by
    intro x
    rw [scaledDot, div_pow, hsq]
  have hsum : ∑ x : (Fin d → Bool), (scaledDot (signVec x) k) ^ 2
      = (∑ x : (Fin d → Bool), (dot (signVec x) k) ^ 2) / (d : ℝ) := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hrw x, Finset.sum_div]
  have hmean := rademacherMean_dot_sq_of_unit_entries hk
  rw [rademacherMean] at hmean ⊢
  rw [hsum, div_div, mul_comm, ← div_div, hmean]
  field_simp
