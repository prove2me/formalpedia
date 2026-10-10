-- Prove2me | solution 1 for BookProof.ChapterEulerNState.exists_theta_tailProd
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:02:13.535308+00:00
-- url     : https://prove2.me/submissions/c43b7147-4d4b-4165-ab32-e611ba3bc13c

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.exists_theta_tailProd
import Mathlib
import Definitions.Def_ChapterEulerNState
import Theorems.Thm_BookProof_ChapterEulerNState_exists_sin_sq
import Theorems.Thm_BookProof_ChapterEulerNState_tailProd_succ
import Theorems.Thm_BookProof_ChapterEulerNState_tailSum_zero_eq
import Theorems.Thm_BookProof_ChapterEulerNState_tailSum_succ
import Theorems.Thm_BookProof_ChapterEulerNState_tailSum_nonneg
open BookProof.ChapterEulerNState



open scoped BigOperators


@[simp] private theorem tailProd_zero (θ : ℕ → ℝ) : tailProd θ 0 = 1 := by
  simp [tailProd]

set_option maxHeartbeats 1000000 in
theorem solution (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) {n : ℕ}
    (hsum : ∑ j ∈ Finset.range n, p j = 1) :
    ∃ θ : ℕ → ℝ, ∀ m ≤ n, tailProd θ m = tailSum p n m := by

  -- For each `k < n`, pick an angle with `sin²(θ k) = tailSum(k+1)/tailSum(k)`
  -- (the conditional weight `P(k+1 or above | k or above)`).
  have h_ind : ∀ k < n, ∃ θ_k : ℝ, Real.sin θ_k ^ 2 = (tailSum p n (k + 1)) / (tailSum p n k) := by
    intro k hk
    have h_range : 0 ≤ (tailSum p n (k + 1)) / (tailSum p n k)
        ∧ (tailSum p n (k + 1)) / (tailSum p n k) ≤ 1 := by
      refine ⟨div_nonneg (tailSum_nonneg p hp n _) (tailSum_nonneg p hp n _),
        div_le_one_of_le₀ ?_ (tailSum_nonneg p hp n _)⟩
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico (by linarith) le_rfl) fun _ _ _ => hp _
    exact exists_sin_sq h_range.1 h_range.2;
  choose! θ hθ using h_ind
  refine ⟨θ, ?_⟩
  intro m
  induction m with
  | zero => intro _; rw [tailProd_zero, tailSum_zero_eq, hsum]
  | succ m ih =>
    intro hm
    have hmn : m < n := by omega
    rw [tailProd_succ, ih hmn.le]
    by_cases h : tailSum p n m = 0
    · have h_tail : tailSum p n m = p m + tailSum p n (m + 1) := tailSum_succ p n m hmn
      have h1 : tailSum p n (m + 1) = 0 := by
        have := tailSum_nonneg p hp n (m + 1); linarith [hp m]
      rw [h, h1, zero_mul]
    · rw [hθ m hmn, mul_div_cancel₀ _ h]
