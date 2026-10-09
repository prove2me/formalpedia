-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.eq_zero_of_flux_small
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:58:55.534907+00:00
-- url     : https://prove2.me/submissions/99a98290-d191-44b4-861f-9aaaae1aca5f

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.eq_zero_of_flux_small
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Theorems.Thm_BookProof_CarlemanUnboundedHop_flux_identity
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} (hz : z.im ≠ 0)
    (hherm : IsHermitianKernel a) (hrec : LadderRecInf a u z)
    (hsmall : ∀ ε > 0, ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ‖flux a u N‖ < ε) :
    ∀ n, u n = 0 := by

  have key : ∀ M : ℕ, ∑ n ∈ range (M + 1), ‖u n‖ ^ 2 ≤ 0 := by
    intro M
    by_contra hpos
    push_neg at hpos
    set S := ∑ n ∈ range (M + 1), ‖u n‖ ^ 2 with hS
    obtain ⟨N, hMN, hflux⟩ := hsmall (|z.im| * S) (by positivity) M
    have hmono : S ≤ ∑ n ∈ range (N + 1), ‖u n‖ ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hid := flux_identity hherm hrec N
    have h1 : |z.im| * S ≤ |z.im * ∑ n ∈ range (N + 1), ‖u n‖ ^ 2| := by
      rw [abs_mul]
      have hnn : 0 ≤ ∑ n ∈ range (N + 1), ‖u n‖ ^ 2 :=
        Finset.sum_nonneg fun n _ => by positivity
      rw [abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left hmono (abs_nonneg _)
    have h2 : |z.im * ∑ n ∈ range (N + 1), ‖u n‖ ^ 2| ≤ ‖flux a u N‖ := by
      rw [hid]
      exact Complex.abs_im_le_norm _
    linarith
  intro n
  have h := key n
  have hnn : 0 ≤ ∑ m ∈ range (n + 1), ‖u m‖ ^ 2 := Finset.sum_nonneg fun m _ => by positivity
  have hzero : ∑ m ∈ range (n + 1), ‖u m‖ ^ 2 = 0 := le_antisymm h hnn
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => by positivity)).mp hzero n
    (Finset.self_mem_range_succ n)
  simpa using this
