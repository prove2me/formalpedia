-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.exists_mul_lt_of_not_summable_inv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:00:45.01554+00:00
-- url     : https://prove2.me/submissions/48b60b12-1252-4570-a459-9d86242981de

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.exists_mul_lt_of_not_summable_inv
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution {A S : ℕ → ℝ} (hA : ∀ n, 0 < A n)
    (hSsum : Summable S) (hcar : ¬ Summable fun n => (A n)⁻¹) :
    ∀ ε > 0, ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ A N * S N < ε := by

  by_contra hcon
  push_neg at hcon
  obtain ⟨ε, hε, N₀, hall⟩ := hcon
  refine hcar ?_
  have hkey : ∀ N : ℕ, (A (N + N₀))⁻¹ ≤ S (N + N₀) / ε := by
    intro N
    have h := hall (N + N₀) (by omega)
    have hApos := hA (N + N₀)
    rw [inv_eq_one_div, div_le_div_iff₀ hApos hε]
    nlinarith
  have hmaj : Summable (fun N : ℕ => S (N + N₀) / ε) :=
    (((summable_nat_add_iff N₀).mpr hSsum)).div_const ε
  have h2 : Summable (fun N : ℕ => (A (N + N₀))⁻¹) :=
    Summable.of_nonneg_of_le (fun N => inv_nonneg.mpr (hA _).le) hkey hmaj
  exact (summable_nat_add_iff N₀).mp h2
