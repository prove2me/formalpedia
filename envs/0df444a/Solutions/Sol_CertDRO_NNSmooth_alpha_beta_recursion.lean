-- Prove2me | solution 1 for CertDRO.NNSmooth.alpha_beta_recursion
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:38:59.115984+00:00
-- url     : https://prove2.me/submissions/cdb8046d-8de1-4210-aaf8-5559f842e576

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Network

set_option autoImplicit false

open CertDRO.NNSmooth CertDRO.NNSmooth.Network

theorem solution (N : Network) (L0 L1 : ℕ → ℝ) :
    N.α L0 0 = 1 ∧ N.β L0 L1 0 = 0 ∧
    (∀ l, N.α L0 (l + 1) = L0 l * ‖N.θ l‖ * N.α L0 l) ∧
    (∀ l, N.β L0 L1 (l + 1) =
      L0 l * ‖N.θ l‖ * N.β L0 L1 l + (L1 l / (L0 l) ^ 2) * N.α L0 (l + 1) ^ 2) ∧
    (∀ l, N.α L0 l ≠ 0 → N.β L0 L1 (l + 1) =
      (N.α L0 (l + 1) / N.α L0 l) * N.β L0 L1 l + (L1 l / (L0 l) ^ 2) * N.α L0 (l + 1) ^ 2) ∧
    (∀ L, ‖N.θ L‖ = 1 → L0 L = Real.sqrt 2 → L1 L = 1 →
      N.β L0 L1 (L + 1) = Real.sqrt 2 * N.β L0 L1 L + N.α L0 L ^ 2) := by
  have hα : ∀ l, N.α L0 (l + 1) = L0 l * ‖N.θ l‖ * N.α L0 l := by
    intro l
    unfold Network.α
    rw [Finset.prod_range_succ]; ring
  have hβ : ∀ l, N.β L0 L1 (l + 1) =
      L0 l * ‖N.θ l‖ * N.β L0 L1 l + (L1 l / (L0 l) ^ 2) * N.α L0 (l + 1) ^ 2 := by
    intro l
    unfold Network.β
    rw [Finset.sum_range_succ, hα l]
    ring
  refine ⟨by simp [Network.α], by simp [Network.β], hα, hβ, ?_, ?_⟩
  · intro l hl
    rw [hβ l, hα l]
    field_simp
  · intro L h1 h2 h3
    rw [hβ L, h1, h2, h3, hα L, h1, h2]
    have h2' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hne : (2:ℝ) ≠ 0 := by norm_num
    field_simp
