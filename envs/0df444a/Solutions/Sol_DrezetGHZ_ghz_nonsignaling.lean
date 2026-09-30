-- Prove2me | solution 1 for DrezetGHZ.ghz_nonsignaling
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:16:53.296135+00:00
-- url     : https://prove2.me/submissions/3e039557-8135-4ca4-85d9-cd1b325dd35f

import Definitions.Def_DrezetGHZ_Quantum

set_option autoImplicit false
open DrezetGHZ Matrix

set_option maxHeartbeats 1600000 in
private theorem marginal_half (n₁ n₂ n₃ : Setting) (α : ℤˣ) :
    ∑ β, ∑ γ, bornProb n₁ n₂ n₃ α β γ = 1 / 2 := by
  have hu : (Finset.univ : Finset ℤˣ) = {1, -1} := by
    ext u
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  have hs2r : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast hs2r
  have hs4 : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
    calc
      (Real.sqrt 2 : ℂ) ^ 4 = ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hs2]; norm_num
  cases n₁ <;> cases n₂ <;> cases n₃ <;>
    rcases Int.units_eq_one_or α with rfl | rfl <;>
    norm_num [hu, bornProb, productKet, spinEigenvector, dotProduct, ghzState,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_div, Complex.normSq_mul,
      Complex.normSq_ofReal, Real.sq_sqrt] <;>
    ring_nf <;> norm_num [Complex.I_sq, hs4, Complex.normSq_apply]

theorem solution :
    (∀ (n₁ n₂ n₃ n₂' n₃' : Setting) (α : ℤˣ),
      ∑ β, ∑ γ, bornProb n₁ n₂ n₃ α β γ = ∑ β, ∑ γ, bornProb n₁ n₂' n₃' α β γ) ∧
    (∀ (n₂ n₃ : Setting) (α : ℤˣ), ∑ β, ∑ γ, bornProb .x n₂ n₃ α β γ = 1 / 2) := by
  constructor
  · intro n₁ n₂ n₃ n₂' n₃' α
    rw [marginal_half, marginal_half]
  · intro n₂ n₃ α
    exact marginal_half .x n₂ n₃ α
