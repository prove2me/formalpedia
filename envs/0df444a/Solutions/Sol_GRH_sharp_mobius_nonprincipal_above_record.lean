-- Prove2me | solution 1 for GRH.sharp_mobius_nonprincipal_above_record
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:32:46.195445+00:00
-- url     : https://prove2.me/submissions/a7024cdd-35e4-42e0-b770-ef087d135406

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.NormNum
import Theorems.Thm_Titchmarsh_partialSum_isBigO_of_holomorphic_growth
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound

import Theorems.Thm_GRH_reciprocal_nonprincipal_subpower

open Filter Asymptotics

theorem solution (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (σ : ℝ)
    (hσ : (0.8749570698 : ℝ) < σ) :
    (fun n : ℕ => ∑ k ∈ Finset.range (n+1), χ k * (ArithmeticFunction.moebius k : ℂ))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ σ) := by
  let a (k : ℕ) : ℂ := χ k * (ArithmeticFunction.moebius k : ℂ)
  have ha (k : ℕ) : ‖a k‖ ≤ 1 := by
    have hμ : ‖(ArithmeticFunction.moebius k : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
    dsimp only [a]
    rw [norm_mul]
    simpa using mul_le_mul (χ.norm_le_one _) hμ (norm_nonneg _) zero_le_one
  have hF : DifferentiableOn ℂ (fun s : ℂ => (χ.LFunction s)⁻¹)
      {s : ℂ | (0.8749570698 : ℝ) < s.re} := by
    intro s hs
    exact ((χ.differentiable_LFunction hχ s).inv
      (TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound χ hs
        (fun h => hχ h.1))).differentiableWithinAt
  have hFL (s : ℂ) (hs : 1 < s.re) :
      (χ.LFunction s)⁻¹ = LSeries a s := by
    rw [χ.LFunction_eq_LSeries hs]
    exact inv_eq_of_mul_eq_one_right (DirichletCharacter.LSeries.mul_mu_eq_one χ hs)
  have hperron := Titchmarsh.partialSum_isBigO_of_holomorphic_growth a ha _
    (by norm_num : (0:ℝ) ≤ 0.8749570698) _ hF hFL
    (fun δ hδ ε hε => GRH.reciprocal_nonprincipal_subpower q χ hχ δ ε hδ hε)
    (σ - 0.8749570698) (sub_pos.mpr hσ)
  have hsum (n : ℕ) : ∑ k ∈ Finset.range (n+1), a k = ∑ k ∈ Finset.Icc 1 n, a k := by
    have he : Finset.range (n+1) = insert 0 (Finset.Icc 1 n) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [he, Finset.sum_insert (by simp)]
    simp [a]
  change (fun n : ℕ => ∑ k ∈ Finset.range (n+1), a k) =O[atTop] _
  simp_rw [hsum]
  simpa only [add_sub_cancel] using hperron
