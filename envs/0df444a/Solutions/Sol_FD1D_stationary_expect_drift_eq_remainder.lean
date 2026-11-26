-- Prove2me | solution 1 for FD1D.stationary_expect_drift_eq_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:43.864531+00:00
-- url     : https://prove2.me/submissions/51734c76-fbf6-4a63-9994-b90ca366adc1

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_harmonicPotential_zero
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.harmonicPotential_zero
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (K : α → α → ℝ)
    (Phi D R : α → ℝ)
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hstationary : ∀ y, ∑ x, μ.mass x * K x y = μ.mass y)
    (hdrift : ∀ x, ∑ y, K x y * (Phi y - Phi x) = D x - R x) :
    μ.expect D = μ.expect R := by
  have hnext :
      ∑ x, μ.mass x * (∑ y, K x y * Phi y) =
        ∑ y, μ.mass y * Phi y := by
    calc
      ∑ x, μ.mass x * (∑ y, K x y * Phi y)
          = ∑ x, ∑ y, μ.mass x * K x y * Phi y := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = ∑ y, ∑ x, μ.mass x * K x y * Phi y := Finset.sum_comm
      _ = ∑ y, (∑ x, μ.mass x * K x y) * Phi y := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [Finset.sum_mul]
      _ = ∑ y, μ.mass y * Phi y := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [hstationary]
  have hcurrent :
      ∑ x, μ.mass x * (∑ y, K x y * Phi x) =
        ∑ x, μ.mass x * Phi x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_mul, hrow, one_mul]
  have hzero :
      ∑ x, μ.mass x * (∑ y, K x y * (Phi y - Phi x)) = 0 := by
    calc
      ∑ x, μ.mass x * (∑ y, K x y * (Phi y - Phi x))
          = (∑ x, μ.mass x * (∑ y, K x y * Phi y)) -
              ∑ x, μ.mass x * (∑ y, K x y * Phi x) := by
                simp_rw [mul_sub, Finset.sum_sub_distrib]
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hnext, hcurrent]; ring
  have hdriftZero : μ.expect (fun x => D x - R x) = 0 := by
    rw [FiniteLaw.expect]
    calc
      ∑ x, μ.mass x * (D x - R x) =
          ∑ x, μ.mass x *
            (∑ y, K x y * (Phi y - Phi x)) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [hdrift]
      _ = 0 := hzero
  have heq :
      (∑ x, μ.mass x * D x) - (∑ x, μ.mass x * R x) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [FiniteLaw.expect, mul_sub] using hdriftZero
  change (∑ x, μ.mass x * D x) = ∑ x, μ.mass x * R x
  exact sub_eq_zero.mp heq
end FD1D
