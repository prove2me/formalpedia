-- Prove2me | solution 1 for FD1D.FiniteKernel.tendsto_iterate_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:44:15.161458+00:00
-- url     : https://prove2.me/submissions/6512a536-32da-465d-a003-756b8b4ee331

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_FiniteConvergence
import Theorems.Thm_FD1D_FiniteKernel_exists_pow_pos
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteKernel_iterate_add
import Theorems.Thm_FD1D_FiniteKernel_pow_nonneg
import Theorems.Thm_FD1D_FiniteKernel_sum_pow
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const


section
namespace FD1D
noncomputable section
open Filter
open scoped BigOperators Topology
namespace FiniteKernel
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
private theorem lawL1_nonneg (μ ν : FiniteLaw α) :
    0 ≤ lawL1 μ ν :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
private theorem mass_iterate_sub
    (K : FiniteKernel α) (n : ℕ) (μ ν : FiniteLaw α) (y : α) :
    (K.iterate n μ).mass y - (K.iterate n ν).mass y =
      ∑ x, (μ.mass x - ν.mass x) * K.pow n x y := by
  rw [K.mass_iterate, K.mass_iterate, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring
private theorem lawL1_iterate_le
    (K : FiniteKernel α) (n : ℕ) (μ ν : FiniteLaw α) :
    lawL1 (K.iterate n μ) (K.iterate n ν) ≤ lawL1 μ ν := by
  unfold lawL1
  simp_rw [mass_iterate_sub]
  calc
    (∑ y, |∑ x, (μ.mass x - ν.mass x) * K.pow n x y|) ≤
        ∑ y, ∑ x, |(μ.mass x - ν.mass x) * K.pow n x y| := by
      exact Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, ∑ y, |μ.mass x - ν.mass x| * K.pow n x y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_mul, abs_of_nonneg (K.pow_nonneg n x y)]
    _ = ∑ x, |μ.mass x - ν.mass x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum, K.sum_pow, mul_one]
private theorem exists_minorization
    (K : FiniteKernel α) {N : ℕ}
    (hpos : ∀ x y, 0 < K.pow N x y) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ x y, ε ≤ K.pow N x y) ∧
      (Fintype.card α : ℝ) * ε ≤ 1 := by
  obtain ⟨p, _, hp⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (α × α))
      (fun p => K.pow N p.1 p.2) Finset.univ_nonempty
  let ε := K.pow N p.1 p.2
  refine ⟨ε, hpos p.1 p.2, ?_, ?_⟩
  · intro x y
    exact hp (x, y) (Finset.mem_univ _)
  · let x₀ : α := Classical.arbitrary α
    calc
      (Fintype.card α : ℝ) * ε = ∑ _y : α, ε := by
        simp
      _ ≤ ∑ y, K.pow N x₀ y := by
        exact Finset.sum_le_sum fun y _ => hp (x₀, y) (Finset.mem_univ _)
      _ = 1 := K.sum_pow N x₀
private theorem sum_mass_sub (μ ν : FiniteLaw α) :
    ∑ x, (μ.mass x - ν.mass x) = 0 := by
  rw [Finset.sum_sub_distrib, μ.sum_mass, ν.sum_mass, sub_self]
private theorem mass_iterate_sub_eq_residual
    (K : FiniteKernel α) (N : ℕ) (ε : ℝ)
    (μ ν : FiniteLaw α) (y : α) :
    (K.iterate N μ).mass y - (K.iterate N ν).mass y =
      ∑ x, (μ.mass x - ν.mass x) * (K.pow N x y - ε) := by
  rw [mass_iterate_sub]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_mass_sub, zero_mul, sub_zero]
private theorem lawL1_block_contraction
    (K : FiniteKernel α) (N : ℕ) (ε : ℝ)
    (hε : ∀ x y, ε ≤ K.pow N x y)
    (μ ν : FiniteLaw α) :
    lawL1 (K.iterate N μ) (K.iterate N ν) ≤
      (1 - (Fintype.card α : ℝ) * ε) * lawL1 μ ν := by
  unfold lawL1
  simp_rw [mass_iterate_sub_eq_residual K N ε]
  calc
    (∑ y, |∑ x, (μ.mass x - ν.mass x) * (K.pow N x y - ε)|) ≤
        ∑ y, ∑ x,
          |(μ.mass x - ν.mass x) * (K.pow N x y - ε)| := by
      exact Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, ∑ y,
        |μ.mass x - ν.mass x| * (K.pow N x y - ε) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hε x y))]
    _ = ∑ x, |μ.mass x - ν.mass x| *
        (1 - (Fintype.card α : ℝ) * ε) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_sub_distrib, K.sum_pow]
      simp
    _ = (1 - (Fintype.card α : ℝ) * ε) *
        ∑ x, |μ.mass x - ν.mass x| := by
      rw [← Finset.sum_mul]
      ring
private theorem lawL1_blocks_le
    (K : FiniteKernel α) (π μ : FiniteLaw α)
    (hπ : K.IsStationary π)
    (N : ℕ) (ε : ℝ)
    (hε : ∀ x y, ε ≤ K.pow N x y)
    (hq : 0 ≤ 1 - (Fintype.card α : ℝ) * ε)
    (k : ℕ) :
    lawL1 (K.iterate (k * N) μ) π ≤
      (1 - (Fintype.card α : ℝ) * ε) ^ k * lawL1 μ π := by
  let q := 1 - (Fintype.card α : ℝ) * ε
  induction k with
  | zero =>
      simp [q]
  | succ k ih =>
      have hcontract :=
        lawL1_block_contraction K N ε hε (K.iterate (k * N) μ) π
      rw [hπ.iterate N] at hcontract
      have hstep :
          lawL1 (K.iterate N (K.iterate (k * N) μ)) π ≤
            q ^ (k + 1) * lawL1 μ π := by
        calc
          lawL1 (K.iterate N (K.iterate (k * N) μ)) π ≤
              q * lawL1 (K.iterate (k * N) μ) π := hcontract
          _ ≤ q * (q ^ k * lawL1 μ π) :=
            mul_le_mul_of_nonneg_left ih hq
          _ = q ^ (k + 1) * lawL1 μ π := by
            rw [pow_succ]
            ring
      rw [← K.iterate_add] at hstep
      simpa [q, Nat.succ_mul, Nat.add_comm] using hstep
private theorem lawL1_iterate_geometric
    (K : FiniteKernel α) (π μ : FiniteLaw α)
    (hπ : K.IsStationary π)
    (N : ℕ) (hN : 0 < N)
    (ε : ℝ) (hε : ∀ x y, ε ≤ K.pow N x y)
    (hc : (Fintype.card α : ℝ) * ε ≤ 1)
    (n : ℕ) :
    lawL1 (K.iterate n μ) π ≤
      (1 - (Fintype.card α : ℝ) * ε) ^ (n / N) * lawL1 μ π := by
  let q := 1 - (Fintype.card α : ℝ) * ε
  have hq : 0 ≤ q := sub_nonneg.mpr hc
  have hdecomp : n % N + (n / N) * N = n := by
    rw [mul_comm, Nat.mod_add_div]
  calc
    lawL1 (K.iterate n μ) π =
        lawL1
          (K.iterate (n % N) (K.iterate ((n / N) * N) μ))
          (K.iterate (n % N) π) := by
      rw [← K.iterate_add, hdecomp, hπ.iterate]
    _ ≤ lawL1 (K.iterate ((n / N) * N) μ) π :=
      lawL1_iterate_le K (n % N) _ _
    _ ≤ q ^ (n / N) * lawL1 μ π :=
      lawL1_blocks_le K π μ hπ N ε hε hq (n / N)
private theorem tendsto_lawL1_zero
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops)
    (π : FiniteLaw α) (hπ : K.IsStationary π)
    (μ : FiniteLaw α) :
    Tendsto (fun n => lawL1 (K.iterate n μ) π) atTop (𝓝 0) := by
  obtain ⟨N, hN, hpow⟩ := exists_pow_pos K hirr hloop
  obtain ⟨ε, hεpos, hε, hc⟩ := exists_minorization K hpow
  let q := 1 - (Fintype.card α : ℝ) * ε
  have hq0 : 0 ≤ q := sub_nonneg.mpr hc
  have hcard : 0 < (Fintype.card α : ℝ) := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    nlinarith
  have hpowlim :
      Tendsto (fun n : ℕ => q ^ (n / N)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
      (Nat.tendsto_div_const_atTop hN.ne')
  refine squeeze_zero (fun n => lawL1_nonneg (K.iterate n μ) π)
    (fun n => lawL1_iterate_geometric K π μ hπ N hN ε hε hc n) ?_
  simpa [q] using hpowlim.mul_const (lawL1 μ π)
end FiniteKernel
end
end FD1D
end

set_option autoImplicit true
open FD1D
noncomputable section
open Filter
open scoped BigOperators Topology
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
namespace FD1D.FiniteKernel
theorem _root_.solution
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops)
    (π : FiniteLaw α) (hπ : K.IsStationary π)
    (μ : FiniteLaw α) :
    Tendsto (fun n => (K.iterate n μ).mass) atTop (𝓝 π.mass) := by
  rw [tendsto_pi_nhds]
  intro x
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hL1 := tendsto_lawL1_zero K hirr hloop π hπ μ
  refine squeeze_zero (fun n => dist_nonneg)
    (fun n => ?_) hL1
  rw [Real.dist_eq]
  exact Finset.single_le_sum
    (fun y _ => abs_nonneg ((K.iterate n μ).mass y - π.mass y))
    (Finset.mem_univ x)
end FD1D.FiniteKernel
