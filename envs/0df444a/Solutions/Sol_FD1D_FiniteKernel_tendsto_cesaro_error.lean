-- Prove2me | solution 1 for FD1D.FiniteKernel.tendsto_cesaro_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:08.157844+00:00
-- url     : https://prove2.me/submissions/326c92a7-76b9-47e8-97d8-52aa2cd5201d

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_FiniteKernel_orbit_le_one
import Theorems.Thm_FD1D_FiniteKernel_cesaro_step_sub
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteKernel
theorem _root_.solution [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) :
    Tendsto (fun n =>
      K.cesaroVec μ n ᵥ* K.matrix - K.cesaroVec μ n)
      atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro x
  refine squeeze_zero_norm' (a := fun n : ℕ => 1 / (n + 1 : ℝ))
    (Eventually.of_forall fun n => ?_) ?_
  · rw [K.cesaro_step_sub μ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Real.norm_eq_abs]
    have hd :
        |K.orbit μ (n + 1) x - K.orbit μ 0 x| ≤ 1 := by
      rw [abs_le]
      constructor <;>
        linarith [K.orbit_nonneg μ (n + 1) x,
          K.orbit_le_one μ (n + 1) x,
          K.orbit_nonneg μ 0 x, K.orbit_le_one μ 0 x]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    calc
      ((↑(n + 1))⁻¹ : ℝ) *
          |K.orbit μ (n + 1) x - K.orbit μ 0 x| ≤
          (↑(n + 1))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = 1 / (n + 1 : ℝ) := by simp [one_div]
  · simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
end FD1D.FiniteKernel
