-- Prove2me | solution 2 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:31:19.807217+00:00
-- url     : https://prove2.me/submissions/fef74a82-45a1-4133-98af-3e8b70abca01

import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_nonneg
open BookProof.ChapterF7
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
theorem h43_kin_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (L : LagrangianFullData F) (v : L.D) :
    (inner ℂ (v : F) (L.kinetic v : F) : ℂ)
      = (((1 / 2 : ℝ) * ∑ i : Fin 3, ‖(L.P i v : F)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [LagrangianFullData.kinetic, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, Submodule.coe_smul, Submodule.coe_sum,
    inner_smul_right, inner_sum]
  have h : ∀ i, (inner ℂ (v : F) ((L.P i (L.P i v)) : F) : ℂ) = ((‖(L.P i v : F)‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← L.P_symm i v (L.P i v), inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp only [h]
  push_cast; ring

theorem h43_kin_nonneg {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (L : LagrangianFullData F) (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.kinetic v : F) : ℂ).re := by
  rw [h43_kin_inner, Complex.ofReal_re]
  positivity

theorem solution (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.kinetic v : F) : ℂ).re := by
  exact h43_kin_nonneg L v

