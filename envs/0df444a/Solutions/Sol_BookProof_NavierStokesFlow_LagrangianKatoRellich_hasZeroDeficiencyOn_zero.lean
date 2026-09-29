-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianKatoRellich.hasZeroDeficiencyOn_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:53:16.41639+00:00
-- url     : https://prove2.me/submissions/a77eda19-d2fe-4171-9ac4-9891ececa4ab

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — solution of BookProof.NavierStokesFlow.LagrangianKatoRellich.hasZeroDeficiencyOn_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianKatoRellich

















open Filter Topology



open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)


























variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (L : LagrangianFullData F)








open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.DiagonalEsa

















open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.JacobiDeficiency

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} (hd : Dense (D : Set F)) :
    HasZeroDeficiencyOn D (0 : D →ₗ[ℂ] D) := by

  have key : ∀ w : F, (∀ v : D, (inner ℂ (v : F) w : ℂ) = 0) → w = 0 := by
    intro w hw
    have hclosed : IsClosed {y : F | (inner ℂ y w : ℂ) = 0} :=
      isClosed_eq (Continuous.inner continuous_id continuous_const) continuous_const
    have hsub : (D : Set F) ⊆ {y : F | (inner ℂ y w : ℂ) = 0} := fun y hy => hw ⟨y, hy⟩
    have huniv := hclosed.closure_subset_iff.mpr hsub
    rw [hd.closure_eq] at huniv
    exact inner_self_eq_zero.mp (huniv (Set.mem_univ w))
  constructor <;> intro w hw <;> refine key w fun v => ?_
  · have h := hw v
    simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, inner_zero_left, inner_smul_right] at h
    exact (mul_eq_zero.mp h.symm).resolve_left Complex.I_ne_zero
  · have h := hw v
    simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, inner_zero_left, inner_neg_right,
      inner_smul_right] at h
    exact (mul_eq_zero.mp (neg_eq_zero.mp h.symm)).resolve_left Complex.I_ne_zero
