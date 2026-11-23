-- Prove2me | solution 1 for Formalism.L2.Th1.H.CmData.selfDual_img
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:32.531724+00:00
-- url     : https://prove2.me/submissions/30d8657c-630e-48e8-9e7a-a1cc15226603

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_StdDataCmProof

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H Formalism.L2.Th1.H.CmData
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmPair cmTheta)
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.Th1.H.CmData
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V)
    (H' : Sesq W) (g : V ≃ₗ[ℂ] W) (hg : IsIsom H H' (g : V →ₗ[ℂ] W)) (Λ : AddSubgroup V)
    (hsd : IsSelfDual H Λ) : IsSelfDual H' (imgLat (g : V →ₗ[ℂ] W) Λ) := by
  ext x
  constructor
  · intro hx
    refine ⟨g.symm x, ?_, by simp⟩
    show g.symm x ∈ Λ
    rw [← hsd]
    intro y hy
    obtain ⟨m, hm⟩ := hx (g y) ⟨y, hy, rfl⟩
    refine ⟨m, ?_⟩
    rw [← hm]
    have := hg (g.symm x) y
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    simp only [altE, this]
  · rintro ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
    have h1 : x' ∈ dualLat H Λ := by rw [hsd]; exact hx'
    obtain ⟨m, hm⟩ := h1 y' hy'
    refine ⟨m, ?_⟩
    rw [← hm]
    have := hg x' y'
    simp only [altE]
    exact congrArg Complex.im this
end Formalism.L2.Th1.H.CmData
