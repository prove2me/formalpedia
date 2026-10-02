-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.IsShiftInvert.isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:53:28.944655+00:00
-- url     : https://prove2.me/submissions/77fc1b14-aea9-4bbe-9ee8-6632d72d9383

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterComplexShiftCore
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.HashimotoShiftInvert

set_option autoImplicit false

open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

open BookProof.HashimotoShiftInvert BookProof.FarisLavine in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} [CompleteSpace F] {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A) : IsSelfAdjoint R := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  obtain ⟨hu, hu'⟩ := h.2 u
  obtain ⟨hv, hv'⟩ := h.2 v
  have key := hsym ⟨R u, hu⟩ ⟨R v, hv⟩
  simp only [ContinuousLinearMap.coe_coe]
  conv_lhs => rw [← hv']
  conv_rhs => rw [← hu']
  simp only [shiftMap, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [key]
