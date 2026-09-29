-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.ell2ShiftInvert_resolventPre
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:30:12.116358+00:00
-- url     : https://prove2.me/submissions/19a7fd78-1558-43e1-bd00-729f50a4f98e

-- Generated from ChapterHashimotoComplexShifts.lean — solution of BookProof.HashimotoShiftInvert.ell2ShiftInvert_resolventPre
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
import Theorems.Thm_BookProof_HashimotoShiftInvert_diagCLMC_apply
import Theorems.Thm_BookProof_HashimotoShiftInvert_sub_natCast_ne_zero
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
open BookProof.HashimotoShiftInvert



















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]







variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]








open scoped ENNReal InnerProductSpace lp

set_option maxHeartbeats 1000000 in
theorem solution {γ : ℂ} (hγ : γ.im ≠ 0) (u : ℓ²(ℕ, ℂ)) :
    ell2ShiftInvert (ell2ResolventPre hγ u) = ell2Resolvent hγ u := by

  apply lp.ext
  funext n
  have hne : γ - (n : ℂ) ≠ 0 := sub_natCast_ne_zero hγ n
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℂ)) by push_cast; ring]
    exact_mod_cast Nat.succ_ne_zero n
  have hcoe : ((invCoeff n : ℝ) : ℂ) = ((n : ℂ) + 1)⁻¹ := by
    rw [invCoeff]
    push_cast
    rw [one_div]
  rw [ell2ShiftInvert, diagCLM_apply, ell2ResolventPre, diagCLMC_apply, ell2Resolvent,
    diagCLMC_apply, hcoe, preCoeff, resCoeff]
  field_simp
