-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.ell2ExampleMatrix_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:25:29.76972+00:00
-- url     : https://prove2.me/submissions/261cdc50-05c3-46ed-a32f-59626c86e73e

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.ell2ExampleMatrix_unbounded
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore

set_option linter.unusedSectionVars false
open scoped lp
open BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology


theorem solution (C : ℝ) :
    ∃ x : finiteModeDomain ell2Basis, C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖ := by
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have hmem : (ell2Basis k : ℓ²(ℕ, ℂ)) ∈ finiteModeDomain ell2Basis :=
    Submodule.subset_span ⟨k, rfl⟩
  refine ⟨⟨ell2Basis k, hmem⟩, ?_⟩
  set x : finiteModeDomain ell2Basis := ⟨ell2Basis k, hmem⟩
  have hnormx : ‖(x : ℓ²(ℕ, ℂ))‖ = 1 := by
    simpa [x] using ell2Basis.orthonormal.norm_eq_one k
  have hy :
      (x : ℓ²(ℕ, ℂ)) ∈ LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) := by
    simpa [x] using ell2Basis_mem_range k
  let y : LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) := ⟨x, hy⟩
  have hpre :
      preim ell2ShiftInvert y = ((k : ℂ) + 1) • lp.single 2 k (1 : ℂ) := by
    apply ell2ShiftInvert_injective
    rw [preim_spec, ell2ShiftInvert_smul_single]
    simp [y, x, ell2Basis_apply]
  have hAx :
      ell2ExampleMatrix x = ((k : ℂ) • (ell2Basis k : ℓ²(ℕ, ℂ))) := by
    have hinc :
        (Submodule.inclusion finiteModeDomain_le_range x : ℓ²(ℕ, ℂ)) = (x : ℓ²(ℕ, ℂ)) := rfl
    have hAy :
        ell2UnboundedExample (Submodule.inclusion finiteModeDomain_le_range x)
          = preim ell2ShiftInvert y - (1 : ℂ) • (y : ℓ²(ℕ, ℂ)) := by
      have hEq : Submodule.inclusion finiteModeDomain_le_range x = y := by
        apply Subtype.ext
        simp [y, hinc]
      simpa [ell2UnboundedExample, hEq] using
        (show invShiftOperator ell2ShiftInvert ell2ShiftInvert_injective (1 : ℝ) y
            = preim ell2ShiftInvert y - (1 : ℂ) • (y : ℓ²(ℕ, ℂ)) from rfl)
    simp only [ell2ExampleMatrix, LinearMap.comp_apply, hAy, hpre]
    simp [y, x, ell2Basis_apply, sub_eq_add_neg]
    -- (k+1) • e - 1 • e = k • e
    module
  rw [hnormx, hAx]
  have hnk : ‖(k : ℂ) • (ell2Basis k : ℓ²(ℕ, ℂ))‖ = (k : ℝ) := by
    rw [norm_smul, Complex.norm_natCast, hnormx, mul_one]
  rw [hnk]
  simpa using hk
