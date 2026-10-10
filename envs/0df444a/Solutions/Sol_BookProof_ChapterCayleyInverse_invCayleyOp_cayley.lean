-- Prove2me | solution 1 for BookProof.ChapterCayleyInverse.invCayleyOp_cayley
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:16:21.379011+00:00
-- url     : https://prove2.me/submissions/9982f05e-c855-489f-a104-d7bc04e28896

-- Generated from ChapterCayleyInverse.lean — solution of BookProof.ChapterCayleyInverse.invCayleyOp_cayley
import Mathlib
import Definitions.Def_ChapterCayleyInverse
import Theorems.Thm_BookProof_ChapterCayleyInverse_oneSubU_cayley_injective
import Theorems.Thm_BookProof_ChapterCayleyTransform_add_cayley_shift
import Theorems.Thm_BookProof_ChapterCayleyTransform_sub_cayley_shift
open BookProof.ChapterCayleyInverse



open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterCayleyTransform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (V : H ≃ₗᵢ[ℂ] H)
variable (hinj : Function.Injective (oneSubU V))
variable [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution (x : T.domain) (hmem : (x : H) ∈ invCayleyDomain (cayley T)) :
    invCayleyOp (cayley T) (oneSubU_cayley_injective T) ⟨(x : H), hmem⟩ = T.op x := by

  have h2 : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  set y : H := (2 * Complex.I : ℂ)⁻¹ • T.shift (-1) x with hy
  have hVy : cayley T y = (2 * Complex.I : ℂ)⁻¹ • cayley T (T.shift (-1) x) := by
    rw [hy, map_smul]
  have hsub : oneSubEquiv (cayley T) (oneSubU_cayley_injective T) y = ⟨(x : H), hmem⟩ := by
    apply Subtype.ext
    rw [oneSubEquiv_coe, hVy, hy, ← smul_sub, sub_cayley_shift, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  rw [← hsub, invCayleyOp_apply, hVy, hy, ← smul_add, add_cayley_shift, smul_smul, smul_smul]
  have hI : Complex.I * (2 * Complex.I : ℂ)⁻¹ * 2 = 1 := by
    field_simp
  rw [hI, one_smul]
