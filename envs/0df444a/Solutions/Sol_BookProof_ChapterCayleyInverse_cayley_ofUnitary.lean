-- Prove2me | solution 1 for BookProof.ChapterCayleyInverse.cayley_ofUnitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:03:54.046215+00:00
-- url     : https://prove2.me/submissions/27b4f3d2-6c1a-4a8a-b03b-e5fdc72173a0

-- Generated from ChapterCayleyInverse.lean — solution of BookProof.ChapterCayleyInverse.cayley_ofUnitary
import Mathlib
import Definitions.Def_ChapterCayleyInverse
import Theorems.Thm_BookProof_ChapterCayleyTransform_cayley_shift
open BookProof.ChapterCayleyInverse



open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterCayleyTransform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (V : H ≃ₗᵢ[ℂ] H)
variable (hinj : Function.Injective (oneSubU V))
variable [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (hdense : Dense ((invCayleyDomain V : Submodule ℂ H) : Set H))
    (y : H) : cayley (ofUnitary V hinj hdense) y = V y := by

  set T := ofUnitary V hinj hdense with hT
  set x : T.domain := oneSubEquiv V hinj ((2 * Complex.I : ℂ)⁻¹ • y) with hx
  have h2 : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  have hplus : T.shift (-1) x = y := by
    rw [T.shift_apply]
    have hop : T.op x + Complex.I • (x : H) = (2 * Complex.I) • ((2 * Complex.I : ℂ)⁻¹ • y) :=
      invCayleyOp_add_i V hinj _
    rw [smul_smul, mul_inv_cancel₀ h2, one_smul] at hop
    rw [← hop]
    push_cast
    module
  have hminus : T.shift 1 x = V y := by
    rw [T.shift_apply]
    have hop : T.op x - Complex.I • (x : H)
        = (2 * Complex.I) • V ((2 * Complex.I : ℂ)⁻¹ • y) := invCayleyOp_sub_i V hinj _
    rw [map_smul, smul_smul, mul_inv_cancel₀ h2, one_smul] at hop
    rw [← hop]
    push_cast
    module
  calc cayley T y = cayley T (T.shift (-1) x) := by rw [hplus]
    _ = T.shift 1 x := cayley_shift T x
    _ = V y := hminus
