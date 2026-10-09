-- Prove2me | solution 1 for BookProof.ChapterCayleyTransform.one_sub_cayley_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:04:47.272132+00:00
-- url     : https://prove2.me/submissions/91d9892a-12de-454a-bf33-570292759f26

-- Generated from ChapterCayleyTransform.lean — solution of BookProof.ChapterCayleyTransform.one_sub_cayley_injective
import Mathlib
import Definitions.Def_ChapterCayleyTransform
import Theorems.Thm_BookProof_ChapterCayleyTransform_sub_cayley_shift
open BookProof.ChapterCayleyTransform



open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution :
    Function.Injective (fun y : H => y - cayley T y) := by

  intro y z hyz
  obtain ⟨x, rfl⟩ : ∃ x : T.domain, T.shift (-1) x = y :=
    ⟨T.res (-1) y, T.shift_res (by norm_num) y⟩
  obtain ⟨w, rfl⟩ : ∃ w : T.domain, T.shift (-1) w = z :=
    ⟨T.res (-1) z, T.shift_res (by norm_num) z⟩
  simp only [sub_cayley_shift] at hyz
  have h2 : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  have hx : (x : H) = (w : H) := by
    have := congrArg (fun v => (2 * Complex.I : ℂ)⁻¹ • v) hyz
    simpa [smul_smul, inv_mul_cancel₀ h2] using this
  rw [Subtype.ext hx]
