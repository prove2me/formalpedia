-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeSemigroup.norm_resolvent_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:30.451369+00:00
-- url     : https://prove2.me/submissions/e408feee-9797-405e-b827-87e319158154

-- Generated from ChapterNumericalRangeSemigroup.lean — solution of BookProof.ChapterNumericalRangeSemigroup.norm_resolvent_le
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
import Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_shift_symm_apply
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterNumericalRangeSemigroup



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re) :
    ‖((shiftEquiv h hz).symm : E →L[ℂ] E)‖ ≤ (z.re - ω)⁻¹ := by

  have hc : 0 < z.re - ω := by linarith
  have hlow : ∀ x : E, (z.re - ω) * ‖x‖ ≤ ‖(z • (1 : E →L[ℂ] E) - A) x‖ :=
    norm_ge_of_re_inner_ge (fun x => re_inner_shift h z x)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro y
  have hb := hlow ((shiftEquiv h hz).symm y)
  rw [shift_symm_apply h hz y] at hb
  have heq : ((shiftEquiv h hz).symm : E →L[ℂ] E) y = (shiftEquiv h hz).symm y := rfl
  rw [heq, inv_mul_eq_div, le_div_iff₀ hc]
  linarith [hb]
