-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeSemigroup.norm_exp_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:57:14.632463+00:00
-- url     : https://prove2.me/submissions/de52f351-bd0b-435d-8c74-1bb622e66224

-- Generated from ChapterNumericalRangeSemigroup.lean — solution of BookProof.ChapterNumericalRangeSemigroup.norm_exp_apply_le
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
import Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_hasDerivAt_normSq
open BookProof.ChapterNumericalRangeSemigroup



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) (x : E) {t : ℝ}
    (ht : 0 ≤ t) : ‖NormedSpace.exp (t • A) x‖ ≤ Real.exp (ω * t) * ‖x‖ := by

  set g : ℝ → ℝ := fun s => ‖(NormedSpace.exp (s • A)) x‖ ^ 2 * Real.exp (-(2 * ω) * s) with hg
  have hderiv : ∀ s : ℝ, HasDerivAt g
      (2 * (inner ℂ (NormedSpace.exp (s • A) x) (A (NormedSpace.exp (s • A) x))).re
          * Real.exp (-(2 * ω) * s)
        + ‖(NormedSpace.exp (s • A)) x‖ ^ 2 * (Real.exp (-(2 * ω) * s) * -(2 * ω))) s := by
    intro s
    have h1 := hasDerivAt_normSq A x s
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-(2 * ω) * s))
        (Real.exp (-(2 * ω) * s) * -(2 * ω)) s := by
      simpa using ((hasDerivAt_id s).const_mul (-(2 * ω))).exp
    exact h1.mul h2
  have hnonpos : ∀ s : ℝ, deriv g s ≤ 0 := by
    intro s
    rw [(hderiv s).deriv]
    have hb := h (NormedSpace.exp (s • A) x)
    have hpos : 0 < Real.exp (-(2 * ω) * s) := Real.exp_pos _
    nlinarith [hb, hpos]
  have hdiff : Differentiable ℝ g := fun s => (hderiv s).differentiableAt
  have hanti : Antitone g := antitone_of_deriv_nonpos hdiff hnonpos
  have hle := hanti ht
  simp only [hg] at hle
  have h0 : ‖(NormedSpace.exp ((0 : ℝ) • A)) x‖ ^ 2 * Real.exp (-(2 * ω) * 0) = ‖x‖ ^ 2 := by
    simp
  rw [h0] at hle
  have hexp : 0 < Real.exp (-(2 * ω) * t) := Real.exp_pos _
  have hsq : ‖(NormedSpace.exp (t • A)) x‖ ^ 2 ≤ (Real.exp (ω * t) * ‖x‖) ^ 2 := by
    have hdiv : ‖(NormedSpace.exp (t • A)) x‖ ^ 2 ≤ ‖x‖ ^ 2 / Real.exp (-(2 * ω) * t) := by
      rw [le_div_iff₀ hexp]
      exact hle
    have hone : Real.exp (ω * t) ^ 2 * Real.exp (-(2 * ω) * t) = 1 := by
      rw [sq, ← Real.exp_add, ← Real.exp_add,
        show ω * t + ω * t + -(2 * ω) * t = 0 by ring, Real.exp_zero]
    have hrw : ‖x‖ ^ 2 / Real.exp (-(2 * ω) * t) = (Real.exp (ω * t) * ‖x‖) ^ 2 := by
      rw [div_eq_iff (ne_of_gt hexp), mul_pow]
      nlinarith [hone]
    rw [hrw] at hdiv
    exact hdiv
  have hb : 0 ≤ Real.exp (ω * t) * ‖x‖ := by positivity
  calc ‖(NormedSpace.exp (t • A)) x‖
      = Real.sqrt (‖(NormedSpace.exp (t • A)) x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.exp (ω * t) * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.exp (ω * t) * ‖x‖ := Real.sqrt_sq hb
