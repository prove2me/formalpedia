-- Prove2me | solution 1 for BookProof.FockCubicQuarticStability.mode_cubic_quartic_bounded_below
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:10:15.652767+00:00
-- url     : https://prove2.me/submissions/b01a979f-1ea1-4b7f-a12b-72800711bfa2

-- Generated from ChapterFockCubicQuarticStability.lean — solution of BookProof.FockCubicQuarticStability.mode_cubic_quartic_bounded_below
import Mathlib
import Definitions.Def_ChapterFockCubicQuarticStability
import Theorems.Thm_BookProof_FockCubicQuarticStability_quart_form_eq
import Theorems.Thm_BookProof_FockCubicQuarticStability_cubic_form_eq
import Theorems.Thm_BookProof_FockCubicQuarticStability_norm_creA_sq
import Theorems.Thm_BookProof_FockCubicQuarticStability_sq_norm_annA_le_mul
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockCubicQuarticStability



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicUnbounded
open BookProof.FockSecondQuantization

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (mu lam : ℝ) (u : FockAlg) :
    -(2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - mu) ^ 2 / 2) * ‖toLp u‖ ^ 2
      ≤ mu * ‖toLp (annA k u)‖ ^ 2
        + lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
        + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re := by

  set nu := ‖toLp u‖ with hnudef
  set an := ‖toLp (annA k u)‖ with handef
  set a2 := ‖toLp (annA k (annA k u))‖ with ha2def
  set ac := ‖toLp (creA k u)‖ with hacdef
  set xc := ‖toLp (creA k (annA k u))‖ with hxcdef
  have hnu0 : 0 ≤ nu := norm_nonneg _
  have han0 : 0 ≤ an := norm_nonneg _
  have ha20 : 0 ≤ a2 := norm_nonneg _
  have hac0 : 0 ≤ ac := norm_nonneg _
  have hxc0 : 0 ≤ xc := norm_nonneg _
  have hquart : (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re = a2 ^ 2 := quart_form_eq k u
  have hcubic : (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
      = 2 * (inner ℂ (toLp (annA k (annA k u))) (toLp (creA k u)) : ℂ).re := cubic_form_eq k u
  set R := (inner ℂ (toLp (annA k (annA k u))) (toLp (creA k u)) : ℂ).re with hRdef
  have hR : |R| ≤ a2 * ac := by
    have h1 : |R| ≤ ‖(inner ℂ (toLp (annA k (annA k u))) (toLp (creA k u)) : ℂ)‖ :=
      Complex.abs_re_le_norm _
    exact h1.trans (norm_inner_le_norm _ _)
  have hcc : ac ^ 2 = an ^ 2 + nu ^ 2 := norm_creA_sq k u
  have hxx : xc ^ 2 = a2 ^ 2 + an ^ 2 := norm_creA_sq k (annA k u)
  have hcs : an ^ 2 ≤ nu * xc := sq_norm_annA_le_mul k u
  -- the cubic term is dominated by half the quartic term plus `2lam²‖a†u‖²`
  have hRbound : -(a2 ^ 2 / 2 + 2 * lam ^ 2 * ac ^ 2) ≤ lam * (2 * R) := by
    obtain ⟨hR1, hR2⟩ := abs_le.mp hR
    rcases le_or_gt 0 lam with hl | hl
    · nlinarith [sq_nonneg (a2 - 2 * lam * ac)]
    · nlinarith [sq_nonneg (a2 + 2 * lam * ac)]
  -- the quartic term dominates the remainder, by Cauchy–Schwarz
  have hkey : 0 ≤ mu * an ^ 2 + a2 ^ 2 / 2 - 2 * lam ^ 2 * (an ^ 2 + nu ^ 2)
      + (2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - mu) ^ 2 / 2) * nu ^ 2 := by
    rcases eq_or_lt_of_le hnu0 with hnu | hnu
    · -- the degenerate case `‖u‖ = 0`: Cauchy–Schwarz forces `‖a_k u‖ = 0` too
      have hz : nu = 0 := hnu.symm
      have han2 : an ^ 2 = 0 :=
        le_antisymm (by rw [hz] at hcs; simpa using hcs) (sq_nonneg an)
      rw [hz, han2]
      nlinarith [sq_nonneg a2]
    · have hnu2 : (0 : ℝ) < 2 * nu ^ 2 := by positivity
      have hA : an ^ 4 - nu ^ 2 * an ^ 2 ≤ nu ^ 2 * a2 ^ 2 := by
        have h1 : an ^ 4 ≤ nu ^ 2 * xc ^ 2 := by
          nlinarith [hcs, sq_nonneg an, mul_nonneg hnu0 hxc0]
        have h2 : nu ^ 2 * xc ^ 2 = nu ^ 2 * (a2 ^ 2 + an ^ 2) := by rw [hxx]
        linarith
      have hmul : 2 * nu ^ 2 * 0 ≤ 2 * nu ^ 2 * (mu * an ^ 2 + a2 ^ 2 / 2
          - 2 * lam ^ 2 * (an ^ 2 + nu ^ 2)
          + (2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - mu) ^ 2 / 2) * nu ^ 2) := by
        have hsq := sq_nonneg (an ^ 2 - (2 * lam ^ 2 + 1 / 2 - mu) * nu ^ 2)
        nlinarith [hA, hsq]
      exact le_of_mul_le_mul_left hmul hnu2
  have hcc' : 2 * lam ^ 2 * ac ^ 2 = 2 * lam ^ 2 * (an ^ 2 + nu ^ 2) := by rw [hcc]
  rw [hquart, hcubic]
  linarith [hkey, hRbound, hcc']
