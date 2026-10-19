-- Prove2me | solution 1 for Everyday.higgs_ground
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:23:33.375047+00:00
-- url     : https://prove2.me/submissions/4fcd10ac-5627-4609-869e-d2b9b83d1b97

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

open Everyday
/-- Higgs: the vacuum. The Mexican-hat potential is bounded below, with
its minimum value -μ⁴/(4λ) attained exactly on the circle of fields with
|φ|² = μ²/(2λ) — the spontaneous symmetry breaking locus of the Higgs
field, the nonzero field value the everyday world rests on. The quartic
coupling λ is bound as lam, λ being a reserved keyword in Lean 4. -/


theorem solution (μ lam : ℝ) (φ : ℂ) (hμ : 0 < μ) (hlam : 0 < lam) :
    -(μ ^ 4 / (4 * lam)) ≤ higgsV μ lam φ ∧
      (higgsV μ lam φ = -(μ ^ 4 / (4 * lam)) ↔
        Complex.normSq φ = μ ^ 2 / (2 * lam)) := by
  have hs : higgsV μ lam φ = -(μ ^ 4 / (4 * lam)) + lam * (Complex.normSq φ - μ ^ 2 / (2 * lam)) ^ 2 := by
    unfold higgsV; field_simp; ring
  rw [hs]
  constructor
  · have := sq_nonneg (Complex.normSq φ - μ ^ 2 / (2 * lam)); nlinarith
  · constructor
    · intro h
      have h2 : lam * (Complex.normSq φ - μ ^ 2 / (2 * lam)) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · linarith
      · have := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h3; linarith
    · intro h; rw [h]; ring


