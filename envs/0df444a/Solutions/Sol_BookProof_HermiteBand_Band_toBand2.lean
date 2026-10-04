-- Prove2me | solution 1 for BookProof.HermiteBand.Band.toBand2
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:34:01.407517+00:00
-- url     : https://prove2.me/submissions/0fe8a56a-2220-40e0-a681-a75de34d8f5f

/-
Adapted from leonardopedro/timepiece, ChapterHermiteBandCalculus.lean,
commit 61595bca99e3b8d8b8df51a2c3043b64597e24f9 (Apache-2.0).
Helper proofs, where needed, are included directly; no platform theorem imports.
-/
import Definitions.Def_ChapterHermiteBandCalculus

open BookProof.HermiteBand
open scoped BigOperators

noncomputable section

variable {d : ℕ}

private theorem growth_le (n : ℕ) : g1 n ≤ g2 n := by
  have hsq : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (n : ℝ) + 1 by positivity),
      Real.sqrt_nonneg ((n : ℝ) + 1),
      sq_nonneg (Real.sqrt ((n : ℝ) + 1) - 1)]
  simpa [g1, g2] using hsq

theorem solution {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    {M : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (h : Band T 1 M C g1) : Band T 2 M C g2 := by
  intro α
  obtain ⟨f, hrep, hcard, hband, hcoef⟩ := h α
  refine ⟨f, hrep, hcard, fun β hβ => le_trans (hband β hβ) (by norm_num), fun β => ?_⟩
  exact le_trans (hcoef β) (mul_le_mul_of_nonneg_left (growth_le α.degree) hC)

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
