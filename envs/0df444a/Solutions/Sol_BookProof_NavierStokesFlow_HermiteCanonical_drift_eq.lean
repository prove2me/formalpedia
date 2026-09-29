-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteCanonical.drift_eq
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:45:11.637383+00:00
-- url     : https://prove2.me/submissions/b0079f70-b3a0-4405-b1d9-ad555356b12d

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.drift_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}
set_option autoImplicit false

theorem solution (hκ : 0 < κ) : drift κ = (κ : ℂ) • pos κ := by
  have hs0 : Real.sqrt (2 * κ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hp : Real.sqrt (κ / 2) * Real.sqrt (2 * κ) = κ := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ κ / 2)]
    have he : κ / 2 * (2 * κ) = κ ^ 2 := by ring
    rw [he, Real.sqrt_sq (le_of_lt hκ)]
  have hs : Real.sqrt (κ / 2) = κ * (1 / Real.sqrt (2 * κ)) := by
    field_simp [hs0]
    simpa only [mul_comm] using hp
  simp only [drift, pos, smul_smul, ← Complex.ofReal_mul, hs]

#print axioms solution
