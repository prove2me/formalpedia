-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteCanonical.amp_eq_sqrt_mul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:45:13.358638+00:00
-- url     : https://prove2.me/submissions/1006f665-e75a-4c1e-9c5e-63ef88a92b7d

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.amp_eq_sqrt_mul
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}
set_option autoImplicit false

theorem solution (κ : ℝ) (n : ℕ) :
    amp κ n = (κ / 2) * (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)) := by
  unfold amp
  rw [Real.sqrt_mul (by positivity : 0 ≤ (n : ℝ) + 1)]

#print axioms solution
