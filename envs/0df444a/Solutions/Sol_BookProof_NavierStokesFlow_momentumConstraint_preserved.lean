-- Prove2me | solution 1 for BookProof.NavierStokesFlow.momentumConstraint_preserved
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:15:05.058252+00:00
-- url     : https://prove2.me/submissions/bc0131fe-643c-4d8b-81b4-b4c8fc79fdcb

import Definitions.Def_ChapterFreeFieldConstraint

-- Direct proof from the registered statement using Mathlib.
theorem solution {n : ℕ} (D H A : Matrix (Fin n) (Fin n) ℂ)
    (hDH : BookProof.FreeFieldConstraint.bracket D H = 0)
    (hDA : BookProof.FreeFieldConstraint.bracket D A = 0) :
    BookProof.FreeFieldConstraint.bracket D (BookProof.FreeFieldConstraint.bracket H A) = 0 := by
  have hDH' : Commute D H := sub_eq_zero.mp hDH
  have hDA' : Commute D A := sub_eq_zero.mp hDA
  exact sub_eq_zero.mpr
    ((hDH'.mul_right hDA').sub_right (hDA'.mul_right hDH')).eq

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
