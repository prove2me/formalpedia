-- Prove2me | solution 2 for BookProof.NavierStokes.ghostNumber_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T17:36:32.4447+00:00
-- url     : https://prove2.me/submissions/97f668fb-5acf-4da4-8afb-443aa7456c1f

import Definitions.Def_ChapterNavierStokes

open BookProof.NavierStokes Matrix

theorem solution : ghostNumberᴴ = ghostNumber := by
  simp [ghostNumber, ghostCreate, Matrix.conjTranspose_mul]

#print axioms solution
