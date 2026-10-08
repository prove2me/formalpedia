-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.shiftCol_diagCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:17:57.6089+00:00
-- url     : https://prove2.me/submissions/62ba0a2c-d5ae-4bbe-8b8a-02452c9d1dbc

-- Generated from ChapterFockNumberPreservingGap.lean — solution of BookProof.FockNumberPreservingGap.shiftCol_diagCol
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
open BookProof.FockNumberPreservingGap



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (e : ℕ → ℝ) (mu : ℝ) :
    shiftCol (diagCol e) mu = diagCol fun k => e k - mu := by

  funext k
  refine Finsupp.ext fun j => ?_
  simp only [shiftCol, diagCol, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul]
  split_ifs with h
  · push_cast; ring
  · ring
