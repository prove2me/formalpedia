-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.number_quadForm_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:25:55.310393+00:00
-- url     : https://prove2.me/submissions/3957b918-c08e-41ef-82c4-124af774558c

-- Generated from ChapterFockNumberPreservingGap.lean — solution of BookProof.FockNumberPreservingGap.number_quadForm_ge
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Theorems.Thm_BookProof_FockOneParticleGap_fock_gap_quadForm
open BookProof.FockNumberPreservingGap



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution {u : FockAlg} (h0 : u 0 = 0) :
    ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma numberCol u)) : ℂ).re := by

  have h := fock_gap_quadForm (e := fun _ => (1 : ℝ)) (mu := 1) zero_le_one
    (fun _ => le_rfl) h0
  rw [one_mul] at h
  exact h
