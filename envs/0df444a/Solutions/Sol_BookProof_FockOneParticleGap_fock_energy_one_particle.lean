-- Prove2me | solution 1 for BookProof.FockOneParticleGap.fock_energy_one_particle
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:30:04.817082+00:00
-- url     : https://prove2.me/submissions/ec93f71f-43fb-4ac3-a906-0c9d9ebd0cd3

-- Generated from ChapterFockOneParticleGap.lean — solution of BookProof.FockOneParticleGap.fock_energy_one_particle
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
import Theorems.Thm_BookProof_FockOneParticleGap_confEnergy_single
import Theorems.Thm_BookProof_FockOneParticleGap_re_inner_dGamma_diagCol
open BookProof.FockOneParticleGap













noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (e : ℕ → ℝ) (k : ℕ) :
    (inner ℂ (toLp (Finsupp.single (Finsupp.single k 1) (1 : ℂ)))
        (toLp (dGamma (diagCol e) (Finsupp.single (Finsupp.single k 1) (1 : ℂ)))) : ℂ).re
      = e k := by

  classical
  rw [re_inner_dGamma_diagCol,
    show (Finsupp.single (Finsupp.single k 1) (1 : ℂ)).support = {Finsupp.single k 1} from
      Finsupp.support_single_ne_zero _ one_ne_zero]
  simp [confEnergy_single]
