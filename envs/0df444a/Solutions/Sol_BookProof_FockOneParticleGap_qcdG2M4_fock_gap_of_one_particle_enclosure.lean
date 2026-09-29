-- Prove2me | solution 1 for BookProof.FockOneParticleGap.qcdG2M4_fock_gap_of_one_particle_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:37:45.84899+00:00
-- url     : https://prove2.me/submissions/939994ff-1784-4642-987f-bb9dee35a0c2

-- Generated from ChapterFockOneParticleGap.lean — solution of BookProof.FockOneParticleGap.qcdG2M4_fock_gap_of_one_particle_enclosure
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
import Theorems.Thm_BookProof_FockOneParticleGap_dGamma_diagCol_vac
import Theorems.Thm_BookProof_FockOneParticleGap_fock_gap_quadForm
import Theorems.Thm_BookProof_FockOneParticleGap_le_of_band
open BookProof.FockOneParticleGap













noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution {e : ℕ → ℝ} {lo hi : ℕ → ℝ} {lam : ℝ}
    (hband : ∀ m, lam ∈ Set.Icc (lo m) (hi m)) {m₀ : ℕ}
    (hlo : (1.932 : ℝ) ≤ lo m₀) (hedge : ∀ k, lam ≤ e k) :
    (1.932 : ℝ) ≤ lam ∧ dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        (1.932 : ℝ) * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by

  have hlam : (1.932 : ℝ) ≤ lam := le_of_band hband hlo
  refine ⟨hlam, dGamma_diagCol_vac e, fun u h0 => ?_⟩
  exact fock_gap_quadForm (by norm_num) (fun k => le_trans hlam (hedge k)) h0
