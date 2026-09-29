-- Prove2me | solution 1 for BookProof.FockOneParticleGap.fock_mass_gap_of_certified_bands
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:36:51.118624+00:00
-- url     : https://prove2.me/submissions/ff9674df-924e-46fd-a9c9-b0dcbc28b21c

-- Generated from ChapterFockOneParticleGap.lean — solution of BookProof.FockOneParticleGap.fock_mass_gap_of_certified_bands
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
import Theorems.Thm_BookProof_FockOneParticleGap_dGamma_diagCol_vac
import Theorems.Thm_BookProof_FockOneParticleGap_fock_gap_quadForm
import Theorems.Thm_BookProof_FockOneParticleGap_band_endpoints_tendsto
import Theorems.Thm_BookProof_FockOneParticleGap_le_of_band
open BookProof.FockOneParticleGap













noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution {e : ℕ → ℝ} {lo hi : ℕ → ℝ} {lam mu : ℝ}
    (hmu : 0 ≤ mu) (hband : ∀ m, lam ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0))
    {m₀ : ℕ} (hlo : mu ≤ lo m₀) (hedge : ∀ k, lam ≤ e k) :
    Tendsto lo atTop (𝓝 lam) ∧ mu ≤ lam ∧ dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by

  refine ⟨(band_endpoints_tendsto hband hwidth).1, le_of_band hband hlo,
    dGamma_diagCol_vac e, fun u h0 => ?_⟩
  exact fock_gap_quadForm hmu (fun k => le_trans (le_of_band hband hlo) (hedge k)) h0
