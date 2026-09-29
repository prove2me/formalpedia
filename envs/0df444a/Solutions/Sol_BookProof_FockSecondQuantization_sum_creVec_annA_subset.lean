-- Prove2me | solution 1 for BookProof.FockSecondQuantization.sum_creVec_annA_subset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:30:06.513581+00:00
-- url     : https://prove2.me/submissions/1329fa0d-20d9-465f-93a3-30223fe5b482

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.sum_creVec_annA_subset
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_annA_eq_zero_of_not_mem_modes
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) {K L : Finset ℕ}
    (hKL : K ⊆ L) (hK : modes u ⊆ K) :
    ∑ k ∈ K, creVec (col k) (annA k u) = ∑ k ∈ L, creVec (col k) (annA k u) :=
  Finset.sum_subset hKL fun k _ hk => by
      rw [annA_eq_zero_of_not_mem_modes (fun hc => hk (hK hc)), map_zero]
