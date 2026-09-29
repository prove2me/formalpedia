-- Prove2me | solution 1 for BookProof.FockSecondQuantization.dGamma_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:37:58.596701+00:00
-- url     : https://prove2.me/submissions/1019b551-cca5-4429-862e-4c51423b0bb0

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.dGamma_eq_sum
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_dGamma_eq_sum_aux
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (col : ℕ → (ℕ →₀ ℂ)) {u : FockAlg} {K : Finset ℕ} (hK : modes u ⊆ K) :
    dGamma col u = ∑ k ∈ K, creVec (col k) (annA k u) := dGamma_eq_sum_aux col u K hK
