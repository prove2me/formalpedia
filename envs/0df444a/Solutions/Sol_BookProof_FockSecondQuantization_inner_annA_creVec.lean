-- Prove2me | solution 1 for BookProof.FockSecondQuantization.inner_annA_creVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:38:21.785103+00:00
-- url     : https://prove2.me/submissions/ae3c20ed-dcae-403f-bbc1-6eb701b8ef05

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.inner_annA_creVec
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_toLpL_apply
import Theorems.Thm_BookProof_FockSecondQuantization_inner_creA_right
import Theorems.Thm_BookProof_FockSecondQuantization_creVec_apply
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) (j : ℕ) {L : Finset ℕ}
    (h : (col j).support ⊆ L) :
    (inner ℂ (toLp u) (toLp (creVec (col j) (annA j v))) : ℂ)
      = ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by

  have hexp : toLp (creVec (col j) (annA j v))
      = ∑ k ∈ (col j).support, (col j) k • toLp (creA k (annA j v)) := by
    rw [creVec_apply, ← toLpL_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, toLpL_apply]
  rw [hexp, inner_sum, ← Finset.sum_subset h (fun k _ hk => by
    rw [Finsupp.notMem_support_iff.mp hk, zero_mul])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, inner_creA_right]
