-- Prove2me | solution 1 for BookProof.FockSecondQuantization.inner_creVec_annA
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:37:48.602183+00:00
-- url     : https://prove2.me/submissions/88264d29-c787-4886-9f27-81f21298e078

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.inner_creVec_annA
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_toLpL_apply
import Theorems.Thm_BookProof_FockSecondQuantization_inner_creA_left
import Theorems.Thm_BookProof_FockSecondQuantization_creVec_apply
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) (k : ℕ) {L : Finset ℕ}
    (h : (col k).support ⊆ L) :
    (inner ℂ (toLp (creVec (col k) (annA k u))) (toLp v) : ℂ)
      = ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
          * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by

  have hexp : toLp (creVec (col k) (annA k u))
      = ∑ j ∈ (col k).support, (col k) j • toLp (creA j (annA k u)) := by
    rw [creVec_apply, ← toLpL_apply, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, toLpL_apply]
  rw [hexp, sum_inner, ← Finset.sum_subset h (fun j _ hj => by
    rw [Finsupp.notMem_support_iff.mp hj, map_zero, zero_mul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_creA_left]
