-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.kin_kin_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T18:40:06.208982+00:00
-- url     : https://prove2.me/submissions/3e5d02d5-6567-4101-80b6-0b8a821cd172

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.kin_kin_comm
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_coreD_sum
import Theorems.Thm_BookProof_GaussCoreQuadBounds_coreD_comm
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution (c : Fin D → ℂ) (p : MvPolynomial (Fin D) ℂ) :
    (∑ k : Fin D, coreD k (coreD k (∑ j : Fin D, c j • coreD j (coreD j p))))
      = ∑ j : Fin D, c j • coreD j (coreD j (∑ k : Fin D, coreD k (coreD k p))) := by

  have hswap : ∀ (j k : Fin D) (q : MvPolynomial (Fin D) ℂ),
      coreD k (coreD k (coreD j (coreD j q))) = coreD j (coreD j (coreD k (coreD k q))) := by
    intro j k q
    calc coreD k (coreD k (coreD j (coreD j q)))
        = coreD k (coreD j (coreD k (coreD j q))) := by rw [coreD_comm k j (coreD j q)]
      _ = coreD j (coreD k (coreD k (coreD j q))) := coreD_comm k j (coreD k (coreD j q))
      _ = coreD j (coreD k (coreD j (coreD k q))) := by rw [coreD_comm k j q]
      _ = coreD j (coreD j (coreD k (coreD k q))) := by rw [coreD_comm k j (coreD k q)]
  calc (∑ k : Fin D, coreD k (coreD k (∑ j : Fin D, c j • coreD j (coreD j p))))
      = ∑ k : Fin D, ∑ j : Fin D, c j • coreD k (coreD k (coreD j (coreD j p))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [coreD_sum, coreD_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [coreD_smul, coreD_smul]
    _ = ∑ j : Fin D, ∑ k : Fin D, c j • coreD j (coreD j (coreD k (coreD k p))) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
          rw [hswap j k p]
    _ = ∑ j : Fin D, c j • coreD j (coreD j (∑ k : Fin D, coreD k (coreD k p))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [coreD_sum, coreD_sum, Finset.smul_sum]
