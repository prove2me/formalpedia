-- Prove2me | solution 1 for BookProof.SqSumOuterFamily.SqFamily.truncHam_eq_of_support
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T21:10:24.409617+00:00
-- url     : https://prove2.me/submissions/cb91f18e-1f1c-4602-ba65-e8cd79d23bc8

-- Generated from ChapterSqSumOuterSingleTime.lean — solution of BookProof.SqSumOuterFamily.SqFamily.truncHam_eq_of_support
import Mathlib
import Definitions.Def_ChapterSqSumOuterSingleTime
import Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_trunc_secHam_eq_of_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSqSumOuterFamily
open BookProof.SqSumOuterFamily
open BookProof.SqSumOuterFamily.SqFamily




open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert BookProof.SirkSingleTime
open BookProof.QgTimeIndependent BookProof.QgTruncationResolvent
open BookProof.DirectSumEsa BookProof.HermiteProductCore
open BookProof.HermiteProductCore

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (F : SqFamily) (x : outerCore F.dim) {N : ℕ}
    (hsupp : ∀ n : ℕ, N < n → ((x : outerFock F.dim) : ∀ n : ℕ, L2d (F.dim n)) n = 0) :
    (truncHam F N x : outerFock F.dim) = F.outerHam x := by

  refine lp.ext (funext fun n => ?_)
  have h2 : ((F.outerHam x : outerFock F.dim) : ∀ n : ℕ, L2d (F.dim n)) n
      = F.secHam n
          ((⟨((x : outerFock F.dim) : ∀ n : ℕ, L2d (F.dim n)) n, x.2.2 n⟩ :
            ↥(polyGaussCore (d := F.dim n))) : polyGaussCore (d := F.dim n)) := rfl
  by_cases h : n ≤ N
  · rw [truncHam_coe, h2, trunc_secHam_eq_of_le F h]
    rfl
  · have hzero : (⟨((x : outerFock F.dim) : ∀ n : ℕ, L2d (F.dim n)) n, x.2.2 n⟩ :
        ↥(polyGaussCore (d := F.dim n))) = 0 :=
      Subtype.ext (hsupp n (by omega))
    rw [truncHam_coe, h2]
    simp only [hzero, LinearMap.map_zero]
    exact LinearMap.map_zero ((F.trunc N).secHam n)
