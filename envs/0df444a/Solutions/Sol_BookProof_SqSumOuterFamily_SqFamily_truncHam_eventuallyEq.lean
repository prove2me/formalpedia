-- Prove2me | solution 1 for BookProof.SqSumOuterFamily.SqFamily.truncHam_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T21:10:42.665056+00:00
-- url     : https://prove2.me/submissions/f0ab5a88-58e6-4147-80d8-810ed1843777

-- Generated from ChapterSqSumOuterSingleTime.lean — solution of BookProof.SqSumOuterFamily.SqFamily.truncHam_eventuallyEq
import Mathlib
import Definitions.Def_ChapterSqSumOuterSingleTime
import Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_truncHam_eq_of_support
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
theorem solution (F : SqFamily) (x : outerCore F.dim) :
    ∀ᶠ N in atTop, (truncHam F N x : outerFock F.dim) = F.outerHam x := by

  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n : ℕ,
      ((x : outerFock F.dim) : ∀ n : ℕ, L2d (F.dim n)) n ≠ 0 → n ≤ N₀ := by
    obtain ⟨N₀, hN₀⟩ := x.2.1.bddAbove
    exact ⟨N₀, fun n hn => hN₀ hn⟩
  filter_upwards [eventually_ge_atTop N₀] with N hN
  refine truncHam_eq_of_support F x fun n hn => ?_
  by_contra hne
  exact absurd (hN₀ n hne) (by omega)
