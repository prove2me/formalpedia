-- Prove2me | solution 1 for BookProof.SqSumOuterFamily.SqFamily.esa_farisLavine
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:16:32.663993+00:00
-- url     : https://prove2.me/submissions/c3a48f02-1d6d-46b8-a9d3-4fff77e53b73

import Definitions.Def_ChapterSqSumOuterFamily
import Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_secExt_core
import Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_secExt_commForm_le
import Theorems.Thm_BookProof_QgOuterFockFL_dsFibOp_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_QgOuterFockFL_dsFibOp_fib

open BookProof.DirectSumEsa
open BookProof.FarisLavine
open BookProof.HermiteProductCore
open BookProof.QgOuterFockFL
open BookProof.SqSumOuterFamily

noncomputable section

variable (F : SqFamily)

theorem solution :
    EssentiallySelfAdjointOn (outerFriedDom F.dim)
        (dsFibOp (fun n : ℕ => harmFried (F.dim n)) F.secExt F.flK F.secExt_rel) ∧
      ∀ x : outerCore F.dim, ∃ h : (x : outerFock F.dim) ∈ outerFriedDom F.dim,
        dsFibOp (fun n : ℕ => harmFried (F.dim n)) F.secExt F.flK F.secExt_rel
            ⟨(x : outerFock F.dim), h⟩ = F.outerHam x := by
  refine ⟨BookProof.QgOuterFockFL.dsFibOp_essentiallySelfAdjointOn
      F.flc_nonneg F.secExt_rel F.secExt_symmetricOn F.secExt_commForm_le,
    fun x => ⟨outerCore_le_friedDom F.dim x.2, ?_⟩⟩
  apply lp.ext
  funext n
  rw [BookProof.QgOuterFockFL.dsFibOp_fib]
  exact F.secExt_core n
    ⟨((x : outerFock F.dim) : ∀ n : ℕ, L2d (F.dim n)) n, x.2.2 n⟩ _
