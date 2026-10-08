-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.gcSeq_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T23:02:48.007144+00:00
-- url     : https://prove2.me/submissions/1507dc76-585f-4ce3-887d-fd4a6056d0b4

-- Generated from ChapterQgOuterFockCoreFL.lean — solution of BookProof.QgOuterFockCoreFL.CoreData.gcSeq_tendsto
import Mathlib
import Definitions.Def_ChapterQgOuterFockCoreFL
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_gcSeq_norm_lt
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_tendsto_inv_succ
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData




open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.QgOuterFockFL
open BookProof.YangMillsFriedrichs
open BookProof.EsaClosure
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore
open Filter Topology

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (d : CoreData F)

set_option maxHeartbeats 1000000 in
theorem solution (x : d.C.dom) :
    Tendsto (fun k => ((d.gcSeq x k : d.C.dom) : F)) atTop (𝓝 (x : F)) := by

  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => (d.gcSeq_norm_lt x k).le)
    tendsto_inv_succ
