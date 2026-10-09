-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.gcSeq_ext_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:52:31.496979+00:00
-- url     : https://prove2.me/submissions/e84eec19-493c-4816-b719-537042fe2d14

-- Generated from ChapterQgOuterFockCoreFL.lean — solution of BookProof.QgOuterFockCoreFL.CoreData.gcSeq_ext_tendsto
import Mathlib
import Definitions.Def_ChapterQgOuterFockCoreFL
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_gcSeq_tendsto
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_gcSeq_op_tendsto
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_apply
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
    Tendsto (fun k => d.ext (d.gcSeq x k)) atTop (𝓝 (d.ext x)) := by

  have hs : Tendsto (fun k => d.C.op (d.gcSeq x k) + ((d.gcSeq x k : d.C.dom) : F)) atTop
      (𝓝 (d.C.op x + (x : F))) := (d.gcSeq_op_tendsto x).add (d.gcSeq_tendsto x)
  simp only [ext_apply]
  exact (d.extCLM.continuous.tendsto _).comp hs
