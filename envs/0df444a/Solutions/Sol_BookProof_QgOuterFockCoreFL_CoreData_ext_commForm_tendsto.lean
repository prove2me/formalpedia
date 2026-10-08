-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.ext_commForm_tendsto
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T23:31:34.532674+00:00
-- url     : https://prove2.me/submissions/17030e58-b0b1-4fd2-a72f-75709e401fa5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQgOuterFockCoreFL.lean — solution of BookProof.QgOuterFockCoreFL.CoreData.ext_commForm_tendsto
import Mathlib
import Definitions.Def_ChapterQgOuterFockCoreFL
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_gcSeq_op_tendsto
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_gcSeq_ext_tendsto
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
    Tendsto (fun k => commForm d.ext d.C.op (d.gcSeq x k)) atTop
      (𝓝 (commForm d.ext d.C.op x)) := by

  have h1 : Tendsto (fun k => (inner ℂ (d.ext (d.gcSeq x k)) (d.C.op (d.gcSeq x k)) : ℂ))
      atTop (𝓝 (inner ℂ (d.ext x) (d.C.op x))) :=
    (d.gcSeq_ext_tendsto x).inner (d.gcSeq_op_tendsto x)
  have h2 : Tendsto (fun k => (inner ℂ (d.C.op (d.gcSeq x k)) (d.ext (d.gcSeq x k)) : ℂ))
      atTop (𝓝 (inner ℂ (d.C.op x) (d.ext x))) :=
    (d.gcSeq_op_tendsto x).inner (d.gcSeq_ext_tendsto x)
  simp only [commForm]
  exact (Complex.reCLM.continuous.tendsto _).comp
    (((h1.sub h2).const_mul Complex.I))
