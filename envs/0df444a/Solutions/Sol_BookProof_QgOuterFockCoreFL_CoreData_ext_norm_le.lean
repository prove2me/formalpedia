-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.ext_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:42:10.02064+00:00
-- url     : https://prove2.me/submissions/fe79dfc2-10ab-48cf-97a0-08d8c520b87f

-- Generated from ChapterQgOuterFockCoreFL.lean — solution of BookProof.QgOuterFockCoreFL.CoreData.ext_norm_le
import Mathlib
import Definitions.Def_ChapterQgOuterFockCoreFL
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_norm_extCLM_le
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
theorem solution (x : d.C.dom) : ‖d.ext x‖ ≤ d.K * ‖d.C.op x + (x : F)‖ := by

  rw [ext_apply]
  calc ‖d.extCLM (d.C.op x + (x : F))‖ ≤ ‖d.extCLM‖ * ‖d.C.op x + (x : F)‖ :=
        d.extCLM.le_opNorm _
    _ ≤ d.K * ‖d.C.op x + (x : F)‖ :=
        mul_le_mul_of_nonneg_right d.norm_extCLM_le (norm_nonneg _)
