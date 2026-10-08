-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.ext_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T23:18:25.172654+00:00
-- url     : https://prove2.me/submissions/72a1f129-7134-4e9d-804b-24c730dc5cff

-- Generated from ChapterQgOuterFockCoreFL.lean — solution of BookProof.QgOuterFockCoreFL.CoreData.ext_core
import Mathlib
import Definitions.Def_ChapterQgOuterFockCoreFL
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_coreRange_denseRange
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_coreRange_isUniformInducing
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
theorem solution (p : d.C₀) : d.ext ⟨(p : F), d.gc.le p.2⟩ = d.H₀ p := by

  have hext := ContinuousLinearMap.extend_eq d.resolvedCLM d.coreRange_denseRange
    d.coreRange_isUniformInducing (d.coreEquiv p)
  calc d.ext ⟨(p : F), d.gc.le p.2⟩
      = (d.resolvedCLM.extend d.coreRange.subtypeL)
          (d.coreRange.subtypeL (d.coreEquiv p)) := rfl
    _ = d.resolvedCLM (d.coreEquiv p) := hext
    _ = d.H₀ p := by simp [resolvedCLM, resolvedMap]
