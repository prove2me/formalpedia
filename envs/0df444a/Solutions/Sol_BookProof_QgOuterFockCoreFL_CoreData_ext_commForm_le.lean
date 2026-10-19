-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.ext_commForm_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T20:29:34.172977+00:00
-- url     : https://prove2.me/submissions/b70bf09a-6e84-434f-a19a-20a548ed15a0

-- Generated from ChapterQgOuterFockCoreFL.lean — solution of BookProof.QgOuterFockCoreFL.CoreData.ext_commForm_le
import Mathlib
import Definitions.Def_ChapterQgOuterFockCoreFL
import Theorems.Thm_BookProof_QgOuterFockCoreFL_commForm_congr
import Theorems.Thm_BookProof_QgOuterFockCoreFL_quadForm_congr

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterLeafGaps
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
theorem solution {c : ℝ}
    (hcomm : ∀ p : d.C₀, |commForm d.H₀ d.coreN p| ≤ c * quadForm d.coreN p)
    (x : d.C.dom) : |commForm d.ext d.C.op x| ≤ c * quadForm d.C.op x := by

  have hstep : ∀ k, |commForm d.ext d.C.op (d.gcSeq x k)|
      ≤ c * quadForm d.C.op (d.gcSeq x k) := by
    intro k
    have h := hcomm ⟨((d.gcSeq x k : d.C.dom) : F), d.gcSeq_mem x k⟩
    have hc1 : commForm d.ext d.C.op (d.gcSeq x k)
        = commForm d.H₀ d.coreN ⟨((d.gcSeq x k : d.C.dom) : F), d.gcSeq_mem x k⟩ :=
      commForm_congr _ _ _ _ _ _ (d.ext_gcSeq x k) (d.coreN_gcSeq x k).symm
    have hc2 : quadForm d.C.op (d.gcSeq x k)
        = quadForm d.coreN ⟨((d.gcSeq x k : d.C.dom) : F), d.gcSeq_mem x k⟩ :=
      quadForm_congr _ _ _ _ rfl (d.coreN_gcSeq x k).symm
    rw [hc1, hc2]
    exact h
  exact le_of_tendsto_of_tendsto ((d.ext_commForm_tendsto x).abs)
    ((d.quadForm_tendsto x).const_mul c) (Eventually.of_forall hstep)
