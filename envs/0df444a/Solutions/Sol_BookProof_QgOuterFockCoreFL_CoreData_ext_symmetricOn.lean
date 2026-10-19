-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.ext_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T20:29:32.857784+00:00
-- url     : https://prove2.me/submissions/ccbba7f6-62cf-4f53-8df5-62766c082ec6

-- Generated from ChapterQgOuterFockCoreFL.lean — solution of BookProof.QgOuterFockCoreFL.CoreData.ext_symmetricOn
import Mathlib
import Definitions.Def_ChapterQgOuterFockCoreFL

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
theorem solution (hsym : SymmetricOn d.C₀ d.H₀) : SymmetricOn d.C.dom d.ext := by

  intro x z
  have hl : Tendsto (fun k => (inner ℂ (d.ext (d.gcSeq x k))
      ((d.gcSeq z k : d.C.dom) : F) : ℂ)) atTop (𝓝 (inner ℂ (d.ext x) (z : F))) :=
    (d.gcSeq_ext_tendsto x).inner (d.gcSeq_tendsto z)
  have hr : Tendsto (fun k => (inner ℂ ((d.gcSeq x k : d.C.dom) : F)
      (d.ext (d.gcSeq z k)) : ℂ)) atTop (𝓝 (inner ℂ (x : F) (d.ext z))) :=
    (d.gcSeq_tendsto x).inner (d.gcSeq_ext_tendsto z)
  have heq : ∀ k, (inner ℂ (d.ext (d.gcSeq x k)) ((d.gcSeq z k : d.C.dom) : F) : ℂ)
      = inner ℂ ((d.gcSeq x k : d.C.dom) : F) (d.ext (d.gcSeq z k)) := by
    intro k
    rw [d.ext_gcSeq x k, d.ext_gcSeq z k]
    exact hsym ⟨_, d.gcSeq_mem x k⟩ ⟨_, d.gcSeq_mem z k⟩
  exact tendsto_nhds_unique (by simpa only [heq] using hl) hr
