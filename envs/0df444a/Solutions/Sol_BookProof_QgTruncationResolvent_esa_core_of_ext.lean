-- Prove2me | solution 1 for BookProof.QgTruncationResolvent.esa_core_of_ext
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-27T05:58:49.484812+00:00
-- url     : https://prove2.me/submissions/5c53d03c-727c-4709-bc90-5cf478b74513

-- Generated from ChapterQgTruncationResolvent.lean — solution of BookProof.QgTruncationResolvent.esa_core_of_ext
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
-- The four gcSeq helper lemmas come from the leaf-gap bundle: importing them as
-- Theorems.* stubs would either collide with Def_ChapterLeafGaps (same fully
-- qualified names) or block forever (ext_gcSeq's stub is parked as a duplicate
-- declaration carried by that bundle).
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.QgTruncationResolvent




open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa
open BookProof.QgOuterFockCoreFL

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (d : CoreData F) (hesa : EssentiallySelfAdjointOn d.C.dom d.ext) :
    EssentiallySelfAdjointOn d.C₀ d.H₀ := by

  have key : ∀ z : ℂ, DeficiencyTrivialAt d.C.dom d.ext z → DeficiencyTrivialAt d.C₀ d.H₀ z := by
    intro z hz w hw
    refine hz w fun x => ?_
    have h1 : Tendsto (fun k => (inner ℂ (d.ext (d.gcSeq x k)) w : ℂ)) atTop
        (𝓝 (inner ℂ (d.ext x) w : ℂ)) := (d.gcSeq_ext_tendsto x).inner tendsto_const_nhds
    have h2 : Tendsto (fun k => z * (inner ℂ ((d.gcSeq x k : d.C.dom) : F) w : ℂ)) atTop
        (𝓝 (z * (inner ℂ (x : F) w : ℂ))) :=
      ((d.gcSeq_tendsto x).inner tendsto_const_nhds).const_mul z
    have heq : ∀ k, (inner ℂ (d.ext (d.gcSeq x k)) w : ℂ)
        = z * (inner ℂ ((d.gcSeq x k : d.C.dom) : F) w : ℂ) := by
      intro k
      rw [d.ext_gcSeq x k]
      exact hw ⟨_, d.gcSeq_mem x k⟩
    exact tendsto_nhds_unique (by simpa only [heq] using h1) h2
  exact ⟨key _ hesa.1, key _ hesa.2⟩
