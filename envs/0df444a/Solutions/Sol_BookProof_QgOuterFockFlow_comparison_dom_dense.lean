-- Prove2me | solution 1 for BookProof.QgOuterFockFlow.comparison_dom_dense
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:08:45.727026+00:00
-- url     : https://prove2.me/submissions/90faad23-7a83-4646-9120-c5346aa5cc6e

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQgOuterFockFlow
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterA4

set_option autoImplicit false

open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.QgOuterFockFL
open Filter Topology
open BookProof.FarisLavine BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato

noncomputable section

open BookProof.NavierStokesFlow.CanonicalVector BookProof.QgOuterFockFL BookProof.FarisLavine BookProof.QgOuterFockCoreFL BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure BookProof.ChapterSirkTrotterKato in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (C : Comparison F) : Dense ((C.dom : Submodule ℂ F) : Set F) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨x, hx⟩ := C.surj y
  have h0 : (inner ℂ (x : F) y : ℂ) = 0 := Submodule.inner_right_of_mem_orthogonal x.2 hy
  have hpos := C.pos x
  have hre : quadForm C.op x + ‖(x : F)‖ ^ 2 = 0 := by
    have := congrArg Complex.re h0
    rw [← hx, inner_add_right, Complex.add_re, inner_self_eq_norm_sq_to_K] at this
    unfold quadForm
    simpa [← Complex.ofReal_pow] using this
  have hn : ‖(x : F)‖ = 0 := by nlinarith [norm_nonneg (x : F)]
  have hx0 : x = 0 := by
    ext; simpa using hn
  rw [← hx, hx0]; simp

end
