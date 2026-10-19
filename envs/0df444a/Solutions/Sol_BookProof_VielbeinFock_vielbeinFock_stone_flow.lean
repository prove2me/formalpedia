-- Prove2me | solution 1 for BookProof.VielbeinFock.vielbeinFock_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:46:58.682969+00:00
-- url     : https://prove2.me/submissions/8ba50c1b-3c0a-472d-9b12-c88c2bb01eb4

import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterVielbeinFiberFock
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Theorems.Thm_BookProof_VielbeinFock_vielbeinFockCore_dense
import Theorems.Thm_BookProof_VielbeinFock_vielbeinFock_symmetric
import Theorems.Thm_BookProof_VielbeinFock_vielbeinFock_esa
-- Generated from ChapterVielbeinFiberFock.lean — theorem BookProof.VielbeinFock.vielbeinFock_stone_flow
open BookProof.EsaClosure
open BookProof.StoneBridge
open BookProof.VielbeinFock


open Filter Topology MeasureTheory


open BookProof.Starobinsky BookProof.ScalaronEsa BookProof.ScalaronFock
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.FarisLavine BookProof.ChapterStoneResolvent

noncomputable section


theorem solution (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (vielbeinFock d))
      (U : ℝ → (vielbeinFock d →L[ℂ] vielbeinFock d)),
      IsSelfAdjointExtension (vielbeinFockHamiltonian M alpha d om) T.op ∧ IsStoneFlow T U := by
  exact BookProof.StoneBridge.exists_stone_flow_of_esa _ (BookProof.VielbeinFock.vielbeinFockCore_dense d)
    (BookProof.VielbeinFock.vielbeinFock_symmetric M alpha d om) (BookProof.VielbeinFock.vielbeinFock_esa M alpha d om)

