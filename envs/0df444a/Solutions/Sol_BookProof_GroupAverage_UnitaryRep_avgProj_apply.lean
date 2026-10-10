-- Prove2me | solution 1 for BookProof.GroupAverage.UnitaryRep.avgProj_apply
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:29:00.187932+00:00
-- url     : https://prove2.me/submissions/9d6de9f0-cccf-4103-b157-1730b15ec872

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.GroupAverage
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa

noncomputable section

theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (G : Type*) [Group G] [Fintype G] (rep : UnitaryRep G F) (x : F) :
    rep.avgProj x = ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, rep.act g x := by
  simp [UnitaryRep.avgProj, LinearMap.sum_apply]
