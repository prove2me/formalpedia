-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.isHermCol_diagCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:23:41.864031+00:00
-- url     : https://prove2.me/submissions/bf06374d-2bdd-407e-b6bd-ea6027cf687b

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.isHermCol_diagCol
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℕ → ℝ) : IsHermCol (diagCol lam) := by

  intro j k
  classical
  rcases eq_or_ne j k with h | h
  · subst h
    simp [diagCol]
  · rw [diagCol, diagCol, Finsupp.single_apply, Finsupp.single_apply, if_neg h.symm,
      if_neg h, map_zero]
