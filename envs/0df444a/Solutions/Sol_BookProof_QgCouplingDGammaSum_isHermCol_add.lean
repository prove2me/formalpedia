-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.isHermCol_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:36:09.607014+00:00
-- url     : https://prove2.me/submissions/7290a645-2e29-49c2-857e-a3e40574d12d

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.isHermCol_add
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {a b : ℕ → (ℕ →₀ ℂ)} (ha : IsHermCol a) (hb : IsHermCol b) :
    IsHermCol (fun k => a k + b k) := by

  intro j k
  simp only [Finsupp.add_apply, map_add]
  rw [ha j k, hb j k]
