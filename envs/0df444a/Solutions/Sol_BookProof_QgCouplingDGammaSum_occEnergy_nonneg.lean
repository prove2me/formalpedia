-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.occEnergy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:23:11.33614+00:00
-- url     : https://prove2.me/submissions/972530e3-fcc3-42ff-9b28-e2fe9503e28c

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.occEnergy_nonneg
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
theorem solution {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) (α : Conf) :
    0 ≤ occEnergy lam α := Finset.sum_nonneg fun k _ => mul_nonneg (hlam k) (Nat.cast_nonneg _)
