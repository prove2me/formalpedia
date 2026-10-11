-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.quadForm_dGammaOp_finsetSum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:22:41.818912+00:00
-- url     : https://prove2.me/submissions/a7c0a14f-e7b2-4c2d-bc54-7c68ad2e9d9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.quadForm_dGammaOp_finsetSum
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_finsetSum_col
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ))
    (x : lpFiniteModes Conf) :
    quadForm (dGammaOp (fun k => ∑ i ∈ s, cols i k)) x
      = ∑ i ∈ s, quadForm (dGammaOp (cols i)) x := by

  rw [quadForm, dGammaOp_finsetSum_col s cols x, inner_sum, Complex.re_sum]
  rfl
