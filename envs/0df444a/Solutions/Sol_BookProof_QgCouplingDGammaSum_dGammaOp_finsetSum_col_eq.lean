-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:21:58.09015+00:00
-- url     : https://prove2.me/submissions/42e97f05-6e3d-4328-990c-840427786e66

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_finsetSum_col
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
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
theorem solution (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ)) :
    dGammaOp (fun k => ∑ i ∈ s, cols i k) = ∑ i ∈ s, dGammaOp (cols i) := by

  refine LinearMap.ext fun x => ?_
  rw [dGammaOp_finsetSum_col s cols x, LinearMap.sum_apply]
