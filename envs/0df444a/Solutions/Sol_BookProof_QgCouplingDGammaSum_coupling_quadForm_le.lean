-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.coupling_quadForm_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:22:42.81661+00:00
-- url     : https://prove2.me/submissions/bf584509-4f41-4aa4-af46-51ee007619a5

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.coupling_quadForm_le
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_quadForm_dGammaOp_finsetSum
import Theorems.Thm_BookProof_FockSecondQuantization_dGammaOp_quadForm_nonneg
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
theorem solution {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)}
    (hpos : ∀ i ∈ s, IsPosCol (cols i)) {i : ι} (hi : i ∈ s) (x : lpFiniteModes Conf) :
    quadForm (dGammaOp (cols i)) x
      ≤ quadForm (dGammaOp (fun k => ∑ j ∈ s, cols j k)) x := by

  rw [quadForm_dGammaOp_finsetSum]
  exact Finset.single_le_sum
    (fun j hj => dGammaOp_quadForm_nonneg (hpos j hj) x) hi
