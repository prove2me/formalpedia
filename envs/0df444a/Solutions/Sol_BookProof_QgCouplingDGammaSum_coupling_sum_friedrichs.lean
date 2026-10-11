-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.coupling_sum_friedrichs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:37:19.885865+00:00
-- url     : https://prove2.me/submissions/6f5cb06c-4bd3-4122-aeac-0850de8c052b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.coupling_sum_friedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_finsetSum_col_eq
import Theorems.Thm_BookProof_QgCouplingDGammaSum_coupling_friedrichs
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)}
    (hherm : ∀ i ∈ s, IsHermCol (cols i)) (hpos : ∀ i ∈ s, IsPosCol (cols i)) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (∑ i ∈ s, dGammaOp (cols i)) A := by

  rw [← dGammaOp_finsetSum_col_eq s cols]
  exact coupling_friedrichs hherm hpos
