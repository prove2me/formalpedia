-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.coupling_friedrichs
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:22:40.786063+00:00
-- url     : https://prove2.me/submissions/00531a17-f10a-47fe-b499-2ea3a25f4297

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.coupling_friedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_isHermCol_finsetSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_isPosCol_finsetSum
import Theorems.Thm_BookProof_FockSecondQuantization_dGamma_friedrichs_extension
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
      IsPositiveSelfAdjointExtension (dGammaOp (fun k => ∑ i ∈ s, cols i k)) A := dGamma_friedrichs_extension (isHermCol_finsetSum hherm) (isPosCol_finsetSum hpos)
