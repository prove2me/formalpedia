-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.comparison_friedrichs
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:36:11.739208+00:00
-- url     : https://prove2.me/submissions/476b5aa1-fbe3-47d2-b461-c85e43acb66d

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.comparison_friedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_isHermCol_finsetSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_isPosCol_finsetSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_isHermCol_numberCol
import Theorems.Thm_BookProof_QgCouplingDGammaSum_isPosCol_numberCol
import Theorems.Thm_BookProof_QgCouplingDGammaSum_isHermCol_add
import Theorems.Thm_BookProof_QgCouplingDGammaSum_isPosCol_add
import Theorems.Thm_BookProof_FockSecondQuantization_dGamma_friedrichs_extension
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFockOneParticleGap
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
      IsPositiveSelfAdjointExtension (dGammaOp (comparisonCol s cols)) A :=
  dGamma_friedrichs_extension
      (isHermCol_add (isHermCol_finsetSum hherm) isHermCol_numberCol)
      (isPosCol_add (isPosCol_finsetSum hpos) isPosCol_numberCol)
