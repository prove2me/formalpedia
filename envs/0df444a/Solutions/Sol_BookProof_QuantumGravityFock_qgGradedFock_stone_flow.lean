-- Prove2me | solution 1 for BookProof.QuantumGravityFock.qgGradedFock_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:52:17.17932+00:00
-- url     : https://prove2.me/submissions/30168292-5564-4679-8a00-e45468a5adc2

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFockSecondQuantization
import Mathlib
import Definitions.Def_ChapterQuantumGravityFock
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_hasZeroDeficiencyOn
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_isSymmetricDom
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGradedFock_stone_flow
open BookProof.EsaClosure
open BookProof.StoneBridge
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section


theorem solution (omega g : ℕ → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (lp (fun _ : GradedIdx => ℂ) 2))
      (U : ℝ → (lp (fun _ : GradedIdx => ℂ) 2 →L[ℂ] lp (fun _ : GradedIdx => ℂ) 2)),
      IsSelfAdjointExtension
        ((lpFiniteModes GradedIdx).subtype.comp (qgGradedHam omega g)) T.op ∧ IsStoneFlow T U := by
  have hsym : SymmetricOn (lpFiniteModes GradedIdx)
      ((lpFiniteModes GradedIdx).subtype.comp (qgGradedHam omega g)) := by
    intro x y
    exact BookProof.NavierStokesFlow.FockOfFock.lpDiag_isSymmetricDom _ x y
  have hesa : EssentiallySelfAdjointOn (lpFiniteModes GradedIdx)
      ((lpFiniteModes GradedIdx).subtype.comp (qgGradedHam omega g)) := by
    obtain ⟨h1, h2⟩ := BookProof.NavierStokesFlow.FockOfFock.lpDiag_hasZeroDeficiencyOn (qgGradedSymbol omega g)
    constructor
    · intro w hw
      apply h1 w
      intro v
      rw [inner_smul_right]
      exact hw v
    · intro w hw
      apply h2 w
      intro v
      rw [inner_neg_right, inner_smul_right, ← neg_mul]
      exact hw v
  exact BookProof.StoneBridge.exists_stone_flow_of_esa _ BookProof.NavierStokesFlow.lpFiniteModes_dense hsym hesa

