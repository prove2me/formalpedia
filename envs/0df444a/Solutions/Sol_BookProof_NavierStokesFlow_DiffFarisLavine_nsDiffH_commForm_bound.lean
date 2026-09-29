-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_commForm_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T09:58:01.088968+00:00
-- url     : https://prove2.me/submissions/f9b15782-0302-403f-82cb-02e98dc759ad

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — solution of BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_commForm_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_embedCore_surjective
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_quadForm_nsDiffN_embedCore
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_commForm_embedCore
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_commForm_bound
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesDifferentialL2

open BookProof.FarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiffFarisLavine














open MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

















variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem solution :
    ∃ cst : ℝ, 0 ≤ cst ∧ ∀ f : polyGaussCore (d := 3),
      |commForm ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c))
          ((polyGaussCore (d := 3)).subtype.comp (nsDiffN (diffMu A c))) f|
        ≤ cst * quadForm ((polyGaussCore (d := 3)).subtype.comp (nsDiffN (diffMu A c))) f := by

  obtain ⟨cst, hcst, hbound⟩ :=
    SignedShift.listH_commForm_bound (hopList A (seqConst c))
      (fun β => velSym_ge_one (velMu_nonneg A (seqConst c)) β)
  refine ⟨cst, hcst, fun f => ?_⟩
  obtain ⟨x, rfl⟩ := embedCore_surjective f
  simp only [diffMu]
  rw [commForm_embedCore, quadForm_nsDiffN_embedCore]
  exact hbound _
