-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_restrict
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:10:02.893988+00:00
-- url     : https://prove2.me/submissions/a991781b-aac8-4f37-9dc0-a20802a64c8a

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — solution of BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_restrict
import Mathlib
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_embedCore_surjective
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_nsDiffH_embedCore
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_canH_coe_velH
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_diffMaxH_apply
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_polyGaussCore_le_diffMaxDom
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesDifferentialL2
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
    (diffMaxH A c).comp
        (Submodule.inclusion (polyGaussCore_le_diffMaxDom (velMu A (seqConst c))))
      = (polyGaussCore (d := 3)).subtype.comp (nsDiffH A c) := by

  refine LinearMap.ext fun f => ?_
  obtain ⟨x, rfl⟩ := embedCore_surjective f
  have hz : (Submodule.inclusion (polyGaussCore_le_diffMaxDom (velMu A (seqConst c)))
        (embedCore x))
      = diffMaxEquiv (velMu A (seqConst c))
          (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A (seqConst c)))) x) :=
    Subtype.ext rfl
  rw [LinearMap.comp_apply, hz, diffMaxH_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    nsDiffH_embedCore, canH_coe_velH]
