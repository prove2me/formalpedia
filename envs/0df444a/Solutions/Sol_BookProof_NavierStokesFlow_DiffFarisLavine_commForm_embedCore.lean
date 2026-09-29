-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.commForm_embedCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T09:57:57.545978+00:00
-- url     : https://prove2.me/submissions/b8f43239-500f-407d-9e70-6fc750c3e5de

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — solution of BookProof.NavierStokesFlow.DiffFarisLavine.commForm_embedCore
import Mathlib
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_nsDiffH_embedCore
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_nsDiffN_embedCore
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_canH_coe_velH
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesDifferentialL2

open BookProof.NavierStokesFlow.ThreeComponent
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
theorem solution (x : lpFiniteModes Vel) :
    commForm ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c))
        ((polyGaussCore (d := 3)).subtype.comp (nsDiffN (velMu A (seqConst c)))) (embedCore x)
      = commForm (velH A (seqConst c)) (diagMax (velSym (velMu A (seqConst c))))
          (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A (seqConst c)))) x) := by

  simp only [commForm, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [nsDiffH_embedCore, nsDiffN_embedCore, canH_coe_velH, velUnitary.inner_map_map,
    velUnitary.inner_map_map]
