-- Prove2me | solution 1 for BookProof.NavierStokesFlow.NSHashimoto.velCore_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T20:29:36.950996+00:00
-- url     : https://prove2.me/submissions/ce83ef00-450e-432a-b737-4783818bc543

-- Generated from ChapterNavierStokesHashimoto.lean — solution of BookProof.NavierStokesFlow.NSHashimoto.velCore_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesHashimoto
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterLeafGaps
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.NSHashimoto



open Filter Topology



open BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.EsaClosure
open BookProof.HermiteGalerkin
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution : SymmetricOn (lpFiniteModes Vel) (velCore A c) :=
  fun x y =>
    velH_symmetricOn A c (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x)
      (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) y)
