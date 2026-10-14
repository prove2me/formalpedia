-- Prove2me | solution 1 for BookProof.NavierStokesFlow.NSHashimoto.velCore_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T15:06:11.757475+00:00
-- url     : https://prove2.me/submissions/20706d0e-1a01-418d-b7c1-fc469c0feef0

-- Generated from ChapterNavierStokesHashimoto.lean — solution of BookProof.NavierStokesFlow.NSHashimoto.velCore_esa
import Mathlib
import Definitions.Def_ChapterNavierStokesHashimoto
import Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velH_essentiallySelfAdjointOn_core
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
theorem solution : EssentiallySelfAdjointOn (lpFiniteModes Vel) (velCore A c) := velH_essentiallySelfAdjointOn_core A c
