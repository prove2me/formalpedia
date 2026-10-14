-- Prove2me | solution 1 for BookProof.NavierStokesFlow.NSHashimoto.velCore_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T15:06:13.103885+00:00
-- url     : https://prove2.me/submissions/bbbba995-e221-4229-b3b4-5f357a0906c5

-- Generated from ChapterNavierStokesHashimoto.lean — solution of BookProof.NavierStokesFlow.NSHashimoto.velCore_dense
import Mathlib
import Definitions.Def_ChapterNavierStokesHashimoto
import Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velH_domain_dense
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
theorem solution : Dense ((lpFiniteModes Vel : Submodule ℂ (L2I Vel)) : Set (L2I Vel)) := velH_domain_dense
