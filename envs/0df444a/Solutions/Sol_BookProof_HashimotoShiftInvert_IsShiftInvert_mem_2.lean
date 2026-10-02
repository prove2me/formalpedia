-- Prove2me | solution 2 for BookProof.HashimotoShiftInvert.IsShiftInvert.mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-02T01:38:23.777476+00:00
-- url     : https://prove2.me/submissions/01aa166b-b531-4be0-a394-dd8be25ce4bb

-- Generated from ChapterHashimotoShiftInvert.lean — solution of BookProof.HashimotoShiftInvert.IsShiftInvert.mem
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
open BookProof.HashimotoShiftInvert




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (u : F) : R u ∈ Dom := (h.2 u).choose
