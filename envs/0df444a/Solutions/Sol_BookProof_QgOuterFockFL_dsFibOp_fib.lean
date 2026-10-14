-- Prove2me | solution 1 for BookProof.QgOuterFockFL.dsFibOp_fib
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-13T06:23:24.10801+00:00
-- url     : https://prove2.me/submissions/ac8c1727-7b7a-4ae0-aed4-7416caae1678

-- Generated from ChapterQgOuterFockFarisLavine.lean — solution of BookProof.QgOuterFockFL.dsFibOp_fib
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
open BookProof.QgOuterFockFL



open scoped ENNReal


open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.HashimotoShiftInvert
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable (C : ∀ i, Comparison (G i))
variable (H : ∀ i, (C i).dom →ₗ[ℂ] G i)
variable {C H}

set_option maxHeartbeats 1000000 in
theorem solution {K : ℝ}
    (hrel : ∀ (i : ι) (u : (C i).dom), ‖H i u‖ ≤ K * ‖(C i).op u + (u : G i)‖)
    (x : dsDom C) (i : ι) :
    ((dsFibOp C H K hrel x : lp G 2) : ∀ i, G i) i = H i (fib C x i) := opTot_of_mem _ (x.2.1 i)
