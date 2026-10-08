-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.qg3DElliptic_essentiallySelfAdjointOn_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T23:47:11.525784+00:00
-- url     : https://prove2.me/submissions/e9129b75-9201-4839-81ba-a843945fdb0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQg3DGaugeEsa.lean — solution of BookProof.Qg3DGaugeEsa.qg3DElliptic_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa
import Theorems.Thm_BookProof_Qg3DGaugeEsa_qgSigned_essentiallySelfAdjointOn_core
open BookProof.Qg3DGaugeEsa




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution :
    EssentiallySelfAdjointOn (polyGaussCore (d := 84))
      (qg3DEllipticHamiltonian (coreRepPoly 84)) := qgSigned_essentiallySelfAdjointOn_core qgKappaElliptic
