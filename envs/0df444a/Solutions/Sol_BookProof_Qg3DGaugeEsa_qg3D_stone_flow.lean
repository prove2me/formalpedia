-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.qg3D_stone_flow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:39:28.04186+00:00
-- url     : https://prove2.me/submissions/4a3a646e-c615-4576-8524-a93172561200
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQg3DGaugeEsa.lean — solution of BookProof.Qg3DGaugeEsa.qg3D_stone_flow
import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa
import Theorems.Thm_BookProof_Qg3DGaugeEsa_qg3D_essentiallySelfAdjointOn_core
import Theorems.Thm_BookProof_QuantumGravity3DGauge_signedOp_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qgMom_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_torsionOps_symmetricOn
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
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
    ∃ (T : UnboundedSelfAdjoint (L2d 84)) (U : ℝ → (L2d 84 →L[ℂ] L2d 84)),
      IsSelfAdjointExtension (qg3DHamiltonian (coreRepPoly 84)) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ polyGaussCore_dense
    (signedOp_symmetricOn (qgMom_symmetricOn (coreRepPoly 84))
      (torsionOps_symmetricOn (coreRepPoly 84)))
    qg3D_essentiallySelfAdjointOn_core
