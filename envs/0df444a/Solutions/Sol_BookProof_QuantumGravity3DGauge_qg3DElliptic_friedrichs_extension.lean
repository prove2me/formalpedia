-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qg3DElliptic_friedrichs_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T09:47:58.280033+00:00
-- url     : https://prove2.me/submissions/02107d35-8890-4698-88af-5045fe281c28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQuantumGravity3DGauge.lean — solution of BookProof.QuantumGravity3DGauge.qg3DElliptic_friedrichs_extension
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qg3DElliptic_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_signedOp_quadForm_nonneg
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qgKappaElliptic_nonneg
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qgMom_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_torsionOps_symmetricOn
import Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_extension_exists
open BookProof.QuantumGravity3DGauge




open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution :
    ∃ (Dom : Submodule ℂ (L2d 84)) (A : Dom →ₗ[ℂ] L2d 84),
      IsPositiveSelfAdjointExtension (qg3DEllipticHamiltonian (coreRepPoly 84)) A :=
  friedrichs_extension_exists
      ⟨polyGaussCore, qg3DEllipticHamiltonian (coreRepPoly 84),
        qg3DElliptic_symmetricOn _,
        fun x => signedOp_quadForm_nonneg qgKappaElliptic_nonneg (qgMom_symmetricOn _)
          (torsionOps_symmetricOn _) x⟩
      polyGaussCore_dense
