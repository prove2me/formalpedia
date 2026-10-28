-- Prove2me | solution 2 for BookProof.QuantumGravity3DGauge.qg3DElliptic_friedrichs_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:13:02.28274+00:00
-- url     : https://prove2.me/submissions/683b243b-2d90-42db-b4db-f5c7d435221f

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterHermiteProductCore
import Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsOp_isPositiveSelfAdjointExtension
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qg3DElliptic_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qgMom_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_torsionOps_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_signedOp_quadForm_nonneg
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qgKappaElliptic_nonneg
-- Generated from ChapterQuantumGravity3DGauge.lean — theorem solution
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section
theorem solution :
    ∃ (Dom : Submodule ℂ (L2d 84)) (A : Dom →ₗ[ℂ] L2d 84),
      IsPositiveSelfAdjointExtension (qg3DEllipticHamiltonian (coreRepPoly 84)) A := by
  let P : BookProof.FriedrichsExtension.PosSymOp (L2d 84) :=
    { dom := BookProof.HermiteProductCore.polyGaussCore (d := 84)
      op := qg3DEllipticHamiltonian (coreRepPoly 84)
      sym := qg3DElliptic_symmetricOn (coreRepPoly 84)
      pos := fun x => signedOp_quadForm_nonneg (fun i => qgKappaElliptic_nonneg i)
        (fun j => qgMom_symmetricOn (coreRepPoly 84) j)
        (fun m => torsionOps_symmetricOn (coreRepPoly 84) m) x }
  exact ⟨_, _, BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension P
    BookProof.HermiteProductCore.polyGaussCore_dense⟩
