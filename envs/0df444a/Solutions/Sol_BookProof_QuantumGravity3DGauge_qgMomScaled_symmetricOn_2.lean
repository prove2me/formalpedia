-- Prove2me | solution 2 for BookProof.QuantumGravity3DGauge.qgMomScaled_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:13:03.474281+00:00
-- url     : https://prove2.me/submissions/b0086846-5f17-4180-86a2-395a168d069a

import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterHermiteProductCore
import Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsOp_isPositiveSelfAdjointExtension
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qg3DElliptic_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qgMom_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_torsionOps_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_signedOp_quadForm_nonneg
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qgKappaElliptic_nonneg
-- Generated from ChapterQuantumGravity3DGauge.lean — theorem solution
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

variable {d : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {D : Submodule ℂ (L2d 84)}



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
