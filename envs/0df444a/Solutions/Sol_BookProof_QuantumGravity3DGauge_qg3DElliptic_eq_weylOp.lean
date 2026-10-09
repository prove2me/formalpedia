-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qg3DElliptic_eq_weylOp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T09:47:56.410709+00:00
-- url     : https://prove2.me/submissions/e349a85d-f84b-408e-8b8f-233bd6c38cb3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQuantumGravity3DGauge.lean — solution of BookProof.QuantumGravity3DGauge.qg3DElliptic_eq_weylOp
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Theorems.Thm_BookProof_QuantumGravity3DGauge_signedOp_eq_weylOp
import Theorems.Thm_BookProof_QuantumGravity3DGauge_signedOp_quadForm_nonneg
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qgKappaElliptic_nonneg
import Theorems.Thm_BookProof_QuantumGravity3DGauge_smul_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qgMom_symmetricOn
open BookProof.QuantumGravity3DGauge




open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {d : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {D : Submodule ℂ (L2d 84)}

set_option maxHeartbeats 1000000 in
theorem solution (Φ : CoreRep 84 D) (j : Fin 84) :
    SymmetricOn D (D.subtype.comp
      (((Real.sqrt (qgKappaElliptic j) : ℝ) : ℂ) • qgMom Φ j)) :=
  smul_symmetricOn _ (qgMom_symmetricOn Φ j)
