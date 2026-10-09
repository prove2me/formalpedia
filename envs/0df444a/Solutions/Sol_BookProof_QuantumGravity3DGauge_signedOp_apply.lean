-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.signedOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T09:44:06.373738+00:00
-- url     : https://prove2.me/submissions/80408c77-aaa4-4a4e-accb-46edfd32c039

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge
open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem solution {n m : ℕ} (kappa : Fin n → ℝ) (pi : Fin n → D →ₗ[ℂ] D)
    (Bf : Fin m → D →ₗ[ℂ] D) (x : D) :
    signedOp kappa pi Bf x
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ i, ((kappa i : ℝ) : ℂ) • ((pi i (pi i x) : D) : F))
            + ∑ a, ((Bf a (Bf a x) : D) : F)) := by
  simp [signedOp, signedOpDom, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.add_apply, Submodule.subtype_apply,
    Submodule.coe_smul, Submodule.coe_sum, Submodule.coe_add]
