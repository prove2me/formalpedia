-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.signedOp_quadForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T13:16:55.37766+00:00
-- url     : https://prove2.me/submissions/a7090a3b-1ac3-4cc5-869f-dd93ccab8bbe

-- Generated from ChapterQuantumGravity3DGauge.lean — solution of BookProof.QuantumGravity3DGauge.signedOp_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Theorems.Thm_BookProof_QuantumGravity3DGauge_signedOp_quadForm
open BookProof.QuantumGravity3DGauge




open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {d : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {n m : ℕ} {kappa : Fin n → ℝ} {pi : Fin n → D →ₗ[ℂ] D}
    {Bf : Fin m → D →ₗ[ℂ] D} (hk : ∀ i, 0 ≤ kappa i)
    (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a))) (x : D) :
    0 ≤ quadForm (signedOp kappa pi Bf) x := by
  rw [signedOp_quadForm hpi hB x]
  have h1 : 0 ≤ ∑ i, kappa i * ‖((pi i x : D) : F)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hk i) (by positivity)
  have h2 : 0 ≤ ∑ a, ‖((Bf a x : D) : F)‖ ^ 2 := Finset.sum_nonneg fun a _ => by positivity
  linarith
