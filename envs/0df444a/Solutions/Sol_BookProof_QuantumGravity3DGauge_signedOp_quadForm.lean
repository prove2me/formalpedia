-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.signedOp_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T14:07:54.242617+00:00
-- url     : https://prove2.me/submissions/6d276f44-a023-4510-8d75-ae8e8e063db4

-- Generated from ChapterQuantumGravity3DGauge.lean — solution of BookProof.QuantumGravity3DGauge.signedOp_quadForm
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Theorems.Thm_BookProof_QuantumGravity3DGauge_signedOp_apply
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
    {Bf : Fin m → D →ₗ[ℂ] D} (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a))) (x : D) :
    quadForm (signedOp kappa pi Bf) x
      = 1 / 2 * (∑ i, kappa i * ‖((pi i x : D) : F)‖ ^ 2)
        + 1 / 2 * ∑ a, ‖((Bf a x : D) : F)‖ ^ 2 := by

  have hinner : (inner ℂ ((x : D) : F) (signedOp kappa pi Bf x) : ℂ)
      = (((1 / 2 * (∑ i, kappa i * ‖((pi i x : D) : F)‖ ^ 2)
          + 1 / 2 * ∑ a, ‖((Bf a x : D) : F)‖ ^ 2 : ℝ)) : ℂ) := by
    have hpi' : ∀ i : Fin n,
        (inner ℂ ((x : D) : F) (((kappa i : ℝ) : ℂ) • ((pi i (pi i x) : D) : F)) : ℂ)
          = ((kappa i * ‖((pi i x : D) : F)‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [inner_smul_right, inner_sq_eq_normSq (hpi i) x]
      push_cast
      ring
    rw [signedOp_apply, inner_smul_right, inner_add_right, inner_sum, inner_sum,
      Finset.sum_congr rfl fun i _ => hpi' i,
      Finset.sum_congr rfl fun a _ => inner_sq_eq_normSq (hB a) x]
    push_cast
    ring
  rw [quadForm, hinner, Complex.ofReal_re]
