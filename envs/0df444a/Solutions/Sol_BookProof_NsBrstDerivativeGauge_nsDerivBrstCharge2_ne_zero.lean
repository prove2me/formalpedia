-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T03:46:36.644181+00:00
-- url     : https://prove2.me/submissions/f8850ff1-bff7-4d8c-80f4-cd5c8f8d8831

import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Definitions.Def_ChapterNavierStokesGaugeY2
import Theorems.Thm_BookProof_NsBrstDerivativeGauge_glin_bos_apply_tmul

open MvPolynomial BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2 BookProof.NsBrstDerivativeGauge BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge in
theorem solution : nsDerivBrstCharge2 ≠ 0 := by
  intro h
  let L : NSGraded →ₗ[ℂ] ℂ := (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
    TensorProduct.map (MvPolynomial.aeval (R := ℂ) (S₁ := ℂ) (σ := NSVar) (fun _ => 0)).toLinearMap
      ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0) ∘ₗ ExteriorAlgebra.ιInv)
  have h1 := congrArg (fun T => L (T (X (NSVar.y 0) ⊗ₜ[ℂ] (1 : nsGhostSpace)))) h
  simp only [LinearMap.zero_apply, map_zero] at h1
  have h2 : nsDerivBrstCharge2 = glin (fun j => nsBos (genY2 j)) nsChi := rfl
  rw [h2, glin_bos_apply_tmul] at h1
  simp [L, nsGhostCre, genY2, pderiv_X, Pi.single_apply, Fin.sum_univ_three, ExteriorAlgebra.ι_leftInverse _] at h1
