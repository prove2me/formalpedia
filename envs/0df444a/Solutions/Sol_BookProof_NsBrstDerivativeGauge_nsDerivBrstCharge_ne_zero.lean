-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:32:28.522875+00:00
-- url     : https://prove2.me/submissions/5d2762cb-8e6f-4999-bb4c-a0b0cce71cab

-- Generated from ChapterNsBrstDerivativeGauge.lean — solution of BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_ne_zero
import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Theorems.Thm_BookProof_NsBrstDerivativeGauge_nsDerivBrstCharge_apply_tmul
import Theorems.Thm_BookProof_NsBrstDerivativeGauge_ghostComponent_tmul
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NsBrstDerivativeGauge




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge
open BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2
open BookProof.NavierStokesGaugeY

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : nsDerivBrstCharge ≠ 0 := by

  intro h
  have happ : nsDerivBrstCharge (X (NSVar.y 0) ⊗ₜ[ℂ] (1 : nsGhostSpace)) = 0 := by
    rw [h]; simp
  rw [nsDerivBrstCharge_apply_tmul] at happ
  have hterm : ∀ j : Fin 3, j ≠ 0 →
      genY j (X (NSVar.y 0)) ⊗ₜ[ℂ] nsGhostCre j (1 : nsGhostSpace) = 0 := by
    intro j hj
    have hzero : genY j (X (NSVar.y 0)) = 0 := by
      simp [genY_apply, pderiv_X, Ne.symm hj]
    rw [hzero, TensorProduct.zero_tmul]
  rw [Finset.sum_eq_single (0 : Fin 3) (fun j _ hj => hterm j hj) (by simp)] at happ
  have h0 : genY (0 : Fin 3) (X (NSVar.y 0)) = 1 := by
    simp [genY_apply, pderiv_X]
  rw [h0] at happ
  have hgh := congrArg ghostComponent happ
  rw [ghostComponent_tmul] at hgh
  simp [nsGhostCre] at hgh
